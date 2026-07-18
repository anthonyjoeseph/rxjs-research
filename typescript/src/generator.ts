import { Closed, Exp, Fn, PrimOp, Tm, Ty, Val } from "./exp.js";
import type { ObservableInput, Slot, TestCase, Timed } from "./prop-test.js";

// The differential-testing generator: deterministic, seeded canonical
// programs. Every tree is well-typed BY CONSTRUCTION (each node built at
// a known type), μ-guarded (a varE names only a USABLE μ-var, and those
// enter scope only past a deferᵉ), and closed at the root (no free Θ- or
// μ-vars). The generator is the authority on the program corpus; the
// Agda side only decodes and evaluates what it emits. There is no Agda
// twin — Agda has its own QuickCheck — so this is free implementation.

// ---- seeded PRNG (mulberry32 over an FNV-1a string hash) ----
type Rng = () => number; // [0, 1)

const hashSeed = (s: string): number => {
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return h >>> 0;
};

const mulberry32 = (seed: number): Rng => {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
};

const int = (rng: Rng, lo: number, hi: number): number =>
  lo + Math.floor(rng() * (hi - lo + 1)); // inclusive
const pick = <T>(rng: Rng, xs: T[]): T => xs[Math.floor(rng() * xs.length)];
const chance = (rng: Rng, p: number): boolean => rng() < p;

// ---- types ----
const unitT: Ty = { type: "unit" };
const boolT: Ty = { type: "bool" };
const natT: Ty = { type: "nat" };
const prodNN: Ty = { type: "prod", fst: natT, snd: natT };

const tyEq = (a: Ty, b: Ty): boolean => {
  if (a.type === "prod" && b.type === "prod")
    return tyEq(a.fst, b.fst) && tyEq(a.snd, b.snd);
  if (a.type === "sum" && b.type === "sum")
    return tyEq(a.left, b.left) && tyEq(a.right, b.right);
  if (a.type === "obs" && b.type === "obs") return tyEq(a.elem, b.elem);
  return (
    a.type === b.type &&
    a.type !== "prod" &&
    a.type !== "sum" &&
    a.type !== "obs"
  );
};

// value types only (no obs): scripted-slot element types and the types a
// term inhabits. obs types arise only as the SOURCE of an *All join
const genValTy = (rng: Rng, depth: number): Ty => {
  if (depth <= 0) return pick(rng, [natT, boolT]);
  const r = rng();
  if (r < 0.55) return natT; // bias nat — the value domain's workhorse
  if (r < 0.7) return boolT;
  if (r < 0.78) return unitT;
  if (r < 0.9)
    return {
      type: "prod",
      fst: genValTy(rng, depth - 1),
      snd: genValTy(rng, depth - 1),
    };
  return {
    type: "sum",
    left: genValTy(rng, depth - 1),
    right: genValTy(rng, depth - 1),
  };
};

// ---- generation context: Γ inputs, Δᵍ guarded / Δ usable μ-vars, Θ ----
type GenCtx = {
  gamma: Ty[]; // slot types (input i : gamma[i])
  guarded: Ty[]; // μ-vars bound but not yet past a defer (unreferenceable)
  usable: Ty[]; // μ-vars in scope (varE may name these)
  theta: Ty[]; // value-var types (varT index 0 = innermost)
};

// ---- terms ----
// a guaranteed-terminating literal of the type (obs → a strmT wrapping a
// shallow observable)
const litTm = (rng: Rng, ty: Ty, ctx: GenCtx, depth: number): Tm => {
  switch (ty.type) {
    case "unit":
      return { type: "unitT", ty };
    case "bool":
      return { type: "boolT", ty, val: chance(rng, 0.5) };
    case "nat":
      return { type: "natT", ty, val: int(rng, 0, 9) };
    case "prod":
      return {
        type: "pairT",
        ty,
        fst: litTm(rng, ty.fst, ctx, depth),
        snd: litTm(rng, ty.snd, ctx, depth),
      };
    case "sum":
      return chance(rng, 0.5)
        ? { type: "inlT", ty, val: litTm(rng, ty.left, ctx, depth) }
        : { type: "inrT", ty, val: litTm(rng, ty.right, ctx, depth) };
    case "obs":
      return {
        type: "strmT",
        ty,
        exp: genExp(rng, ty.elem, ctx, Math.max(0, depth - 1)),
      };
  }
};

const genTm = (rng: Rng, ty: Ty, ctx: GenCtx, depth: number): Tm => {
  const vars = ctx.theta
    .map((vt, i) => ({ vt, i }))
    .filter((x) => tyEq(x.vt, ty));
  const varTm = (): Tm => ({ type: "varT", ty, index: pick(rng, vars).i });

  if (depth <= 0 || chance(rng, 0.35))
    return vars.length > 0 && chance(rng, 0.6)
      ? varTm()
      : litTm(rng, ty, ctx, depth);

  const opts: (() => Tm)[] = [() => litTm(rng, ty, ctx, depth)];
  if (vars.length > 0) opts.push(varTm);
  opts.push(() => ({
    type: "ifT",
    ty,
    cond: genTm(rng, boolT, ctx, depth - 1),
    then: genTm(rng, ty, ctx, depth - 1),
    else: genTm(rng, ty, ctx, depth - 1),
  }));
  const natPair = (): Tm => ({
    type: "pairT",
    ty: prodNN,
    fst: genTm(rng, natT, ctx, depth - 1),
    snd: genTm(rng, natT, ctx, depth - 1),
  });
  if (tyEq(ty, natT))
    opts.push(() => ({
      type: "primT",
      ty,
      op: pick(rng, ["add", "sub", "mul"] as PrimOp[]),
      arg: natPair(),
    }));
  if (tyEq(ty, boolT)) {
    opts.push(() => ({
      type: "primT",
      ty,
      op: pick(rng, ["eq", "lt"] as PrimOp[]),
      arg: natPair(),
    }));
    opts.push(() => ({
      type: "primT",
      ty,
      op: "not",
      arg: genTm(rng, boolT, ctx, depth - 1),
    }));
  }
  if (ty.type === "prod")
    opts.push(() => ({
      type: "pairT",
      ty,
      fst: genTm(rng, ty.fst, ctx, depth - 1),
      snd: genTm(rng, ty.snd, ctx, depth - 1),
    }));
  if (ty.type === "sum")
    opts.push(() =>
      chance(rng, 0.5)
        ? { type: "inlT", ty, val: genTm(rng, ty.left, ctx, depth - 1) }
        : { type: "inrT", ty, val: genTm(rng, ty.right, ctx, depth - 1) },
    );
  if (ty.type === "obs")
    opts.push(() => ({
      type: "strmT",
      ty,
      exp: genExp(rng, ty.elem, ctx, depth - 1),
    }));
  return pick(rng, opts)();
};

// a Fn binds its argument as Θ-var 0
const genFn = (
  rng: Rng,
  argTy: Ty,
  retTy: Ty,
  ctx: GenCtx,
  depth: number,
): Fn => genTm(rng, retTy, { ...ctx, theta: [argTy, ...ctx.theta] }, depth);

// ---- expressions ----
const genExp = (
  rng: Rng,
  ty: Ty,
  ctx: GenCtx,
  depth: number,
  force?: string,
): Exp => {
  const leaves: (() => Exp)[] = [
    () => ({
      type: "of",
      ty,
      items: Array.from({ length: int(rng, 0, 3) }, () =>
        genTm(rng, ty, ctx, Math.min(depth, 2)),
      ),
    }),
    () => ({ type: "empty", ty }),
  ];
  for (const { i } of ctx.gamma
    .map((gt, i) => ({ gt, i }))
    .filter((x) => tyEq(x.gt, ty)))
    leaves.push(() => ({ type: "input", ty, index: i }));
  for (const { i } of ctx.usable
    .map((ut, i) => ({ ut, i }))
    .filter((x) => tyEq(x.ut, ty)))
    leaves.push(() => ({ type: "varE", ty, index: i }));

  const obsOf: Ty = { type: "obs", elem: ty };
  const operators: Record<string, () => Exp> = {
    map: () => {
      const s = genValTy(rng, 2);
      return {
        type: "map",
        ty,
        fn: genFn(rng, s, ty, ctx, depth - 1),
        src: genExp(rng, s, ctx, depth - 1),
      };
    },
    take: () => ({
      type: "take",
      ty,
      count: genTm(rng, natT, ctx, Math.min(depth, 2)),
      src: genExp(rng, ty, ctx, depth - 1),
    }),
    scan: () => {
      const s = genValTy(rng, 2);
      return {
        type: "scan",
        ty,
        fn: genFn(rng, { type: "prod", fst: ty, snd: s }, ty, ctx, depth - 1),
        init: genTm(rng, ty, ctx, Math.min(depth, 2)),
        src: genExp(rng, s, ctx, depth - 1),
      };
    },
    mergeAll: () => ({
      type: "mergeAll",
      ty,
      src: genExp(rng, obsOf, ctx, depth - 1),
    }),
    concatAll: () => ({
      type: "concatAll",
      ty,
      src: genExp(rng, obsOf, ctx, depth - 1),
    }),
    switchAll: () => ({
      type: "switchAll",
      ty,
      src: genExp(rng, obsOf, ctx, depth - 1),
    }),
    exhaustAll: () => ({
      type: "exhaustAll",
      ty,
      src: genExp(rng, obsOf, ctx, depth - 1),
    }),
    // μ binds a guarded var; defer moves the guarded vars into scope
    mu: () => ({
      type: "mu",
      ty,
      body: genExp(
        rng,
        ty,
        { ...ctx, guarded: [ty, ...ctx.guarded] },
        depth - 1,
      ),
    }),
    defer: () => ({
      type: "defer",
      ty,
      body: genExp(
        rng,
        ty,
        { ...ctx, guarded: [], usable: [...ctx.guarded, ...ctx.usable] },
        depth - 1,
      ),
    }),
  };

  // of/empty are leaves; force them there, real operators from `operators`
  const forced =
    force === "of"
      ? leaves[0]
      : force === "empty"
        ? leaves[1]
        : operators[force ?? ""];
  if (forced) return forced();
  if (depth <= 0) return pick(rng, leaves)();
  if (chance(rng, 0.25)) return pick(rng, leaves)();
  // once a μ is open, bias toward a defer so recursion actually closes
  if (ctx.guarded.length > 0 && chance(rng, 0.5)) return operators.defer();
  return pick(rng, Object.values(operators))();
};

// ---- scripted inputs ----
const genVal = (rng: Rng, ty: Ty, depth: number): Val => {
  switch (ty.type) {
    case "unit":
      return null;
    case "bool":
      return chance(rng, 0.5);
    case "nat":
      return int(rng, 0, 9);
    case "prod":
      return [genVal(rng, ty.fst, depth), genVal(rng, ty.snd, depth)];
    case "sum":
      return chance(rng, 0.5)
        ? { type: "inl", val: genVal(rng, ty.left, depth) }
        : { type: "inr", val: genVal(rng, ty.right, depth) };
    case "obs":
      return { type: "empty", ty: ty.elem }; // unreachable: slots are value-typed
  }
};

const genScripted = (rng: Rng, ty: Ty): ObservableInput<Val> => {
  const timed = (n: number): Timed<Val>[] =>
    Array.from({ length: n }, () => ({
      wait: int(rng, 0, 2),
      val: genVal(rng, ty, 2),
    }));
  return chance(rng, 0.5)
    ? { type: "hot", async: timed(int(rng, 0, 3)) }
    : {
        type: "cold",
        sync: Array.from({ length: int(rng, 0, 3) }, () => genVal(rng, ty, 2)),
        async: timed(int(rng, 0, 2)),
      };
};

// the slot telescope: slot i's shared def sees only the prefix (0..i-1),
// exactly a JS `const` telescope
const genSlots = (rng: Rng, depth: number): { types: Ty[]; slots: Slot[] } => {
  const n = int(rng, 0, 3);
  const types: Ty[] = [];
  const slots: Slot[] = [];
  for (let i = 0; i < n; i++) {
    const ty = genValTy(rng, 2);
    const prefix = [...types]; // slots strictly before i
    types.push(ty);
    slots.push(
      chance(rng, 0.7)
        ? { type: "scripted", input: genScripted(rng, ty) }
        : {
            type: "shared",
            def: genExp(
              rng,
              ty,
              { gamma: prefix, guarded: [], usable: [], theta: [] },
              Math.min(depth, 3),
            ) as Closed,
          },
    );
  }
  return { types, slots };
};

const genTestCase = (rng: Rng, operator?: string): TestCase => {
  const rootTy = genValTy(rng, 2);
  const { types, slots } = genSlots(rng, 3);
  const exp = genExp(
    rng,
    rootTy,
    { gamma: types, guarded: [], usable: [], theta: [] },
    4,
    operator,
  );
  return { ctx: types, exp, slots, fuel: int(rng, 0, 10) };
};

const CASES_PER_SEED = 20;

// deterministic per seed: one PRNG stream, drawn sequentially per case
export const genTestCases = (seed: string, operator?: string): TestCase[] => {
  const rng = mulberry32(hashSeed(seed));
  return Array.from({ length: CASES_PER_SEED }, () =>
    genTestCase(rng, operator),
  );
};

export const genSeeds = (): string[] =>
  Array.from({ length: 25 }, (_, i) => `s${i}`);
