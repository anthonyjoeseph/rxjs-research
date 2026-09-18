import { Closed, Exp, Fn, PrimOp, Tm, Ty, Val } from "./exp.js";
import type { ObservableInput, Slot, TestCase, Timed } from "./prop-test.js";

// The differential-testing generator: deterministic, seeded canonical
// programs. Every tree is well-typed BY CONSTRUCTION (each node built at
// a known type), μ-guarded (a varE names only a USABLE μ-var, and those
// enter scope only past a deferᵉ), and closed at the root (no free Θ- or
// μ-vars). The generator is the authority on the program corpus; the
// Agda side only decodes and evaluates what it emits. There is no Agda
// twin — Agda has its own QuickCheck — so this is free implementation.
//
// MOST OF WHAT IT DRAWS EMITS NOTHING, AND THE HEADLINE COUNT DOES NOT
// SAY SO.  Measured over the full seed sweep: 357 of 500 programs
// produce an EMPTY value list, so a reported 500/500 is 143 rows that
// could have diverged and 357 that agree because neither side emitted.
// An empty row is not a wrong row — a program rooted at `empty`, or one
// whose fuel never reaches its async script, legitimately yields nothing
// — but it is not evidence either, and the ratio is what a coverage
// claim has to be denominated in.  This is the same shape as the
// EMPTY-output incident `prop-test.ts` records, one level up: there the
// check could not fail, here it can, and most of it does not.

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
const uniqT: Ty = { type: "uniq" };
const prodNN: Ty = { type: "prod", fst: natT, snd: natT };
const prodUU: Ty = { type: "prod", fst: uniqT, snd: uniqT };

const tyEq = (a: Ty, b: Ty): boolean => {
  if (a.type === "prod" && b.type === "prod")
    return tyEq(a.fst, b.fst) && tyEq(a.snd, b.snd);
  if (a.type === "sum" && b.type === "sum")
    return tyEq(a.left, b.left) && tyEq(a.right, b.right);
  if (a.type === "obs" && b.type === "obs") return tyEq(a.elem, b.elem);
  if (a.type === "list" && b.type === "list") return tyEq(a.elem, b.elem);
  return (
    a.type === b.type &&
    a.type !== "prod" &&
    a.type !== "sum" &&
    a.type !== "obs" &&
    a.type !== "list"
  );
};

// value types only (no obs): scripted-slot element types and the types a
// term inhabits. obs types arise only as the SOURCE of an *All join
const genValTy = (rng: Rng, depth: number): Ty => {
  if (depth <= 0) return pick(rng, [natT, boolT]);
  const r = rng();
  if (r < 0.55) return natT; // bias nat — the value domain's workhorse
  if (r < 0.7) return boolT;
  if (r < 0.75) return unitT;
  // NO uniq LANE, AND IT IS THE HARNESS SAYING SO RATHER THAN THE
  // LANGUAGE.  A type generated here is one a STREAM will carry -- a
  // scripted slot's element, an `of` item -- and a token in a value
  // position is one the differential comparison cannot handle: it
  // renames instants and sources, renames a token in neither, and
  // `canonical` walks values without their TYPE, so it cannot tell a
  // token from a nat to rename it. `mint(t => of(t))` is well-typed in
  // both trees; it is unCOMPARABLE, which is a different finding and
  // the one `noToken` in the harness states. uniq is exercised at term
  // level instead, where `uniq̂` and a mint binder both reach it.
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
  sharedSlots: boolean[]; // slot i is an all-resets-false share
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
    case "uniq":
      // the reserved token, and the only one a term can name: every
      // other token comes from a `mint` binder and is read out of Θ
      return { type: "uniqT", ty };
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
    // no generated type is a list — the lists in a tree are the ones the
    // pure-function former's own encoding builds — but the empty one is
    // the literal at that type, so the clause is real rather than a stub
    case "list":
      return { type: "nilT", ty };
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

  const opts: (() => Tm)[] = [];
  opts.push(() => litTm(rng, ty, ctx, depth));
  if (vars.length > 0) opts.push(varTm);
  // PROJECTING A PAIR VARIABLE IS THE ONLY WAY INTO A BOUND PAIR, and
  // it is what puts a list in scope at all: the pure-function former
  // hands its step ONE argument, the pair of carried state and the
  // emit's values, so without this the list half is unreachable and
  // every generated step ignores its input.
  for (const { vt, i } of ctx.theta.map((vt, i) => ({ vt, i })))
    if (vt.type === "prod") {
      const pair: Tm = { type: "varT", ty: vt, index: i };
      if (tyEq(vt.fst, ty)) opts.push(() => ({ type: "fstT", ty, pair }));
      if (tyEq(vt.snd, ty)) opts.push(() => ({ type: "sndT", ty, pair }));
    }
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
    // BOTH SIDES ARE GENERATED FREELY, because a token can now be
    // WRITTEN as well as bound: `uniq̂` names the reserved one and a
    // `mint` ancestor puts minted ones in Θ. So this lane fires
    // wherever a bool is wanted rather than only under a mint, and the
    // interesting rows -- literal against minted, minted against a
    // DIFFERENT minted -- come from the same draw.
    //
    // WHAT IS STILL OUT OF REACH IS A TOKEN AS STREAM DATA, and that is
    // the harness rather than the language: `mint(t => of(t))` is legal
    // in both trees, but the streams are compared up to renaming of
    // instants and sources, a token in a VALUE position is renamed by
    // neither, and `canonical` walks values without their TYPE, so it
    // cannot tell a token from a nat to rename it. `genValTy` keeps
    // uniq out of every element type for exactly that reason.
    opts.push(() => ({
      type: "primT",
      ty,
      op: "eqU" as PrimOp,
      arg: {
        type: "pairT",
        ty: prodUU,
        fst: genTm(rng, uniqT, ctx, depth - 1),
        snd: genTm(rng, uniqT, ctx, depth - 1),
      },
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
  // THE ONLY ELIMINATOR A SUM HAS, and the one former either tree carried
  // that nothing had ever generated: it decodes, it compiles, and it sits
  // in both unions, so every run of the oracle and every all-Agda sweep
  // reported green without once having been handed one. It is not
  // guarded by a type test, because a case ELIMINATES at whatever type
  // the surrounding term wants; what its own type pins is the scrutinee.
  // That scrutinee's `ty` is built here rather than drawn from scope,
  // since the decoder reads the branch contexts off it and a sum-typed
  // variable is rare enough in a generated Θ that the lane would almost
  // never fire.
  opts.push(() => {
    const scrutTy: Ty = { type: "sum", left: natT, right: boolT };
    return {
      type: "caseT",
      ty,
      scrut: genTm(rng, scrutTy, ctx, depth - 1),
      onInl: genTm(rng, ty, { ...ctx, theta: [natT, ...ctx.theta] }, depth - 1),
      onInr: genTm(
        rng,
        ty,
        { ...ctx, theta: [boolT, ...ctx.theta] },
        depth - 1,
      ),
    };
  });
  if (ty.type === "obs")
    opts.push(() => ({
      type: "strmT",
      ty,
      exp: genExp(rng, ty.elem, ctx, depth - 1),
    }));
  // A LIST-TYPED TERM IS WHERE THE VALUE LANGUAGE GETS ITS OWN REACH.
  // Consing and folding with a conditional are how a term builds a list
  // of a length it was not handed, which is what a pointwise step can
  // never do — so this clause is what the fan lane below spends when it
  // hands `mergeAll` a step that returns literal syntax.
  if (ty.type === "list") {
    const elem = ty.elem;
    opts.push(() => ({
      type: "consT",
      ty,
      head: genTm(rng, elem, ctx, depth - 1),
      tail: genTm(rng, ty, ctx, depth - 1),
    }));
    // the list folded over is drawn from the types REACHABLE in scope
    // rather than from the variables themselves: a list is never bound
    // directly here — it arrives as the second half of the former's
    // argument pair — so a fold restricted to list-typed variables could
    // never fire at all, its only source being another fold's own
    // accumulator.
    const reachable: Ty[] = [];
    for (const vt of ctx.theta) {
      if (vt.type === "list") reachable.push(vt);
      if (vt.type === "prod") {
        if (vt.fst.type === "list") reachable.push(vt.fst);
        if (vt.snd.type === "list") reachable.push(vt.snd);
      }
    }
    if (reachable.length > 0)
      opts.push(() => {
        const srcTy = pick(rng, reachable) as { type: "list"; elem: Ty };
        return {
          type: "foldT",
          ty,
          list: genTm(rng, srcTy, ctx, depth - 1),
          init: genTm(rng, ty, ctx, depth - 1),
          // the step binds the element then the accumulator
          step: genTm(
            rng,
            ty,
            { ...ctx, theta: [srcTy.elem, ty, ...ctx.theta] },
            depth - 1,
          ),
        };
      });
  }
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
    // A SHARED SLOT'S LEAF IS WEIGHTED, because a share with ONE
    // subscriber is a degenerate share: the fan-out, the mid-flight
    // join and the latched one-shot are all reachable only when the
    // same slot is named twice, and an unweighted draw reached that
    // in two cases out of five hundred. The weight is on the SLOT and
    // not on the tree, so what it buys is second references to the
    // one index rather than more inputs generally.
    for (let w = 0; w < (ctx.sharedSlots[i] ? 5 : 3); w++)
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
    // AND THE COUNT-CHANGING LANE, WHICH IS NOW A FLATTEN. A pointwise
    // step emits exactly what it was handed, so dropping a value and
    // duplicating one are shapes neither lane above can reach -- and a
    // generator blind to them is the blind spot this file's history
    // already records. rxjs reaches them with `mergeMap(x => ...)`, so
    // this lane writes exactly that: a step returning literal syntax,
    // spent by `mergeAll`.
    fan: () => {
      const inner: Ty = { type: "obs", elem: ty };
      // the step's OWN context: its argument is Θ-var 0, so everything
      // generated under it counts from there and nothing here may be
      // built in the caller's Θ
      const under: GenCtx = { ...ctx, theta: [ty, ...ctx.theta] };
      const x: Tm = { type: "varT", ty, index: 0 };
      const strm = (exp: Exp): Fn => ({ type: "strmT", ty: inner, exp });
      const step: Fn = pick(rng, [
        () => strm({ type: "empty", ty }),
        () => strm({ type: "of", ty, items: [x] }),
        () => strm({ type: "of", ty, items: [x, x] }),
        () => strm({ type: "of", ty, items: [x, genTm(rng, ty, under, 1)] }),
        // the value-dependent one: which arm is taken is decided by the
        // value itself, per element, so a program cannot be read off the
        // tree the way the four above can
        (): Fn => ({
          type: "ifT",
          ty: inner,
          cond: genTm(rng, boolT, under, Math.min(depth, 2)),
          then: strm({ type: "empty", ty }),
          else: strm({ type: "of", ty, items: [x] }),
        }),
      ])();
      return {
        type: "mergeAll",
        ty,
        limit: undefined,
        src: {
          type: "map",
          ty: inner,
          fn: step,
          src: genExp(rng, ty, ctx, depth - 1),
        },
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
    // the limit axis is where bounded concurrency gets exercised:
    // absent is the old mergeAll, 1 is the old concatAll, 2/3 are the
    // middle that nothing in this development could previously reach.
    // Two lanes with three parked inners is the smallest shape whose
    // drain refills more than one lane in a single instant
    mergeAll: () => ({
      type: "mergeAll",
      ty,
      limit: pick(rng, [undefined, 1, 1, 2, 3] as (number | undefined)[]),
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
    // mint binds one fresh uniq token per subscription, extending Θ by
    // uniqᵗ at index 0; μ-var state (guarded/usable) is unchanged
    mint: () => ({
      type: "mint",
      ty,
      body: genExp(
        rng,
        ty,
        { ...ctx, theta: [uniqT, ...ctx.theta] },
        depth - 1,
      ),
    }),
  };

  // THE GENERATOR PRODUCES THE PLAIN TREE ONLY, so there is no
  // batchSync lane: that former's type IS the instant/batch structure,
  // which plain rxjs has no notion of and the oracle's plain leg
  // therefore cannot mirror. `scripts/formers.tsv` carries the hole with
  // gen=no, which is where a former nothing reaches is counted.

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
    case "uniq":
      // unreachable: `genValTy` yields no uniq, and that is the point —
      // a token is minted at subscription, so nothing OUTSIDE the
      // program can produce one, a scripted input least of all
      throw new Error("no scripted value inhabits uniq — a token is minted");
    case "prod":
      return [genVal(rng, ty.fst, depth), genVal(rng, ty.snd, depth)];
    case "sum":
      return chance(rng, 0.5)
        ? { type: "inl", val: genVal(rng, ty.left, depth) }
        : { type: "inr", val: genVal(rng, ty.right, depth) };
    case "obs":
      // unreachable: slots are value-typed. A value at obs type is a
      // CLOSURE, so the empty environment is part of the shape
      return { exp: { type: "empty", ty: ty.elem }, env: [] };
    case "list":
      return [];
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
    // REUSING AN EARLIER SLOT'S TYPE ON PURPOSE. A slot is reachable
    // only through an `input` leaf at its own type, so types drawn
    // independently make every reference coincidental -- and a slot
    // nothing references is constructed and never subscribed, which is
    // the share telescope being built and not run.
    const ty =
      types.length > 0 && chance(rng, 0.4)
        ? pick(rng, types)
        : genValTy(rng, 2);
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
              {
                gamma: prefix,
                sharedSlots: slots.map((sl) => sl.type === "shared"),
                guarded: [],
                usable: [],
                theta: [],
              },
              Math.min(depth, 3),
            ) as Closed,
          },
    );
  }
  return { types, slots };
};

const genTestCase = (rng: Rng, operator?: string): TestCase => {
  // the slots come FIRST so the root type can be drawn from them: a
  // root type unrelated to every slot leaves the tree no typed leaf to
  // reach one through, which is how most of the corpus came to name no
  // input at all
  const { types, slots } = genSlots(rng, 3);
  const rootTy =
    types.length > 0 && chance(rng, 0.5) ? pick(rng, types) : genValTy(rng, 2);
  const exp = genExp(
    rng,
    rootTy,
    {
      gamma: types,
      sharedSlots: slots.map((sl) => sl.type === "shared"),
      guarded: [],
      usable: [],
      theta: [],
    },
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
