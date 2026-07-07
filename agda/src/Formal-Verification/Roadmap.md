# Roadmap: discharging the seven postulates

This folder contains the one theorem the repository exists to prove, already
a **value**:

```agda
formal-verification :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
```

Everything outside this folder is **fully defined** — the spec, the
implementation, every Naive-Rx operator, `Canonical`, the bridge.

## STATUS (updated as postulates fall)

**Four postulates remain**, down from seven:

- ✅ `counting-factors` — **PROVEN** in `Counting-Factors.agda` (new
  module). The whole mechanical machine-commutation half:
  `mergeMap-oneshot` (mergeMap of one-shot `ofMaybe` inners = concatMap of
  spawn-flushes) ∘ `scan-collect` (scan's running states, flushed, =
  collectB) ∘ `batchSync-bItems` (batchSync+endWith serialize the grouped
  trace into the `bItems` stream). The reification (`bItems`/`flushOf`/
  `collectB`/`countBatches`) moved there too. Three enabling refactors,
  all definitionally identical (refl suite intact): `ofMaybe` no longer
  matches on its `Maybe` (so `State (ofMaybe mo) = Bool` for neutral mo,
  killing a dependent-state block); `mergeMapRx`'s per-step `stepAll`/
  `spawnAll` lifted to top-level `mmStepAll`/`mmSpawnAll`; `scanRx`'s
  burst-fold lifted to top-level `scanBurst`. These lifted helpers are
  reusable for the join cases of `tracks-compile`.
- ✅ `Tracks` — **DEFINED** (was an abstract Set). `spawnFlatten` + the
  ∀-position-j statement; three refl tripwires in `Trace-Faithful.agda`.
- ✅ `tracks-stamped` — **PROVEN**: `tr 0 refl` (spawnFlatten em 0 ≡
  flatten em by computation).
- ⬜ `Accounted`, `counting-groups`, `compile-accounted`
  (`Counting-Recovers.agda`) — the counting half's semantic core (§2.2,
  §2.3 below).
- ⬜ `tracks-compile` (`Trace-Faithful.agda`) — the grammar induction
  (§3.2 below). This is the hardest remaining item.

The plan below is written for whoever picks the rest up. §2.1
(counting-factors) is done — kept for reference.

## 0. Ground rules (ratified, do not renegotiate)

- **Agda is the design authority.** The TypeScript is a transcription; if
  Agda and TS disagree, TS is wrong.
- **A postulate that cannot be proven as stated is a spec bug to rework,
  not work around.** If you get stuck because a statement is false, the
  statement (or a definition upstream) changes — surface it to Anthony.
- **No dangling definitions or postulates.** Everything must be consumed by
  the proof of `formal-verification` (or be a `refl` instance guarding it).
  When you decompose a postulate, the new finer postulates must be consumed
  by a _defined_ value replacing the old one.
- **Delete superseded code outright.** Git history is the archive.
- **refl tripwires after every step.** Both sides compute. After ANY change,
  the instance suite at the bottom of `Main-Theorem.agda` must still pass —
  it is the semantics, pinned. Add new `refl` instances for any behavior you
  rely on. Run negative controls (assert a wrong value, watch it fail) when
  you add a new instance; a `refl` that can't fail proves nothing.
- **Build check:** `cd agda && agda src/Formal-Verification/Main-Theorem.agda`
  (`npm run agda` from `typescript/`). Must stay green.
- **The spec authority is the root `README.md`'s semantics-by-edge-case**,
  then Anthony's discretion (ask), then this Agda spec — in that order. If a
  postulate can't be proven because a definition is wrong, check the edge
  cases in the root README first; a divergence there is the real bug.
- **There is no reference tower to transcribe from.** (The previous
  generation, `agda/v1/`, has been deleted — it was legacy.) Prove the
  remaining postulates from first principles against the definitions in
  this tree; the references below to old-generation module names
  (`Protocol.agda`, `ranked-delivery`, …) are historical hints about the
  _idea_, not files you can open.

## 1. The shape of the whole proof

```
impl-batchSimultaneous em e                       ─┐
  = run (batchSimultaneousI (compile e)) (flatten em)
                                                   │ counting-recovers
batchSpecL (stamped em e)                         ─┘
  = batchSpecL (stampFrom 0 (groupsOf (compile e) (flatten em)))
                                                   │ cong batchSpecL
                                                   │   trace-faithful
batchSpecL (emits (⟦ e ⟧ em ρ₀ t₀))               ─┘
  = spec-batchSimultaneous em e
```

The two halves are INDEPENDENT — they can be worked in either order, by
different sessions. Trace-Faithful is where the semantic content lives
(machine ≍ denotation); Counting-Recovers is mostly mechanical (a fold
recovering group boundaries from registration counts).

## 2. Counting-Recovers.agda

`counting-recovers` is already the composition of four postulates. Prove
them in this order:

### 2.1 `counting-factors` (mechanical, do first)

> `run (batchSimultaneousI m) (flatten em) ≡ countBatches (groupsOf m (flatten em))`

The counting pipeline reads only the trace. `countBatches` is DEFINED in
the file (fold `bStep` over `syncB g₀ ∷ asyncBs ∷ endB`), and
`counting-factors-diamond = refl` already pins that the reification is
right on a concrete run — so this postulate is TRUE; it just needs the
induction.

Plan: generalize to arbitrary non-empty input lists `i₀ ∷ is` (the frame
must be the first input; `flatten` guarantees non-emptiness). Prove a
state-correspondence lemma by induction on `is`: after the composed
machine (`mergeMapRx ∘ scanRx ∘ endWithRx ∘ groupFirstRx`) processes a
prefix, its state is `(true, mem)`-shaped where `mem` is the `foldl bStep`
of the BItems so far, and the outputs so far are the collected flushes.
Watch out:

- `mergeMapRx (λ m → ofMaybe (cFlush m))`'s state holds a list of running
  `ofMaybe` machines — they are all _dead_ after their spawn step (ofRx's
  Bool state flips to true and they emit nothing ever after). You will
  need a small invariant: "every running inner in the mergeMap state is
  spent" (emits `[]` on every input). Prove that as its own lemma about
  `ofRx`/`emptyRx`.
- The `end` input goes through `endWithRx`, which appends `endB` AFTER
  the group's own items — check the last-step case carefully against
  `bItems`'s `++ (endB ∷ [])`.
- Keep it at `flatten em` if full generality fights back; only `flatten`
  shapes are ever consumed.

### 2.2 `Accounted` + `counting-groups` (the real content of this half)

> `Accounted gs → countBatches gs ≡ batchSpecL (stampFrom 0 gs)`

Strategy: **derive `Accounted` by attempting the proof.** Do induction on
`gs` with a window-state invariant and let the stuck cases dictate the
conditions; write them down as the definition of `Accounted`. Candidate
content (from reading `stepI`/`bStep` and v1's `Protocol.agda`):

- Group 0 (the frame) is unconstrained — `frameStepI` flushes it whole.
- For each later group `g` with any values: its emits form a _block_ such
  that, starting from the registration totals accumulated over all prior
  groups, the window logic (`owedStart` = count of the first emit's root,
  minus one per emit, plus `init`s/`close`s as they pass) reaches ≤ 1
  exactly at `g`'s last emit — so the accumulated values flush as ONE
  batch at the group boundary, never early, never late.
- Value-free groups must not flush (their emits leave no open window —
  e.g. pure registration/fin traffic).
- Registration totals never go negative; every `close` matches a live
  `init` (v1 `Protocol.agda` trace-validity is the reference).

Then `counting-groups` is: induction on `gs`, invariant "window closed at
every group boundary, `cTotal` = accumulated `trackRegs`", and per-group
an inner induction over the group's emits tracking the open window.
Compare `batchSpecL (stampFrom 0 gs)`: all of group j's values carry time
`(j , 0)`, so `batchSpecL` produces exactly one batch per value-bearing
group — prove a small lemma `batchSpecL-groups` first: stamping gives
same-time runs per group, so `batchSpecL (stampFrom 0 gs)` =
`filter non-empty (map values-of-group gs)`. That lemma is independent
and easy; do it before touching the machine.

### 2.3 `compile-accounted` (grammar induction)

> `Canonical e → Accounted (groupsOf (compile e) (flatten em))`

Once `Accounted` is concrete, this is an induction over `Exp` showing
every operator preserves it (each operator's output emits keep the block
discipline given its input does). Decompose into one preservation lemma
per operator (`srcI-accounted`, `mapI-preserves`, …, joins last), each a
named postulate first, then discharge one at a time — replacing
`compile-accounted`'s postulate with a defined value over the finer ones
as soon as the induction skeleton typechecks. The share case needs the
`CanE` threading (this is where `Canonical` earns its keep: delivery
blocks of a share's refs are consecutive only for registration-canonical
trees — v1 `ranked-delivery`).

## 3. Trace-Faithful.agda

### 3.1 First work item: DEFINE `Tracks`

Everything else in this half waits on this. Intended meaning: machine `m`
tracks denotation `d : Inner` in world `em` iff **for every spawn
position j**, running `m` from position j produces, grouped and stamped,
exactly `emits (d (j , 0))`. Candidate definition:

```agda
-- the inputs a machine spawned at position j experiences: the j-th
-- input REPLACED by spawnInput (a synthesized empty frame unless j = 0,
-- where spawnInput is the identity on the real frame), then the rest
spawnFlatten : {n : ℕ} → Emissions n → ℕ → List (In n)
spawnFlatten em j =
  spawnInput (at j (flatten em)) ∷ drop (suc j) (flatten em)

Tracks em m d =
  (j : ℕ) → ltℕ j (length (flatten em)) ≡ true
  → stampFromAt j (groupsOf m (spawnFlatten em j)) ≡ emits (d (j , 0))
```

where `stampFromAt j` stamps the FIRST group with tick j and subsequent
groups with j+1, j+2, … (the spawned machine's first response happens at
instant j — its synchronous flush rides the trigger). You will need `at`
(list indexing with a default) and `drop` in the Prelude. Check this
definition against reality before building on it: for `m = compile e`,
`d = λ u → ⟦ e ⟧ em ρ₀ u`, write `refl` instances at j = 0 AND at some
j ≥ 1 for `ofE` (a spawned `of` emits everything at tick j — the
denotation says `emits (ofT vs (j , 0))` = all values at `(j , 0)`) and
for `srcE` (a spawned source sees only the strict suffix). If a refl
instance fails, the DEFINITION is wrong, not the instance — adjust (this
is the cheap way to debug a simulation relation).

Note: at j = 0 this specializes to `tracks-stamped`'s statement (spawn
position 0 IS the real frame, `stampFromAt 0 = stampFrom 0`), so
`tracks-stamped` becomes a one-line proof once `Tracks` is real — do it
immediately after, it validates the definition.

### 3.2 `tracks-compile` (the grammar induction — the hardest thing here)

Generalize first: the induction needs environments. Define

```agda
EnvTracks : Emissions n → Env → ShEnv n → Set   -- slot-wise Tracks (+ connection instants line up)
```

and prove the generalized statement

```agda
tracks-compileE : EnvTracks em ρ σ → CanE w e w′ → (share-state consistency)
                → Tracks em (compileE σ e) (λ u → ⟦ e ⟧ em ρ u)
```

by mutual induction with `ExpS`/lists (mirror the shape of `⟦_⟧`/`⟦_⟧S`/
`⟦_⟧L` vs `compileE`/`compileS`/`compileL`). One lemma per operator, in
this dependency order:

1. **`srcE`, `ofE`, `emptyE`** — direct: unfold `srcI`'s responses per
   input against `srcT`+`refT`. `srcGo`'s positional ticks were built to
   match `flatten` exactly; this case is the sanity anchor.
2. **`mapE`, `scanE`** — pointwise: `mapRx`/`scanRx` transform each
   group's values in place; `mapL`/`scanL` do the same to the timed list.
   Key lemma shape: "stamping commutes with value-wise maps/folds in
   delivery order". scan's accumulator order = delivery order = the
   stamped list's order — this is where intra-batch ORDER is load-bearing.
3. **`takeE`** — the cut: `takeI` counts values mid-batch and closes
   inside the emit; `takeL n` + `takeCloseL`. The mid-instant cut
   (`take-full`) is the pinned corner.
4. **`mergeAllE`** — the first join. The machine side interleaves by
   registration rank within a step; the spec side is `mergeL` (stable,
   left wins ties). The bridge: within one instant, outer-trigger-first +
   spawn-order delivery = left-biased merge of same-time blocks. The
   `Joinable` split (ofJ/mapJ) means two subcases sharing one core lemma
   about `mergeItems`/`mergeStep`.
5. **Serial joins** — `concatAllL`'s recursion on `close` must align with
   the machine's queue-drain-at-fin; the spec subscribes a queued inner at
   `timeMax r a`, the machine feeds it `spawnInput` at the fin-carrying
   step — same instant by construction. Similar for switch (cutAt vs
   cut-before-react) and exhaust (timeLt drop vs open-drop).
6. **`shareE`/`letShareE`** — last. `EnvTracks` extension at `can-let`;
   the connecting ref is `Tracks`-related to `refT true` (full history at
   the connection instant), late refs to `refT false` (strict suffix —
   machine side: `lateView` drops the first response's values). This is
   where `CanE`'s threading is consumed.

Do NOT try to prove all of these in one session. Post one lemma per
postulate, keep `tracks-compileE` a defined value over them, discharge
one operator at a time, keep the tree green between each.

### 3.3 Known corners to keep in view

- **Order is exact, not up-to-permutation.** Both sides pin intra-instant
  delivery order (rxjs registration rank ↔ `mergeL` left-bias). If an
  order mismatch appears in a refl instance, that's a real bug in one
  side — compare against real rxjs (the TS oracle) before "fixing".
- **The origin coordinate of `Time` is currently always 0.** Reentrant
  feedback (a `.next()` fired from inside a batch) is not yet expressible
  in `Emissions` — when it is added, `stampFrom`'s `(j , 0)` and
  `spawnFlatten` acquire origin bookkeeping. Don't burn time generalizing
  for it now; don't paint it out either.
- **Resetting shares don't threaten THIS theorem.** Both sides implement
  the same non-resetting connecting-ref model, so impl ≡ spec holds on
  cold-share programs too; the reset divergence is model-vs-real-rxjs,
  owned by the TS oracle (deferred item). If a proof case seems to need
  a reset fence, re-examine — it probably doesn't.
- **`Canonical` may legitimately grow.** If an induction case genuinely
  needs a new side condition, that is a finding — add it to `Bridge.agda`
  with a comment, keep every existing `*-canonical` instance passing, and
  flag it to Anthony (he has approved growing the fence only when a proof
  demands it).

## 4. Definition of done

- Zero postulates under `src/` (grep `postulate`).
- `Main-Theorem.agda`'s full refl suite passes unchanged.
- Both trees green from a clean build (`rm -rf _build`).
- `agda/README.md` updated (it currently documents the seven postulates).
- Anything that changed semantics: a new pinned `refl` instance + a TS
  oracle case (TypeScript side) if it's observable behavior.
