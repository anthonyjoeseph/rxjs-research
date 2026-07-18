# Verified Glitch-Free Batching for Rx-Style Observables

A formally verified solution to the **diamond problem** ("glitches") in reactive
streams, built as a TypeScript implementation on real rxjs, an Agda model of the
same semantics, a machine-checked proof that the batching state machine matches
its specification, and a differential-testing harness that ties the two worlds
together.

---

## 1. The problem

In a reactive graph like:

```typescript
const s = hot<number>();
const a = s.pipe(map((x) => x + 1));
const b = s.pipe(map((x) => x * 10));
const out = combineLatestStyle(a, b);

s.next(5);
```

one root cause (`s.next(5)`) produces two downstream emissions (`6` and `50`).
A naive consumer observes the intermediate **glitch state** `[6, old-b]` before
settling on `[6, 50]`. This is the diamond problem.

## 2. The solution, in one paragraph

Every emission is tagged with a provenance **id** — an `InstEmit<A>` carries a
coalesced list of protocol events (`init`/`value`/`close`/`handoff`/`complete`)
plus the id of the _instant_ (root cause) it belongs to, the source it came
from, and its **kind** (a subscription's own burst vs an arrival delivery).
All emissions synchronously caused by one trigger share its instant id;
independent triggers always get distinct ids. A downstream operator,
`batchSimultaneous`, groups the stream by instant id, emitting each
causally-atomic batch exactly once, as soon as it is complete — a single
`InstEmit` whose value is the instant's list of values, still carrying its
instant id, so a batched stream is again an `Observable<InstEmit>` that feeds
every primitive (merge it with itself and batch once more). Completeness is
decided by counting: init/close traffic maintains the live-registration count
per source, each live registration forwards exactly one (possibly valueless)
delivery per arrival, and a share announces its fan-out with a `handoff`
event before it fires. Every fact is **writer-asserted** — each mint site
knows whether it is a subscription or a delivery, and why a registration
closed (`cut` by an operator vs `exhausted` on its own) — so a reader checks
the accounting rather than reconstructing it. Consumers act per-batch and
never observe glitch states.

The **thesis being verified**: an _online_ batcher — one that sees a single
emission at a time, keeps only its own state, and never looks ahead — recovers
exactly the same partition that a _clairvoyant_ observer of the entire stream
would assign.

## 3. Architecture at a glance

```
                    ┌──────────────────────────────────────────────┐
                    │                Shared artifacts               │
                    │   Exp syntax tree  ·  ObservableInput  ·      │
                    │   JSON schema  ·  (tick, ordinal) arbitration │
                    └───────┬──────────────────────────┬───────────┘
                            │                          │
                 ┌──────────▼─────────┐     ┌──────────▼──────────┐
                 │   Agda (proofs)    │     │  TypeScript (real)  │
                 │                    │     │                     │
                 │  evaluate          │     │  evaluator + Clock  │
                 │  (one evaluator,   │     │  (mirrors Agda      │
                 │   global Sched)    │     │   structurally)     │
                 │        │           │     │        │            │
                 │        ▼           │     │        ▼            │
                 │  canonical Stream  │     │  canonical stream   │
                 │        │           │     │        │            │
                 │        ▼           │     │        ▼            │
                 │  impl-batchSim ◄───┼──┐  │  batchSimultaneous  │
                 │  spec-batchSim     │  │  │        │            │
                 │        │           │  │  │        ▼            │
                 │   ✅ PROVEN ≡      │  │  │  also runs on stock │
                 └────────────────────┘  │  │  rxjs primitives    │
                                         │  └─────────┬───────────┘
                                         │            │
                                         │   fastcheck differential
                                         └── testing: streams compared
                                             up to id renaming (≈)
```

**What is proven** (`formal-verification-batchSimultaneous`): the batching
state machine ≡ its clairvoyant spec, for _all_ input streams, plus the id
laws that make the ids meaningful.

**What is tested** (fastcheck): that the Agda evaluator and the
TypeScript/rxjs pipelines produce the same canonical stream, over thousands of
generated seeds.

The proof burden was deliberately narrowed (see §10): there is **one**
evaluator in Agda, shared by spec and impl; the verified object is the batcher
alone. The evaluator's fidelity to real rxjs is the differential harness's
job.

---

## 4. Core data types

### 4.1 `InstEmit` — provenance-tagged emissions

```agda
data EmitKind : Set where
  subscribe delivery : EmitKind      -- who minted it: a subscription's own
                                     -- burst (owes nothing) vs an arrival
                                     -- delivery (pays the owed count)

data CloseReason : Set where
  cut exhausted : CloseReason        -- an operator ended it vs ran dry

data InstEvent (A : Set) : Set where
  init     : Source → InstEvent A                 -- a registration came alive
  value    : A → InstEvent A
  close    : Source → CloseReason → InstEvent A   -- a registration ended
  handoff  : Source → InstEvent A                 -- this share fans out next,
                                                  -- still inside this instant
  complete : InstEvent A                          -- the stream completes as
                                                  -- part of THIS emit

record InstEmit (A : Set) : Set where
  constructor _at_from_as_
  field events  : List (InstEvent A)   -- everything caused by one incoming emit
        instant : Id                   -- the instant it belongs to
        source  : Source               -- the arrival's source
        kind    : EmitKind             -- subscription burst or arrival delivery
```

In TypeScript, instant ids are `Symbol()`s. Since Symbols do not serialize,
all cross-language comparison is done **up to id renaming** (`≈`) — what is
compared is the _partition structure_, which is the only thing
batchSimultaneous computes anyway.

### 4.2 `ObservableInput` — finite, timed input traces

```agda
record Timed (A : Set) : Set where
  field wait : ℕ          -- actual gap = suc wait  (≥ 1, by construction)
        val  : A

data ObservableInput (A : Set) : Set where
  hot  : List (Timed A)               → ObservableInput A
  cold : List A → List (Timed A)      → ObservableInput A
       -- sync burst   async emissions
```

Decisions baked in here:

- **Delta encoding with gap = `suc wait`** makes per-source timestamps
  strictly increasing _by construction_ — no well-formedness predicate to
  carry through every theorem, and no source can emit twice in one tick.
- **Hot** anchors its deltas at the epoch (tick 0). **Cold** anchors at its
  _subscription tick_ — relative time, resolved to absolute at subscription.
- **Sync emissions have no timestamps.** They fire inside the subscribing
  cascade's instant and _inherit its id_ (see §7).
- Ticks are **logical order, not wall-clock time** (see §8, timing
  invariance). Two different sources _may_ collide on a tick; they remain
  distinct instants with distinct ids, arbitrated deterministically.

### 4.3 `Ty` / `Val` — a closed, first-order type universe

```agda
data Ty : Set where
  unitᵗ boolᵗ natᵗ : Ty
  _×ᵗ_ _+ᵗ_        : Ty → Ty → Ty
  obs              : Ty → Ty
```

`Val Γ (obs t) = Exp Γ [] [] [] t` — **a runtime observable is a closed
expression**. This is a load-bearing decision: inner observables are always
subtrees/syntax, never host-language closures, which keeps the dataflow graph
statically knowable, keeps `Exp` strictly positive, and makes the whole tree
JSON-serializable for the harness. Sums (`+ᵗ`) exist for the Either-based
error story and sentinel-tagging patterns.

---

## 5. The `Exp` syntax tree

The expression tree is the **shared artifact** between all interpreters. It is
indexed by four contexts:

| Context | Meaning                                                                               |
| ------- | ------------------------------------------------------------------------------------- |
| `Γ`     | program slots (a `Vec Ty n`; `input : Fin n → …` points into the `Slots Γ` telescope — scripted inputs **and** shared observables, §5.5) |
| `Δᵍ`    | **guarded** recursion variables (bound by `μᵉ`, _not yet usable_)                     |
| `Δ`     | **usable** recursion variables                                                        |
| `Θ`     | value variables (bound by function terms)                                             |

### 5.1 The primitives

`input`, `ofᵉ`, `emptyᵉ`, `mapᵉ`, `takeᵉ`, `scanᵉ`, `mergeAllᵉ`,
`concatAllᵉ`, `switchAllᵉ`, `exhaustAllᵉ`, `μᵉ`/`varᵉ`, `deferᵉ`.

This set was chosen so that (nearly) all of rxjs is derivable — the claim
being: if `batchSimultaneous` is correct on every combination of these, it is
correct on everything built from them. Scheduling operators are out of scope;
error handling is recovered via `+ᵗ` (Either). `share` is deliberately
absent: share identity is a _binding_, not an expression, so shared
observables live in the slot telescope (§5.5) and are referenced with
`input`.

Notable signatures:

```agda
takeᵉ : Tm Γ Δᵍ Δ Θ natᵗ → Exp … t → Exp … t
```

**Parameterized take**: the count is a _term_, evaluated once, at subscription
time — matching TS closure capture (`take(v)` inside a mergeMap lambda). The
policy generalizes: any scalar parameter a primitive carries is a `Tm`, so
inner pipelines can be shaped by the triggering emission.

### 5.2 Recursion: `μᵉ` / `varᵉ` / `deferᵉ` — guardedness by typing

`expand` is **not** a primitive. It (and arbitrary recursive stream
definitions: recursion under `switchAll`, mutual recursion via nested μ —
Bekić's theorem, no dedicated construct needed) derives from a guarded
fixpoint binder:

- `μᵉ` binds a variable into `Δᵍ` (guarded — _invisible_ to `varᵉ`).
- `deferᵉ : Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t` is the **sole gate**
  that shifts guarded variables into usable scope.
- Therefore **synchronous self-reference is a type error**, not a semantic
  rule. `expand(v => of(v+1))` with a synchronous inner — a genuine infinite
  loop in real rxjs too — is unrepresentable.

`deferᵉ`'s semantics: subscribing at tick `k` subscribes the body at `k+1`,
and the body's emissions **mint fresh ids** (it is an async boundary). ⚠️
Naming caution: rxjs's `defer` is lazy-but-same-instant; `deferᵉ` is that
_plus a one-tick hop_. Its TS twin is `defer(thunk)` composed with the async
boundary. Comment this in both codebases.

Derived expand (`X = merge(s, mergeMap f (defer X))`):

```agda
expandᵈ f s =
  μᵉ (mergeAllᵉ (ofᵉ
       ( strmᵗ (wkᵍ s)
       ∷ strmᵗ (mergeAllᵉ (mapᵉ (wkᵍ f) (deferᵉ (varᵉ (here refl)))))
       ∷ [])))
```

### 5.3 Functions are syntax: the `Tm` language

`mapᵉ`/`scanᵉ` take `Fn Γ Δᵍ Δ Θ s t = Tm Γ Δᵍ Δ (s ∷ Θ) t` — a first-order
term with one extra bound variable, **not** a host-language function. Term
constructors: variables, literals, pairs/projections, `inl`/`inr`/`case`,
`ifᵗ`, `primᵗ` (base operations — currently a postulate; **must** become a
concrete datatype before the JSON bridge), and crucially:

```agda
strmᵗ : Exp Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (obs t)
```

`strmᵗ` embeds expressions as stream-typed _values_, which is how higher-order
operators work:

```
mergeMap f = mergeAllᵉ ∘ mapᵉ f      -- where f's body ends in strmᵗ
```

The bound emission reaches the inner observable through `varᵗ` at `Tm` leaves.
Value-dependent _shape_ is expressible (`ifᵗ` at type `obs u` selects between
`strmᵗ e₁`/`strmᵗ e₂`); computing an `input` index _from a value_ is not —
deliberately, since it keeps the dataflow graph static.

### 5.4 Worked derivations

```
merge a b     = mergeAllᵉ (ofᵉ (strmᵗ a ∷ strmᵗ b ∷ []))
filter p      = mergeMap (λ v → if p v then of v else empty)
completionOf s = concatAllᵉ (ofᵉ (strmᵗ (mergeMap (λ _ → emptyᵉ) s)
                                ∷ strmᵗ (ofᵉ (unit̂ ∷ [])) ∷ []))

-- takeUntil needs fan-out, so its source must be a SHARED SLOT (§5.5):
-- allocate slot j = shared s, then reference it twice
takeUntil n j = switchAllᵉ (merge (ofᵉ (strmᵗ (input j) ∷ []))
                                  (mapᵉ (strmᵗ emptyᵉ)
                                        (takeᵉ 1 (merge n (completionOf (input j))))))
```

`completionOf` deserves a note: the naive takeUntil (without it) hangs when
the source completes while the notifier stays silent — **in real rxjs too**;
the model faithfully reproduced a real behavioral gap of the encoding rather
than papering over it. The fix reifies "completion of s" as an emission using
the completion machinery already in the primitive set: **take**
(count-triggered completion) + **concatAll** (completion-triggered
subscription) + a **shared slot** (safe fan-out). Together these make
completion a first-class value — the load-bearing trio behind takeWhile,
endWith, skipUntil, etc. If a derived operator ever can't be written, expect
the deficit to be a missing `Tm` construct, not a missing primitive.
Derivations that share are *patterns*, elaborated per use site — each use
allocates its own slot, exactly as each rxjs call would invoke `share()`
afresh.

### 5.5 Shared observables: the slot telescope

`share` is not an `Exp` node because share identity is a **binding**, not an
expression — `const s = src.pipe(share())` used twice is one share, while
writing `src.pipe(share())` twice is two, and a pure tree erases exactly
that distinction. So the program carries it structurally:

```agda
data Slot Γ t : Set where
  scripted : ObservableInput (Val Γ t) → Slot Γ t   -- hot/cold script
  shared   : Closed Γ t → Slot Γ t                  -- def, share() at its root

Slots Γ = ∀ i → Slot Γ (lookup Γ i)
```

A program is a main expression over a slot telescope: `input i` references
either kind of slot, and a shared def may reference only **strictly
earlier** slots (a generator/decoder invariant, not enforced by the types —
a forward reference diverges at connect time). The TS compile of a
telescope is literally a chain of JS `const`s, which is the correspondence
argument in one line.

Semantics — rxjs `share` with **every reset option false** ("turn the cold
observable hot"):

- **Connect once, lazily.** The def is subscribed at its first subscriber's
  tick (its colds anchor there); a never-referenced slot never runs.
- **Never disconnect.** Losing all subscribers does not stop the
  underlying — an unobserved share still burns arrivals (observable through
  fuel).
- **Latch completion forever.** A post-completion subscriber gets an
  immediate close/complete and no values — unlike default rxjs `share()`,
  whose `resetOnComplete: true` re-runs the source for each late
  subscriber (`share(of(1,2,3))` replays per subscriber there; here it
  latches).
- **Fan-out is the counting protocol.** The share is a `Source` whose id is
  its slot index (the hots' convention); one upstream arrival yields one
  emit per registration, all in the same instant. The diamond problem is
  this clause. The upstream emit that triggers a fan-out passes through
  first, emptied of values, carrying a **`handoff`** event for the share —
  the announcement that the fan-out follows in the same instant, which is
  what lets an online reader account for multi-round fan-outs and never
  mistake a mid-instant lull for the instant's end.

Why all-resets-false is the primitive: the resets are not derivable from it
(recovering `resetOnComplete: true` needs a fresh *shared* identity minted
per reset at runtime — cache territory, `shareReplay`'s family), while
nothing derivable needs them. The one bit of runtime history a late
subscriber can read is the completion latch — **completion is
re-observable, values are not** — and that bit is precisely what the
completion-driven derivations (takeUntil & co.) consume.

The expressiveness boundary, stated consciously: the telescope expresses
every behavior whose **share-instance count is statically known** — one
slot per use site. Out of scope: a fresh share per runtime instantiation
(per-`mergeMap`-lambda invocation, per-μ-unfolding). Derived operators that
share are therefore top-level patterns, not first-class operators.

---

## 6. The evaluator and its global scheduler

There is **one** evaluator:

```agda
evaluate : Fuel → Closed Γ t → Slots Γ → Stream Γ t
```

producing the flat **canonical stream** — the single sequence of `InstEmit`s
that both the spec and the impl of batchSimultaneous consume.

### 6.1 The driver loop

```
sched := sched-init e ins            -- hots at anchor 0; shares connect lazily
repeat fuel times:
  arrival := sched-next sched        -- min by (tick, ordinal)
  run arrival's cascade to quiescence
  append its emissions to the stream
```

**Fuel counts arrivals processed** — run-to-quiescence, never truncating a
cascade mid-batch. Time (the arrival sequence, unbounded because of μ) is the
only dimension fuel bounds; _work within an instant terminates structurally_
(§6.3). The TS driver is written as the structurally identical
`for (let i = 0; i < fuel; i++) processNextArrival()` so the unit cannot
drift. Two hots colliding on a tick = two arrivals = two fuel decrements.

### 6.2 The scheduler (`Sched`) and `subscribeE`

`Sched` is the "shared global timeline": the set of live sources with their
pending arrivals keyed `(tick, ordinal)`. It is a plain value **threaded
through the evaluation fold** — no IO, no global mutable state, mirroring the
TS `LiveSource` design:

```typescript
type LiveSource<A> = { ordinal: number; pending: [number /*abs tick*/, A][] };
// "next" = pure min over (tick, ordinal); subscription returns the sync
// burst (processed now) + the new LiveSource (merged into threaded state)
```

```agda
subscribeE : Closed Γ u → Path Γ u t → Id → Tick → Sched Γ → EvalSt e
           → Stream Γ u × Sched Γ × EvalSt e
```

Called by evaluator clauses that subscribe things (`*All`s on inner arrival,
`deferᵉ`, μ-unfolding, share connects). The `Path` is the rootward
continuation registered for every source the subtree contains: a chain
either reaches the `root` or ends at a `share-sink` — delivery to a shared
slot, which fans out to that slot's registered chains within the same
instant (`dispatchShare`). It: fires the cold's **sync burst immediately,
inside the given cascade id** (id-inheritance is literally this argument
being reused); resolves the cold's deltas to **absolute** ticks anchored at
the current tick; registers the async future in `Sched` under a **fresh
ordinal (subscription order)**; initializes the node states. `deferᵉ` bodies
register at `tick + 1`.

**Arbitration** — the single discipline both languages must share: arrivals
are totally ordered by `(tick, ordinal, position-within-source)`; Γ-sources
get ordinals in input-index order, dynamic sources in subscription order.
Since both sides walk the same tree on the same inputs, they mint the same
ordinals. In TS this is a sort key / insertion counter; in Agda it is the
`sched-next` min. **This scheduler is the most correspondence-critical code
in the project** — it _is_ the semantics, and deserves its own step-level
differential tests (identical `Sched` states in, compare picked arrival and
updated state).

⚠️ TS discipline: everything within a tick runs **synchronously**. No
`Promise.resolve().then`, no `queueMicrotask` inside operator code — real-JS
time must never leak back in.

### 6.3 Operator clauses and cascade termination

Value operators are pure Mealy steps, one clause per constructor, that never
see `Sched`:

```agda
stepNode (scanᵉ f z) (next (v at i)) (scanSt acc) =
  let acc' = applyFn f (acc , v)
  in ( emitO (acc' at i) ∷ [] , scanSt acc' )          -- id i passes through

stepNode (takeᵉ k src) (next (v at i)) (takeSt (suc n)) =
  ( emitO (v at i) ∷ (n ≟ 0 → completeO) , takeSt n )   -- count set at subscribe
```

The cascade — one arrival propagating **rootward** through the fixed tree —
terminates structurally, with no fuel/gas in the semantics:

1. emissions only move toward the root (remaining path shrinks);
2. sync spawns (cold bursts, `ofᵉ` inners) are finite lists, also propagating
   rootward from the spawn point (lexicographic measure);
3. the two things that could run forever are **unrepresentable**: μ-feedback
   must cross `deferᵉ` (next tick, by typing), and inners are subtrees — no
   operator can conjure unboundedly new nodes within an instant.

(If Agda's checker needs help with the lexicographic measure, use
well-founded recursion on a size, or an _inner_ gas computed from
tree-size × burst-lengths with a one-time sufficiency lemma — an
implementation crutch, distinct from semantic fuel.)

### 6.4 Historical note: why there is no `Req` type

An earlier design had operators _request_ effects (`subscribe`/`defer`/…)
via a `Req` datatype. It was removed twice over: `defer` became **syntax**
(so guardedness is a type-level fact), and the remaining lifecycle verbs
became **evaluator clauses** reading operator state (e.g. `SwitchSt` holds
the current inner's `Id`; the switch clause unsubscribes/subscribes itself).
Consequences: step types are pure Mealy (`Evt → S → List InstEmit × S`) — the
sharpest form of the intrinsic no-cheating guarantee; state types are richer
(`ConcatSt` queues pending inner _expressions_); and lifecycle timing is only
observable via whole-program traces or by serializing node state — **expose
node states to the serializer** for step-level differential tests, or
subscription-timing bugs hide until they surface several nodes downstream.

---

## 7. The verified object: `batchSimultaneous`

```agda
spec-batchSimultaneous : List (InstEmit A) → List (InstEmit (List A))
  -- clairvoyant: sees the whole stream — group emits by instant id,
  -- concat their values in stream order, drop valueless instants;
  -- each batch keeps its instant id (a batched stream re-batches)

step-batch : InstEmit A → BatchSt A → List (InstEmit (List A)) × BatchSt A
impl-batchSimultaneous  = fold step-batch ++ flushBatch
  -- online: one emission at a time, own state only
```

The two sides read **different** information — the spec reads instant ids,
the impl reads kinds, counts, and handoffs — so they agree only on streams
where the two vocabularies tell the same story. That contract is
`WellFormed` (`Rx.Protocol`): an online automaton over the live-registration
multiset and the open instant's owed table, checking instant freshness
(one contiguous run, never recurring), bracketing (every close matches a
live init), fan-out exactness (subscribe emits owe nothing; a delivery from
`s` pays `owed[s]`, seeded from `live(s)` at the arrival and bumped by
`live(x)` at every `handoff x`; instants close fully paid), and complete
discipline (nothing after `complete`). The proof is a sandwich:

```agda
evaluate-well-formed :                          -- the primitives' half
  ∀ fuel e ins → WellFormed (evaluate fuel e ins)

batch-agreement :                               -- the batcher's half
  ∀ xs → WellFormed xs →
  spec-batchSimultaneous xs ≡ impl-batchSimultaneous xs

formal-verification-batchSimultaneous :         -- THE verified object
  ∀ fuel e ins →
  spec-batchSimultaneous (evaluate fuel e ins)
    ≡ impl-batchSimultaneous (evaluate fuel e ins)
formal-verification-batchSimultaneous fuel e ins =
  batch-agreement _ (evaluate-well-formed fuel e ins)   -- already a definition
```

`batch-agreement` is quantified over **streams**, not trees — its proof is
induction over a list with an invariant relating `BatchSt` to the spec's
partition-so-far: no tree, no scheduler, no operator semantics in sight.
`evaluate-well-formed` is one preservation lemma per primitive — a primitive
is correctly implemented iff its clause preserves the protocol automaton's
invariant. The composition is discharged forever; all remaining proof debt
lives in the two lemmas.

### 7.1 The id laws (the bridge premise)

`formal-verification` alone says "the partition matches the ids." Two laws
make the ids _mean provenance_ — together: **emissions share an id iff they
came from the same root cause**:

- **`id-inheritance`** (grouping doesn't miss): everything synchronously
  downstream of one trigger carries the trigger's id — including sync bursts
  of _newly subscribed_ inners (`mergeMap(v => of(v*10))`: the `of` fires
  inside the trigger's instant and inherits). Failure ⇒ batches too small ⇒
  glitches leak.
- **`id-fresh`** (grouping doesn't over-merge): distinct arrivals never
  collide on an id — including two sources colliding on a tick (same tick,
  different ordinals, different ids). Failure ⇒ batches too big ⇒ separate
  moments falsely atomized.

The `*All` operators' id rule, stated once: _the id is per cascade —
a synchronously-spawned inner inherits the trigger's id, never mints; only
the inner's later, async emissions mint new ids._

- **`batch-online`** (no lookahead, extrinsically): once a group is emitted
  it is never reopened — output on a prefix is a prefix of output, _modulo
  the possibly-still-open last group_ (state it against `step-batch`'s
  emitted groups, pre-flush). This is what makes batchSimultaneous a real
  streaming operator rather than `toArray()` postprocessing: a subscriber
  can commit per-batch, finally. It is only _possible_ because inheritance
  guarantees no stray same-id emission lurks in the future — the three laws
  are one mechanism seen from three sides.

### 7.2 Evaluator-level theorems

Stated against `evaluate`; proven where cheap, differentially tested always:

| Theorem             | Statement (informally)                                                                                          |
| ------------------- | --------------------------------------------------------------------------------------------------------------- |
| `fuel-coherent`     | more fuel only extends the stream (prefix)                                                                      |
| `causality`         | scripted slots agreeing before tick k (shared defs equal) ⇒ outputs agreeing before tick k (no clairvoyance)    |
| `locality`          | each node's next state factors through _its_ inbox + _its_ state                                                |
| `non-interference`  | perturbing other nodes' states can't reach node v except via emissions actually delivered to v                  |
| `μ-unfold`          | one μ-unfolding changes nothing observable (fixpoint law — also a free differential test vs TS thunk recursion) |
| `μ-guarded`         | k arrivals force ≤ k unfoldings (falls out of the `deferᵉ` typing gate)                                         |
| `defer-shift`       | `deferᵉ e` ≈ `e` with ticks +1 (≈: body ids re-minted)                                                          |
| `timing-invariance` | see §8                                                                                                          |

The **intrinsic** no-cheating story is free: a step typed
`Evt → S → List InstEmit × S` _cannot_ see the future or other nodes —
they're not in scope. The extrinsic theorems restate this about observable
behavior so it survives refactoring. Caveat honestly: none of this constrains
what an operator does with legitimately-held information (`scan` remembers
the past — allowed and necessary); the meaningful content is the conjunction:
narrow types + causality + non-interference = a causal, compositional stream
function.

---

## 8. Time: ticks, ordinals, and timing invariance

Ticks are a **logical strict ordering**, not wall-clock time — in
single-threaded JS no two emissions truly share an instant anyway. What
matters is only _order and coincidence_, and the formal expression of that is:

```agda
timing-invariance :
  evaluate fuel e (retime ρ ins) ≡ evaluate fuel e ins
  -- ρ : any monotone re-timing preserving the (tick, ordinal)
  -- arbitration order of all arrivals, collisions included
```

Design decision this forced: **mint ids from arbitration-order position
(ordinal rank), not from raw ticks** — otherwise retiming changes ids and the
theorem degrades to ≈. Ordinal-rank minting is also what TS naturally does
(a counter). Practical payoff: fastcheck can sample waits from tiny
distributions (0/1/2) to hammer interesting interleavings, and shrink
timestamps aggressively, without changing semantics.

---

## 9. The differential-testing harness

**Trust structure**: the Agda theorem covers batcher-≡-spec for _all_
streams; fastcheck covers evaluator-≈-rxjs for _sampled_ trees. Together the
untrusted gap is exactly one link.

Components:

1. **One generator** (TypeScript): seed → PRNG → `Exp` tree + slot telescope
   (`ObservableInput` scripts and shared defs).
   Pass _serialized artifacts_ to Agda, not seeds — then Agda needs no PRNG,
   "same inputs" holds trivially, and failures arrive already in shrinkable,
   regression-corpus JSON form. Make the generator emit μ/`varᵉ` at various
   depths and deliberate tick collisions, or those paths stay proven-but-untested.
2. **A shrinker over trees** — a 3-node counterexample is debuggable; a
   40-node one is not.
3. **Three runners**: Agda `evaluate` (via long-lived JSON-over-stdio process,
   or compiled with the Agda JS backend and imported directly — process
   spawn per case is too slow); the TS mirror evaluator; stock rxjs built
   from the TS primitives.
4. **Comparison** under `≈` — partition structure up to id renaming (Symbols
   don't serialize; specific ids are meaningless). The collector records
   `(tick, id, value)` triples, _not_ bare `.toArray()`, which loses grouping.
5. **Step-level tests**: serialize node states; feed identical
   `(state, event)` pairs to each operator in both languages — tells you
   _which operator, which state_ diverged, where whole-program tests only say
   _something_ did. Ditto the scheduler (§6.2). Whole-program tests then
   mostly carry the plumbing: routing, cascade order, id inheritance.
6. **rxjs leg driver**: deliver each arrival's cascade synchronously within
   one turn; the "my instants = this notion of rxjs time" claim is the one
   _asserted_ (not tested or proven) piece of the correspondence — write it
   down explicitly.

---

## 10. Design history: decisions and their reasons

Chronological, because the _reasons_ are the documentation:

1. **Finite traces + fuel, not coinduction.** Inputs are finite;
   μ makes _output_ unbounded, so `fuel` (a prefix index) with
   `fuel-coherent` (the take lemma) gives prefix semantics — agreement at
   every fuel _is_ equivalence. Coinduction/sized types were rejected as
   heavier (bisimulation vs `refl`-adjacent reasoning; sized-type soundness
   warts) and unnecessary.
2. **Tree = subscription graph; no mutable rewiring.** Raw
   subscribe/unsubscribe semantics permit runtime cycles (a Subject fed its
   own output) — _that_ is what breaks termination. The `hot`/`cold`
   constructors can't express feedback; merge-with-self is sharing, not a
   cycle. Unsubscription is state (masking), not mutation.
3. **expand ⇒ μ.** A hypothetical `fixᵉ : (Exp → Exp) → Exp` is rejected by
   positivity (negative occurrence). The guarded binder `μᵉ`/`varᵉ` with
   once-per-tick unfolding is strictly more expressive (recursion under
   switchAll, mutual recursion via nesting/Bekić) — matching what TS can do
   with lazy top-level closures, which is the same mechanism (`defer` thunks)
   doing the same safety work.
4. **Functions ⇒ first-order `Tm`.** Host closures in `mapᵉ` reintroduced the
   positivity problem via `Val (obs t)`; syntactic terms fix it at the root,
   drop everything to `Set₀`, and are what makes JSON serialization possible
   at all.
5. **`defer` ⇒ syntax.** Moving the one clock-touching construct out of the
   effect vocabulary and into the grammar made μ-guardedness a _typing_
   fact (`Δᵍ`/`Δ` split, Fitch-style) instead of an evaluator discipline.
6. **`Req` ⇒ deleted.** Primitives are the base-level cross-language link;
   lifecycle authority lives in evaluator clauses; steps are pure Mealy.
7. **Timestamps ⇒ strictly-positive deltas + `(tick, ordinal)` arbitration.**
   Making cross-source collisions _unrepresentable_ would require a global
   schedule that is a function of the execution it schedules (dynamic
   sources) — rejected as pointless work; a shared deterministic tiebreak is
   sound and cheap.
8. **Virtual scheduler ⇒ pure `min` over threaded state.** No
   setTimeout, no thunk queues: resolve relative→absolute at subscription
   time, then "next" is a pure min by `(tick, ordinal)` — identical shape in
   both languages.
9. **Two evaluators ⇒ one.** The realization: clairvoyance never helped
   evaluate the tree (cold inners must be subscribed either way); it only
   ever applied to _batching_. So the spec/impl split moved to the batcher,
   quantified over streams. The theorem got smaller (no "two evaluators
   agree" proof) and stronger (it isolates exactly the novel claim). Cost,
   eyes open: "formally verified" now means _the batcher_; the evaluator is
   tested, not proven.
10. **Fuel = arrivals, run-to-quiescence.** Emission-budget fuel was
    considered and rejected: truncating mid-cascade makes the depletion
    order part of the spec, splits batches (semantic poison when the output
    _is_ the grouping), and the rxjs harness leg can't be budget-stopped
    anyway. Arrivals-with-quiescence keeps every prefix theorem in clean
    `take` form while staying decoupled from batching.

---

## 11. Implementation roadmap

Postulates that are really **definitions to write** (finite structural
recursions; `formal-verification` proofs need them to _compute_):
`evalTm`, `applyFn`, `unfoldμ`, `wkᵍ`, `step-batch`/`flushBatch`, and the
glue identifying `impl-batchSimultaneous` with the fold (the evaluator,
`spec-batchSimultaneous`, and the `Rx.Protocol` automaton are already
defined). `PrimOp` must become a concrete datatype (a postulate can't be
serialized or given a TS twin). `id-inheritance` and `defer-shift` need their
`⊤` placeholders replaced once `ids-of` / tick-shift vocabulary is defined.

Suggested order:

1. `Tm`/`Val`/substitution (`evalTm`, `applyFn`, `wkᵍ`, `unfoldμ`) — pure
   syntax, no semantics.
2. `Sched` + driver loop + `subscribeE` — and its TS twin, with step-level
   scheduler tests from day one.
3. Evaluator clauses, one constructor at a time, mirrored in TS; step-level
   differential tests per operator as each lands.
4. `step-batch` + `flushBatch`; prove `batch-agreement`,
   `evaluate-well-formed`, and `batch-online`.
5. Id laws (`id-inheritance`, `id-fresh`) — the bridge premise.
6. Harness: generator, shrinker, JSON schema (generate TS types + Agda
   decoder from one schema, or round-trip test the codecs), three runners,
   ≈-comparison.
7. Remaining evaluator theorems (`causality`, `timing-invariance`, μ laws)
   as time permits — each is independently valuable and independently
   testable.

## 12. Glossary

| Term                  | Meaning                                                                    |
| --------------------- | -------------------------------------------------------------------------- |
| **instant / cascade** | one root arrival plus everything it synchronously causes                   |
| **id**                | provenance tag; one per instant; the thing batchSimultaneous groups by     |
| **tick**              | logical time coordinate; ordering only, no wall-clock meaning              |
| **ordinal**           | subscription-order index; tiebreak for same-tick arrivals                  |
| **arrival**           | one pending emission in `Sched`, keyed `(tick, ordinal)`                   |
| **fuel**              | number of arrivals the evaluator processes (run-to-quiescence)             |
| **canonical stream**  | `evaluate`'s flat output; the single input to both batchers                |
| **sync burst**        | a cold's immediate emissions on subscription; inherits the subscriber's id |
| **guarded (Δᵍ)**      | bound by μ but unusable until shifted across `deferᵉ`                      |
| **≈**                 | equality of partition structure up to id renaming; the harness's relation  |
