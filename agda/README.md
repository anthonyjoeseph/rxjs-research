# The Agda development: the design authority

Everything in this directory exists to give a proof to one type:

```agda
formal-verification :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
```

In words: for every program `e` over `n` source subjects, and every thing
the outside world can do to it (`em`), the **implementation** — a machine
that sees one event at a time and has no clock — produces exactly the
batches the **spec** — a clairvoyant referee that sees the whole timed run
at once — says are correct.

Start reading at [src/Formal-Verification/](src/Formal-Verification/).
`formal-verification` is already a *value*, not a postulate: its proof term
is real. **Both sides are now fully defined** — the spec, the implementation,
every Naive-Rx operator, and the validity domain `Canonical` — so the
theorem statement *computes*: on concrete programs Agda normalizes both
pipelines end to end and they literally agree (`diamond-full`,
`share-diamond-full`, `growth-full`, `cascade-full`, … at the bottom of the
entrypoint, all proven by `refl`). Exactly two postulates remain, the two
named halves of the general proof (`counting-recovers`, `trace-faithful`),
each already instantiated by normalization. A postulate that cannot be
proven as stated is a spec bug to rework, not work around.

(The previous generation of this development — the proven burst-batching
denotation and protocol layer — lives in [v1/](v1/), still building, as the
reference the postulates here are discharged from.)

## The broad approach

Both sides import the same vocabulary
([src/Shared-Types.agda](src/Shared-Types.agda)): `Emissions` (what the
world does — per-source synchronous flushes plus a global schedule of
`.next()` calls), `Subscription` (what a subscriber's callback log reads),
and one shared grammar `Exp`/`ExpS` of the system's canonical primitives.
Each side then defines its own `batchSimultaneous` over that vocabulary —
and the two definitions are given *deliberately unequal powers*:

- **The spec is clairvoyant.** `spec-batchSimultaneous` receives the entire
  `Emissions` record, past and future, and may cheat freely: it assigns
  every value a timestamp, and batching is just "group equal times". Its
  timed observables carry their well-formedness BY CONSTRUCTION (`TObsOf`:
  sorted from the subscription time, bounded by the close), so the grouping
  operation is meaningful on every input it can receive, not
  meaningful-given-a-side-theorem.

- **The implementation cannot see the future — structurally.** It is not a
  function on `Emissions` at all. It is a **Mealy machine**: a state, and a
  step function that receives ONE input and produces outputs synchronously.
  The future never exists as a value it could inspect; there is no list it
  could measure. The harness (`run`, `flatten`) lives in Shared-Types, not
  in Implementation/ — the implementation exports machines and never holds
  the input list. Causality is a property of the *types*, not a promise.

The bridge between them is the protocol trace: `run (compile e) (flatten em)`
is the stream of provenance-tagged emits the pipeline produces, and the
theorem factors through it in two named halves — `counting-recovers` (the
batching machine, counting registrations blind, flushes exactly the groups
the referee finds by re-attaching the clock) and `trace-faithful` (the
stamped trace IS the spec's timed denotation, value for value).

Why Mealy machines and not some bespoke operational gadget: **rxjs
operators genuinely are Mealy machines.** `r.scan` is literally one — a
state and a step. That is why the TypeScript implementation is written in
pure-scan style, and why each Naive-Rx operator is a machine *transformer*
(machines in, machine out) — exactly as rxjs operators are
`Observable → Observable` functions, with `.pipe(...)` as application.

## The batchSimultaneous functions, side by side

The counting machine, TypeScript
([typescript/src/batch-simultaneous.ts](../typescript/src/batch-simultaneous.ts)):

```ts
export const batchSimultaneous = <A>(src: Instantaneous<A>): r.Observable<A[]> =>
  src.pipe(
    batchSync(),                 // the frame boundary: the subscribe call itself
    r.endWith({ type: "end" }),  // drain sentinel
    r.scan(step, initialMem),    // the counting machine: pure fold, no clock
    r.mergeMap(flush),           // emit a batch when a window drains to zero
  );
```

The same pipeline in Naive-Rx machines — the ACTUAL definition in
[src/Implementation/Batch-Simultaneous.agda](src/Implementation/Batch-Simultaneous.agda):

```agda
batchSimultaneousI : {n : ℕ} → Inst n Val → RxObs n (List Val)
batchSimultaneousI src =
  mergeMapRx (λ m → ofMaybe (cFlush m))
    (scanRx bStep (mkMem [] nothing nothing)
      (endWithRx endB
        (batchSyncRx src)))
```

Same stages, same order (Agda application nests where TS pipes, so read
inside-out), one machine per `.pipe()` stage — down to `batchSyncRx`,
which needs no defer gadget in Agda: the machine model structurally knows
the response to the first input, which IS the subscribe call.

And the two top-level definitions the theorem equates:

```agda
-- Spec/Batch-Simultaneous.agda — whole-input, clairvoyant, one line
spec-batchSimultaneous em e = batchSpec (⟦ e ⟧ em ρ₀ t₀)

-- Implementation/Batch-Simultaneous.agda — a machine, driven blind
impl-machine e            = batchSimultaneousI (compile e)
impl-batchSimultaneous em e = subscribeRx (impl-machine e) em
```

Note what the implementation's definitions *don't* take: the machine never
receives `em`. It meets the world one `In n` at a time.

## Module map

### [src/Prelude.agda](src/Prelude.agda)

Self-contained, no standard library. `Bool`, `ℕ`, `_≡_`, `List`, `_×_`,
`Maybe`, plus `Fin n` (a source index that cannot be out of bounds) and
`Vec A n` (per-source data of exactly the right length) — the two types
that make "a program over `n` sources" a compile-time fact.

### [src/Shared-Types.agda](src/Shared-Types.agda)

The vocabulary both sides speak.

```agda
record Emissions (n : ℕ) : Set where
  field
    syncs  : Vec (List Val) n      -- per source: its subscribe-time flush
    asyncs : List (Fin n × Val)    -- global .next() schedule; 1 entry = 1 instant

Subscription : Set → Set
Subscription A = List A            -- a subscriber's callback log, in order
```

`Emissions` is the referee's complete knowledge of a run. The async
schedule is global, not per-source — interleaving across sources is
observable, so it must survive in the type. `batchSimultaneous` produces a
`Subscription (List Val)`: the element type `List Val` is what carries the
batch boundaries (the diamond logs `[5, 10]` once, not `5` then `10`).

```agda
data Exp (n : ℕ) : Set where
  srcE …ofE …mapE …takeE …scanE …shareE …letShareE
  …mergeAllE …concatAllE …switchAllE …exhaustAllE
```

One grammar, imported by BOTH sides — exactly the canonical primitives,
with `mergeE`/`concatE`/`mergeMapE` as the derived one-liners they really
are.

```agda
record Machine (I O : Set) : Set₁ where
  field
    State : Set
    start : State
    step  : State → I → State × List O
```

The implementation's only computational medium, with `feed` (a burst of
inputs within one step) and `run` (the harness). There is deliberately
NO element-wise composition operator: piping elements one at a time
would erase which outputs one input caused — the very knowledge the
frame boundary and an inner's synchronous flush depend on. Operators
compose by machine-transformer application instead, exactly as rxjs
operators are `Observable → Observable` functions.

```agda
data In (n : ℕ) : Set where
  frame   : Vec (List Val) n → In n   -- the subscribe() call, with sync flushes
  next    : Fin n → Val → In n        -- one .next() = one instant
  endSlot : Fin n → In n              -- ONE source completes = one instant
  end     : In n                      -- final teardown sentinel (TS r.endWith)

flatten : Emissions n → List (In n)
```

The top-level input alphabet: `flatten` serializes an `Emissions` exactly
as the machine will experience it — subscribe, the `.next()` schedule,
then the sources completed in slot order (each its own instant, exactly
like the TS driver's per-subject `.end()` calls — so a concat leg spawned
by its predecessor's completion still fins on its own later input), then
teardown.

### [src/Spec/MonotonicList.agda](src/Spec/MonotonicList.agda)

```agda
Time = ℕ × ℕ                        -- (tick, origin), lexicographic

record TObsOf (A : Set) (t : Time) : Set where
  field
    emits   : TimedObs A            -- List (Time × A)
    close   : Time                  -- load-bearing: serial joins queue on it
    sorted  : SortedFrom t emits    -- well-formedness carried BY CONSTRUCTION,
    closeAt : timeLeq t close ≡ true --  RELATIVE to the subscription time
    bounded : BoundedBy close emits
```

Tick 0 is the frame; tick k+1 is async entry k; the origin coordinate
orders feedback (a reentrant `.next()` lands strictly after the batch that
caused it). Bundling the evidence is what makes the spec's "group equal
adjacent times" mean "group equal times, period" — and bundling it
*relative to the subscription time* is what dissolved v1's separate
`denote-wf` theorem into the types. Below the record: the raw timed-list
operators (`mergeL` — stable, left wins on ties, the model counterpart of
rxjs subscription order — `mapL`, `takeL`, `scanL`, `filterAfterL`) and
the preservation lemma toolkit every combinator's evidence is assembled
from, transcribed from the proven v1 Sorting module.

### [src/Spec/Batch-Simultaneous.agda](src/Spec/Batch-Simultaneous.agda)

The referee, **fully defined — no postulates in this file**. A timed
denotation by real structural recursion —

```agda
⟦_⟧ : Exp n → Emissions n → Env → (t : Time) → TObs t   -- TObs = TObsOf Val
```

— where `⟦ e ⟧ em ρ t` is the timed history observed by subscribing `e` at
time `t`, *well-formed at `t` by its type*. Cold inner streams denote
functions of their subscription time (`Inner = (u : Time) → TObs u` — the
type is v1's `WFDen` made structural: an inner is well-formed at every
subscription time because it cannot be anything else), the device that
makes burst batching compositional; `Env` assigns share slots their
connection instant and history. Each per-primitive combinator (`srcT` —
the source history DERIVED from `Emissions`, sync flush at tick 0, k-th
async at tick k+1, close at K+1+i matching `flatten`'s serialization
exactly — `ofT`, `mapT`, `takeT`, `refT`, the four joins, `ofST`,
`mapST`) is its v1 counterpart with the evidence fields constructed
inline. A source is a hot slot connected at t₀ whose every frame
subscriber is "connecting" (`refT true` — a subject flushes its frame
values to every subscriber present during subscribe); spawned refs see
the strict suffix. Then:

```agda
spec-batchSimultaneous em e = batchSpec (⟦ e ⟧ em ρ₀ t₀)
```

### [src/Implementation/Naive-Rx.agda](src/Implementation/Naive-Rx.agda)

The protocol and the operator set.

```agda
data Ev (A : Set) : Set where       -- what flows between operators
  init  : Prov → Ev A               -- a subscription chain came alive
  value : A → Ev A
  close : Prov → Ev A               -- a registration ended
  fin   : Ev A                      -- completion, carried in-band

Emit A = Prov × List (Ev A)         -- one next-callback invocation (TS: InstEmit)

RxObs n X = Machine (In n) X        -- a naive rxjs Observable
subscribeRx m em = run m (flatten em)
```

No timestamps anywhere — that is the point. Then one operator per rxjs
export the implementation consumes, **all defined — no postulates in
this file**: `ofRx`, `emptyRx`, `endWithRx`, `mapRx`, `scanRx`,
`mergeRx`, `takeWhileRx`, `mergeMapRx`, `concatMapRx`, `switchMapRx`,
`exhaustMapRx` are real step functions. `mergeMapRx` holds each running
inner as a dependent pair — which element spawned it, with the state of
that element's machine — and delivers in registration-rank order: outer
chain first, spawned flushes riding at their triggers, then existing
inners in spawn order. The three serial policies share that
architecture plus the policy bookkeeping (`concatMapRx` queues and
drains the queue INSIDE the completion step, so a queued inner's flush
rides the completing instant; `switchMapRx` cuts the live inner BEFORE
it reacts to the in-flight input — the outer's rank precedes every
inner's, and rxjs unsubscription takes effect mid-dispatch;
`exhaustMapRx` drops arrivals while one inner is open). One signature
difference from rxjs, and it is a modeling statement: rxjs carries
completion on a separate channel, the machine model carries it in-band,
so the serial policies — exactly the operators that must OBSERVE inner
completion — take the completion test as a parameter
(`isLast : Y → Bool`, rxjs's complete signal reified; the joins pass
`lastJ`, "the item carries a fin").

Several TS operators have NO counterpart here, because the pure model
dissolves them: `tap`/`finalize` exist only to maintain the multicast
registry by side effect; `defer`/`startWith` only to wrap the Subject's
mutable state (the naive subject is a direct machine); and — the big
one — **`connect`/`share` dissolve because machine values are
deterministic**: two copies of a machine driven by the same inputs
produce identical outputs, so multicast fan-out is free. The serial
joins use the outer machine twice where the TS multicasts it (the value
branch strips registration events, so nothing double-counts), and
share's per-ref semantics lives in `shareRefI`'s connecting-flag view,
on the Canonical non-resetting domain the theorem is stated over.

### [src/Implementation/Batch-Simultaneous.agda](src/Implementation/Batch-Simultaneous.agda)

The machine side of the theorem, **fully defined — no postulates in this
file**. It mirrors the TypeScript file for file: one definition per
`primitives.ts` export (`srcI`, `ofI`, `mapI`, `scanI`, `takeI`,
`shareRefI`/`letShareI`, the four `…AllI` joins with their
`JoinItem`/`MergeState`/`SerialState` scans transcribed fold for fold),
and `batchSimultaneousI` is the counting machine
(`batch-simultaneous.ts`). Three definitions are direct machines rather
than operator compositions, precisely where the TS, too, steps outside
combinators: the subject (TS: `new r.Subject` — here a STATELESS machine,
since the world's input is its state), the per-input grouping
(`groupFirstRx`/`onFirstRx`, the machine-model counterpart of the TS
`batchSync` gadget), and the share ref view. Inner streams reach the
joins **defunctionalized** as a `Joinable` — a static list of compiled
inners (`ofJ`) or a compiled template spawned per outer value (`mapJ`),
exactly the `InnerTemplate` device of the TS model — and every join runs
the `mapJ` pipeline, because `ofJ` is `of(srcs)` defunctionalized to
indices (TS: `merge = mergeAll(of(srcs))`, literally).

Why `Joinable` instead of a stream-of-streams wire, as in the TypeScript's
`Instantaneous<Instantaneous<A>>`? Two checkers force it, and both point
the same direction. **Universes**: a machine is a `Set₁` value, so a wire
carrying machines would need `Ev`/`Emit`/`Machine` lifted a universe level
(and the joins' states, holding running inners, lifted again) — universe
creep with no semantic payoff. **Termination**: the alternative of carrying
inners as raw `Exp`s and handing the joins a compiler
(`mergeAllI (compileE ρ) …`) passes the compiler to itself under-applied,
hiding the structural descent from the termination checker — and the
descent is genuinely subtle there. `Joinable` dissolves both: inners are
compiled AT the `ofS`/`mapS` node, where `f v` is a constructor-field
application the checker accepts as smaller, and the wires stay in `Set₀`
because a `Joinable` is a join *argument*, never a wire payload.

```agda
compile : Exp n → Inst n Val                     -- Inst n A = RxObs n (Emit A)
impl-machine e = batchSimultaneousI (compile e)
impl-batchSimultaneous em e = subscribeRx (impl-machine e) em
```

### [src/Formal-Verification/](src/Formal-Verification/)

The theorem, as a folder — **[Main-Theorem.agda](src/Formal-Verification/Main-Theorem.agda)
is the entrypoint**, [Bridge.agda](src/Formal-Verification/Bridge.agda) is
the shared vocabulary of the two proof halves,
[Counting-Recovers.agda](src/Formal-Verification/Counting-Recovers.agda)
and [Trace-Faithful.agda](src/Formal-Verification/Trace-Faithful.agda)
each define their half as a value over finer named postulates, and
[Roadmap.md](src/Formal-Verification/Roadmap.md) is the detailed plan for
discharging them.

The bridge is fully DEFINED: `groupsOf` is the referee's
grouped view of a run (the machine's responses kept grouped by input —
knowledge `run` concatenates away, as the proven `run-groups` lemma
states), and `stamped` re-attaches the clock positionally — `flatten`
places input j at tick j, so group j's values get time `(j , 0)`.

```agda
stamped em e = stampFrom 0 (groupsOf (compile e) (flatten em))
```

`Canonical` is the validity domain, now a real predicate: v1's ratified
**registration-canonical** fence. Share semantics are untouched — this is
a syntactic discipline. Per `letShareE` binder, the slot's
pre-order-first ref is its connecting ref (flagged true, exactly rxjs's
"first subscriber triggers connect") and every later ref is flagged
false; the relation (`CanE`/`CanS`/`CanL`) threads "is the connecting
ref still owed" per slot through the tree in registration order, and
`mapS` templates are quantified over their trigger value and may not
change the state (a spawned ref can never connect — a spawn arm written
left of its slot's connecting static arm is rejected, matching v1's
`ranked-delivery`).

The two halves of the general proof are both VALUES, each assembled from
the finer postulates its file names (seven in total — the only postulates
left in the development; see the Roadmap):

```agda
counting-recovers : … → impl-batchSimultaneous em e ≡ batchSpecL (stamped em e)
  -- = counting-factors ∘ counting-groups ∘ compile-accounted
  --   (the pipeline reads only the trace; the pure counting theorem on
  --    Accounted traces; canonical programs keep their books)
trace-faithful    : … → stamped em e ≡ emits (⟦ e ⟧ em ρ₀ t₀)
  -- = tracks-stamped ∘ tracks-compile
  --   (the Tracks simulation relation: spawned at any position j, the
  --    machine's stamped groups equal the denotation subscribed at (j,0))
```

The theorem is their composition, literally:

```agda
formal-verification em e can =
  trans (counting-recovers em e can)
        (cong batchSpecL (trace-faithful em e can))
```

And since both sides are now fully defined, the theorem statement
**holds by computation** on concrete programs — the bottom of the file
is a suite of `refl`-proofs where Agda normalizes BOTH pipelines
(compile, the joins' scans, the counting machine on one side; the timed
denotation and the clock-grouping referee on the other) and the two
sides literally agree, with no postulate in the path: `diamond-full`,
`take-full` (the mid-instant cut v1 had fenced behind `runMemCut`),
`scan-full`, `mergeMap-full` (spawned-inner coalescing), `merge2-full`,
`cascade-full` (a queued concat leg riding the take-cut's instant),
`switch-full`, `exhaust-full`, `share-diamond-full`, and `growth-full`
(the late-join growth law, `[7]` then `[8, 8]`). `diamond-counting` and
`diamond-trace` instantiate each half separately, and
`diamond-verified` runs the general theorem end to end on a real
`Canonical` proof term. What remains is generalizing the two halves
over all canonical programs.

## Relationship to the TypeScript

Agda proves *implementation ≡ spec*. It cannot prove *Naive-Rx ≡ real
rxjs* — the claim that `scanRx` faithfully models `r.scan`'s delivery
timing is the trust boundary, and it is covered by the fast-check oracle
on the TypeScript side ([typescript/src/__tests__](../typescript/src/__tests__)).
The thinner and more literal each naive operator is, the thinner that
boundary gets — which is why the operator set is exactly the TS import
list and nothing else.

## Building

```sh
agda src/Formal-Verification/Main-Theorem.agda # the entrypoint — everything else follows
cd v1 && agda src/Everything.agda # the v1 reference tower
```

Agda ≥ 2.6.2 (developed with 2.7.0.1). Self-contained — no standard
library.
