# The Agda development: the design authority

This directory is the ratified specification of the instantaneous-observable
semantics. **Agda is the design authority**: semantics questions are settled
here first, and the TypeScript model
([typescript/src/model.ts](../typescript/src/model.ts)) is a
line-by-line *transcription* of these files — any divergence over there is a
transcription bug, checked continuously by the fast-check oracle.

The semantics itself is **burst batching** (ratified 2026-07): one
`subscribe()` call is one root cause, so the entire synchronous subscription
frame is ONE instant; each subject `.next()` is its own fresh instant; and
every cascade — mapped values, spawned inners, completion cascades — inherits
the instant of the event that caused it. See the
[root README](../README.md) for the user-facing tour.

## The two layers

The development answers two different questions, in two layers:

1. **What are the right batches?** — the *denotational* layer
   ([src/Burst.agda](src/Burst.agda)). An observable is a time-ordered list
   of emissions; `batchSpec` groups equal Times. Timestamps exist here and
   nowhere else — they are the referee.
2. **Can a machine with no clock compute them?** — the *operational* layer
   ([src/Protocol.agda](src/Protocol.agda)). The implementation never sees a
   timestamp; it sees protocol events in delivery order, and decides batch
   boundaries by **counting registrations**. This layer proves the counting
   mechanism computes exactly what the referee defines — and it is where the
   non-local semantics live (share lives, delivery ranks), because only an
   operational model can see them.

### Layer 1: the timed denotation (Burst.agda)

The grammar is exactly the system's primitives — `of`, `empty`, `map`,
`take`, `share`, `scan`, `mergeAll`, `concatAll`, `switchAll`, `exhaustAll` —
two-sorted (`Exp` denotes a stream of values, `ExpS` a stream of inner
streams), with `merge`, `concat` and `mergeMap` as derived one-liners. The
technical device is the **subscription-time-parameterized denotation**:
`⟦ e ⟧ env t` is the observable obtained by subscribing `e` at time `t`, and
a cold inner stream denotes a *function* from subscription time to
observable. Burst batching then falls out by construction: a join hands each
inner its own subscription time (its arrival, or the previous close for the
serial joins), so static programs land entirely in the subscription instant
and spawned inners batch with their causes, transitively.

`share` is an environment of hot slots: `letShareE src body` binds a slot to
`src` subscribed at the binder's own time (the slot's content is *derived*,
not hypothesized), and a ref subscribed strictly after the connection sees
only the strict suffix — hot streams don't replay. `filterAfter-absorb`
proves connection time is irrelevant for hot bindings, which is why
binder-time connection is faithful.

Proven here (a sample): `denote-wf` (every program denotes a well-formed
observable — one induction case per primitive, the monotonicity-preservation
lemmas living in [src/Sorting.agda](src/Sorting.agda)); `frame-batch` (any
static program is at most one batch); the n-ary diamond tower
([src/Diamond.agda](src/Diamond.agda): `diamondN`, `diamond2`, with the
classic `diamond` as the corollary at `id`); `share-diamond`,
`share-growth` and `late-join-growth` (the README's `[7,7]` then `[8,8,8]`,
n-ary); the driver contract and `feedback-example` (a reentrant `.next()` is
a fresh instant strictly after the batch that caused it); and the five
formerly-fenced frontier theorems (transient refs, upstream races, tick-0
spawns, stateful folds across batches, multi-value units).

**Validity domain.** The flat compositional denotation is valid exactly for
programs whose shares never *reset* — a subject-backed binding with a
subscriber alive from the frame onward, which is every `letShareE` theorem
in the file. Resetting shares are layer-2 territory:

### Layer 2: the protocol and the counting machine (Protocol.agda)

This layer models what the machinery actually sees, with **no timestamp
anywhere in the types**. Its three core types — `Driver`, `Delivery`,
`Trace` — are abstractions of concrete rxjs happenings. Take the diamond:

```ts
const s = new InstantSubject<number>(); // one root subject; call its provenance p
const doubled = s.pipe(map((n) => n * 2));

merge(s, doubled)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

s.next(5); // logs [5, 10]
```

**`Driver A = List (ℕ × A)`** — everything the outside world does to the
program after subscribing it: the schedule of subject firings, in order,
each entry naming a subject slot and a value. The run above is the driver
`(0 , 5) ∷ []` — slot 0 fired once with 5. One driver entry = one
`.next()` call = one instant; the driver is where "time" lives, and it
never enters the protocol itself.

**`Delivery A = Prov × List (Ev A)`** — what ONE downstream `next` callback
invocation carries between operators (the TypeScript `InstEmit
{ provenance, events }`). When `s.next(5)` runs, the merge's subscriber's
`next` fires TWICE — once through each live subscription of `s` — so the
instant consists of two deliveries, both headed by `s`'s root provenance:

```
(p , [ value 5  ])     -- through the direct arm
(p , [ value 10 ])     -- through the map arm
```

The events inside are the four `InstEv` kinds, each an rxjs happening:

```
init p    a subscription of root p came alive     (rxjs: .subscribe reached a source)
value v   a value                                 (rxjs: a next callback's payload)
close p   a registration of root p ended          (rxjs: take cut a chain, switch switched away)
fin       the stream completes with this delivery (rxjs: complete — carried IN-BAND so
                                                   completion cascades stay in their instant)
```

A delivery can carry several events at once because operators COALESCE:
everything one incoming delivery causes rides the one outgoing delivery.
`mergeMap((n) => of([n * 10]))(s)` reacting to `s.next(5)` forwards the
single delivery `(p , [ value 50 ])` — the trigger value was consumed, the
spawned inner's synchronous flush rides in its place. A spawned
*subscription* is the same story with an `init`:
`mergeMap(() => other)(s)` forwards `(p , [ init q ])` — the new
registration of root `q`, announced inside the instant that caused it.

**`Trace A`** — one program's complete observable behavior over one driver
run: the `frame` (every event delivered synchronously during the
`subscribe()` call — the burst, one instant by definition) and `reacts`,
one list of deliveries per driver entry. The diamond's trace for the run
above is literally:

```
frame  = init p ∷ init p ∷ []                             -- two subscriptions of s
reacts = ((p , value 5 ∷ []) ∷ (p , value 10 ∷ []) ∷ [])  -- the response to (0 , 5)
       ∷ []
```

Now the whole game in one sentence: the grouping of `reacts` by driver
entry is knowledge only the referee has — the real machinery receives the
FLATTENED delivery stream (rxjs hands you one `next` at a time, never "this
instant is over") — and the **machine** must recover the grouping by
counting. It is the provenance memory as a pure fold: the frame's `init`s
make `totalNum p ≡ 2`; the first delivery of an instant opens a window
owing `totalNum p` deliveries; each delivery drains one slot; at zero,
flush — `[5, 10]`, no clock consulted. The theorem says counting alone
always recovers what the flattening erased:

```agda
endgame : OkTrace (applyEvs (λ _ → zero) fr) rs
  → machine (tr fr rs) ≡ forgetT (batchSpec (stamp (tr fr rs)))
```

`OkTrace` is the truthfulness invariant — *"recorded multiplicity equals
live registrations"*, as a datatype. `stamp` is the referee's view of the
same trace: it re-attaches the clock the driver defines (frame values at
`t₀`, driver entry k's values at tick k+1) and hands the result to layer
1's `batchSpec`. The diamond's trace stamps to
`((1 , 0) , 5) ∷ ((1 , 0) , 10) ∷ []`, which batches to one group —
exactly what the machine computed blind. The corollaries `frame-batch` and
`protocol-diamond` show the two headline behaviors decided by pure
counting, and `THE-ENDGAME` states the same equation over the full Burst
grammar (a proof term whose remaining gaps are named postulates — see
"Open edges").

**Share lives** (ratified 2026-07-07, confirmed against rxjs 7): a share
resets when its source completes or its refcount drains to zero, and a
subscriber arriving after a reset reconnects — a fresh life that replays a
cold source (`merge(shared, shared)` of a shared `of(5)` logs 5 twice).
Which life a subscriber joins depends on when its *siblings* closed —
non-local, hence operational. `shareLives` derives the behavior from the
mechanism (connect / fan out in registration order / reset / replay), and
the theorems `cold-share-lives`, `ranked-delivery` and `reset-replay` are
all `refl` — including **delivery ranks**: fan-out walks the live list in
registration order, so a subscriber spawned later delivers later regardless
of where its arm sits syntactically. The rank model is derived, not decreed.

Two protocol design decisions ratified by this layer, which the TypeScript
implements verbatim: registrations are counted **per root-cause provenance**
(a share is counting-transparent — each subscriber registers the roots
feeding it), and operators **coalesce** everything one incoming delivery
causes into one outgoing delivery (a spawned inner's synchronous flush rides
its trigger; a queued concat leg's flush rides the fin-carrying delivery).

## Module map

| Module | What |
| --- | --- |
| [Prelude.agda](src/Prelude.agda) | Self-contained prelude — no standard library |
| [Time.agda](src/Time.agda) | `Time = ℕ × ℕ` (tick, origin), lexicographic; boolean comparisons + soundness lemmas |
| [TimedObs.agda](src/TimedObs.agda) | Timed lists: stable `mergeT`, `batchSpec`, `filterAfter`, sortedness predicates |
| [Sorting.agda](src/Sorting.agda) | Monotonicity preservation per operator; `filterAfter-absorb` |
| [Diamond.agda](src/Diamond.agda) | The anchor laws: `diamondN` / `diamond2` / `diamond` over strictly monotone streams |
| [Obs.agda](src/Obs.agda) | `Obs = record { emits ; close }` + well-formedness |
| [BatchImpl.agda](src/BatchImpl.agda) | The accumulate-and-flush fold; `batchImpl-spec` (fold ≡ spec on EVERY stream) |
| [Burst.agda](src/Burst.agda) | **Layer 1**: the grammar, the denotation, the burst theorems |
| [Protocol.agda](src/Protocol.agda) | **Layer 2**: the protocol, the counting machine, `endgame`, share lives, ranks |
| [Everything.agda](src/Everything.agda) | Typecheck it all |

## Design choices that keep the proofs small

- **Self-contained prelude** — nothing to install or version-match.
- **Boolean comparisons + soundness lemmas**, not decidable-order records:
  programs branch on `if timeLeq …`, proofs are `rewrite` chains that flip
  comparisons to literals, and goals then *compute* — most proofs end in
  `refl`.
- **`if_then_else_` in program definitions** (`with` only inside order
  lemmas), so functions stay ordinary terms `rewrite` can drive.
- **Definitions in projection style where proofs rewrite through them**
  (`runMem` uses `fst`/`snd` of `stepD`, not a `with`-clause).
- **Invariants as inductive predicates mirroring list structure**
  (`StrictMono`, `OkTrace`), so hypotheses destruct in lockstep with lists.

## Open edges

The results we are building toward are written as bona fide **proof
terms** at the bottom of [Protocol.agda](src/Protocol.agda) — above all
`THE-ENDGAME` (the machine, fed the protocol behavior of any canonical
Burst program, produces exactly the batches the timed denotation defines)
— and every gap in their proofs is a **named postulate**, load-bearing
and explicit: the stamp↔mergeT bridge, shareLives truthfulness, the
full-grammar trace denotation (`traceOf`/`Canonical`) with its
truthfulness and faithfulness, and the truncation-aware machine.
Combinator preservation is already discharged (fully proven:
`fragment-endgame`, `diamond-fragment-endgame`, `of-subject-endgame`).
Discharging the remaining holes completes the proofs without touching
the statements, and precedes any further TypeScript work.

## Building

```sh
agda src/Everything.agda
```

Agda ≥ 2.6.2 (developed with 2.7.0.1). No standard library or `.agda-lib`
registration needed — the development is self-contained.
