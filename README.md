# rxjs-research: Instantaneous observables

Research into overcoming the **rxjs diamond problem**: a new kind of observable
(an `Instantaneous`) that tracks the *provenance* of every emission, so that
emissions originating from a common source event can be batched back together.

## The diamond problem

Merge an observable with a derived version of itself:

```ts
const doubled = source.pipe(map((n) => n * 2));
const merged = merge(source, doubled);
```

Every event of `source` now reaches `merged` **twice** — once directly and once
through `map` — as two serial emissions. They are conceptually simultaneous
(they came from the same instant of the same source), but by the time they
reach a subscriber that information is gone: plain rxjs gives you no way to
know that the `5` you just received and the `10` about to arrive belong
together, nor when a "group" starts or ends. Downstream state derived from both
branches passes through an inconsistent intermediate state — the classic
*glitch* of push-based reactive programming, named after the diamond shape of
the dependency graph (one source, two paths, one join).

Further reading:

- [Reactive programming — Glitches](https://en.wikipedia.org/wiki/Reactive_programming#Glitches) (Wikipedia)
- [Rx glitches aren't actually a problem?](https://staltz.com/rx-glitches-arent-actually-a-problem.html) — André Staltz's counterpoint, useful framing for when this *does* matter
- [A Survey on Reactive Programming](https://dl.acm.org/doi/10.1145/2501654.2501666) — Bainomugisha et al., §glitch avoidance

## The idea: provenance + `batchSimultaneous`

An `Instantaneous<A>` is implemented as an `Observable<InstEmit<A>>`, where
every source observable is stamped with a unique **provenance** (a `Symbol()`;
a uuid in practice, for debugging). The usual primitives — `of`, `empty`,
`map`, `take`, `mergeAll`, `concatAll`, `switchAll`, `exhaustAll` — are
reimplemented to preserve provenance through the pipeline.

Alongside the provenance, every protocol node carries a **registration id**
(`sub`): a fresh id minted at each *actual subscription* of a source and
preserved verbatim by every re-statement downstream. Provenance answers
"which source?"; the sub answers "which subscription of it?" — so two live
copies of the same source (a diamond, a re-subscribed inner, a second
`share` ref) are distinguishable, closes name exactly which registration
they end, and a register-and-close lifecycle that lives entirely inside
one delivery pairs with itself instead of eating a sibling's batch slot.

`batchSimultaneous : Instantaneous<A> → Instantaneous<A[]>` then groups
emissions that originate from a common source event:

```ts
import { pipeWith } from "pipe-ts";
import { InstantSubject } from "./v5/constructors";
import { fromInstantaneous, map } from "./v5/basic-primitives";
import { batchSimultaneous } from "./v5/batch-simultaneous";
import { merge } from "./v5/util";

const s = new InstantSubject<number>();
const merged = merge(s, pipeWith(s, map((n) => n * 10)));

pipeWith(merged, batchSimultaneous, fromInstantaneous).subscribe(console.log);

s.next(5); // logs [5, 50]  — one batch, not two emissions
s.next(6); // logs [6, 60]
```

Independent sources stay in separate batches, and a branch that filters an
instant out still releases the batch (`merge(s, s.pipe(filter(isEven)))` logs
`[1]` then `[2, 2]`).

### `batchSync()`

The building block underneath ([typescript/src/batch-sync.ts](typescript/src/batch-sync.ts)).
Subscribing to an observable delivers some emissions *synchronously, during the
subscribe call itself* (e.g. everything `of(1, 2, 3)` will ever emit), and the
rest later. `batchSync()` makes that boundary observable — it collects the
synchronous burst into a single `{ type: "sync", value: A[] }` emission, then
passes every later emission through as `{ type: "async", value: A }`:

```ts
r.merge(of(1), of(2), someSubject)
  .pipe(batchSync())
  .subscribe(console.log);
// { type: "sync", value: [1, 2] }     — everything that fired during subscribe
someSubject.next(3);
// { type: "async", value: 3 }         — one at a time afterwards
```

The joins (`mergeAll` and friends) use it to treat the subscription instant as
one instant: all the `init` emissions of simultaneously subscribed inners are
grouped into a single tree before flowing downstream.

## The semantics, by its edge cases

"Simultaneous" is a **causal** notion here, not a temporal one: two emissions
batch together when they trace back to the same root cause — *not* merely
because they happened in the same synchronous burst of JavaScript. Every
tricky case below falls out of one rule:

> **Every emission belongs to the instant of the value that caused it** —
> transitively: mapped values, spawned inners, subscriptions triggered by an
> async completion, and their sync flushes all inherit. The only *fresh*
> instants are the root causes: **each subject firing** (one `.next()` call =
> one instant — two subjects fired back-to-back are still two instants), and
> **each cold source** at subscription (every `of` is its own instant). A
> cold stream *completing during subscription* is part of the static
> unfolding, not an event — so serial chains stay fragmented.

### Derivation creates simultaneity — sync or async alike

```ts
const wiring = (x) => merge(x, pipeWith(x, mergeMap((n) => of(n * 10))));

wiring(subject);  subject.next(5);   // [5, 50] — inner inherits its trigger
wiring(of(5));                       // [5, 50] — same shape for a cold source
```

The same wiring batches the same way whatever the source. Note the reach of
transitivity: `of(1, 2)` through that wiring gives **one** batch
`[1, 2, 10, 20]` — `10` was caused by `1` and `20` by `2`, but `1` and `2`
already share their `of`'s instant, and inheritance is through the instant.
Independent colds stay apart, though: `merge(of(1), of(2))` is `[1]`, `[2]` —
two root causes, two instants.

How can the machinery tell a `mergeMap`-spawned inner (inherits) from a
`merge`/`concatAll` inner (its own cause), when both arrive as
stream-values of an `of`? By **derivation**: `map` marks its output values
as derived, and a join subscribing a *derived* stream-value knows the
stream was computed from an upstream value — so its flush inherits that
value's instant. A literal stream child is static wiring.

### Nested joins: one async instant, however deep

When one async event delivers *multiple* trigger values (a join over a join,
a diamond used as a join argument), **all** sibling inners inherit it:

```ts
pipeWith(s, mergeMap((n) => of(n, n + 100)), mergeMap((n) => of(n)));
s.next(5);   // [5, 105] — one batch, one instant, arbitrary nesting depth
```

### Completion cascades inherit too

A completion is an async event like any other. When `concatAll` advances its
queue because an inner closed, the next inner's subscription flush belongs to
the closing instant:

```ts
merge(x, concat(pipeWith(x, take(1)), of(7)));
x.next(5);   // [5, 5, 7] — take's last value, its close, and the queued
             // cold's values are one instant
```

(Mechanically: the taking close travels *with* the final value as one
protocol unit, and `concatAll` grafts the next inner's subscription flush
into that unit before it flows downstream — the whole advancement cascade,
chained sync-closing inners included, is one emission. A queue that
advances back onto the *same* source it just took from keeps the source's
registration alive: the close and the re-subscription cancel.)

But a queue that advances through *sync-closing* inners stays fragmented
(subscription-cascade rule): `concat(of(1, 2), of(3))` gives
`[1,2]`, `[3]`.

### Late subscribers: multiplicity grows over time

A subscriber that joins late (a hot `share`d stream re-subscribed by each
trigger of a join, or a hot source queued behind a `concatAll`) sees only
events **strictly after** its subscription instant — so diamonds *grow*:

```ts
// let x = share(src) in merge(x, mergeMap(() => x)(triggers))
triggers.next();  src.next(7);   // [7]     — one subscriber so far
triggers.next();  src.next(8);   // [8, 8]  — two now
```

The strictly-after rule is also what makes **feedback loops**
(`mergeMap(() => x)(x)`, rxjs `expand`-style) well-founded: a
value never triggers a subscription that sees that same value, so
multiplicity grows by exactly one per event — supported and
oracle-verified. One recorded frontier: a trigger derived from the share's
*source* (upstream of the share) races the share's own delivery of the
same event — the spawned subscription is wired first and *does* see the
current value, exactly as plain rxjs behaves, while the model's
strictly-after suffix idealizes it away.

### `take` splits instants

`take(n)` counts values, exactly like rxjs — even mid-batch, even over a
diamond. `take(1)` of a diamond emits one `5`, not the "whole instant"
`[5, 5]`; `take(3)` of a diamond cuts the second instant in half:
`[5, 5]`, `[6]`. The alternative would make `take` aware of a
`batchSimultaneous` applied *later* in the pipeline, which no user would
expect. At the cut, `take` synthesizes protocol closes for every
registration it passed downstream — each carrying the registration id it
ends — traveling with the final value as one unit, so a `concatAll` queued
behind a cut diamond still inherits the closing instant, and window
accounting knows exactly whose delivery slots the cut consumed (this is
what makes cuts correct even across *multiple live copies* of the same
`take`, e.g. one spawned per trigger by a dynamic join).

### The serial joins mirror rxjs — including the subtle cases

- `switchAll` on a synchronous burst of inners subscribes each in turn:
  **every** inner's sync values pass; only the last stays live.
- exhaust drops an arrival only while the previous inner is **still
  active** — `pipeWith(of(1, 2), exhaustMap((n) => of(n * 10)))` emits
  both `10` and `20`, because the first inner completes synchronously and
  frees the slot.
- One thing rxjs never had to care about: unsubscribing a live inner
  (switching away from it) must tell downstream batch accounting that its
  registrations ended. `switchAll` synthesizes protocol closes for the
  switched-away inner, so **diamonds across a switch** batch correctly:

  ```ts
  merge(s, switchAll(of(s, of(1))));   // s registered, switched away, closed
  s.next(5);                           // [5] — single, not stranded
  ```

  (`rxjs-mirror.test.ts` runs the same programs through plain rxjs
  side-by-side to keep the value semantics honest.)

### Async outers: inners that arrive over time

The serial joins also take **asynchronous stream-of-streams outers**
(`concatMap(v => inner)(trigger)`, `switchMap`, `exhaustMap`), and the
causation rule extends to them:

- A `concatMap` arrival while an inner is live **queues**; when the live
  inner ends via an async event, the queued inner subscribes *at the
  closing instant* — the final value, the closes, and the queued inner's
  subscription flush are **one batch**.
- An `exhaustMap` arrival while an inner is live is dropped entirely; a
  `switchMap` arrival switches at its own instant (and a trigger sharing
  the live inner's source silences the inner's same-instant value — the
  trigger chain subscribed first, exactly as in plain rxjs).
- A swallowed arrival (queued or dropped) still **delivers its protocol
  side at the arrival instant** — closes ride along, and the delivery's
  window slot is consumed — so diamonds through a busy serial join never
  strand a batch. Only the payload (the inner's subscription) is deferred
  or discarded.
- Valueless outer emissions (a filtered trigger's empty instant, the
  outer's own completion) are protocol traffic: they forward at their own
  instant and never queue, drop, or switch. In particular `switchAll` now
  mirrors rxjs on completion: the outer completing does **not** kill the
  live inner.

### Batch order is delivery order

Within a batch, values appear **in the order they arrived** — exactly the
order plain rxjs would deliver them (ratified 2026-07-06, replacing an
earlier syntactic-sort design whose position machinery leaked into every
operator). This is still deterministic and rule-governed:

> A source fires its subscribers in **subscription order**. Everything
> wired up statically subscribes in expression order, so for ordinary
> programs the batch reads exactly like the expression:
> `merge(s, map(f)(s))` batches as `[5, f(5)]`. Order only becomes
> sensitive to *subscription timing* where timing genuinely differs.

The consequences, concretely:

- **A `concat` branch that subscribes a hot source *late* delivers last.**
  In `merge(mergeMap(f)(x), concat(take(1)(x), map(g)(x)))`, the concat's
  second branch only subscribes `x` when `take(1)` closes — its
  subscription lands at the *end* of `x`'s subscriber list, so from then
  on its values appear at the **end** of each batch, even though the
  branch reads first inside the concat. (Under the old syntactic sort
  they were re-ordered back to the concat's slot.)
- **A `share`'s fan-out is consecutive.** The share subscribes its source
  once, when its first ref subscribes — so all ref-derived values of an
  instant arrive as one contiguous block at that slot, in ref order:
  `merge(x, s, map(f)(x))` batches as `[x, f(x), s]`, the two refs
  adjacent.
- **A spawned inner's flush arrives inside its trigger's slot** (the
  trigger chain subscribed the source first), and each live copy of an
  inner delivers contiguously, in spawn order.
- **`scan` folds in the same order** — the accumulator threads through a
  diamond's values exactly as they arrive, so the fold always reads as a
  left fold over the batch (see below).

If a specific order matters, make it explicit: tag values before merging
(`map((v) => ["left", v])`) and sort the batch array — local, explicit,
and independent of subscription timing.

### `scan` processes emissions as they come in

`accumulate`/`scan` stays a cheap, provenance-transparent stateful map,
exactly like rxjs `scan` — it never waits for an instant to assemble.
Over a diamond, the accumulator visits the instant's values in delivery
order, which is also the batch's order, so
`scan(0, (a, v) => a + v)(merge(s, map(f)(s)))` on `s.next(5)` batches as
`[5, 5 + f(5)]` — a clean left fold over the displayed batch.

### Out of scope, on purpose

- **Errors** — prefer `Either`-style values; a try/catch boundary at the
  cold/`Subject` constructors may come later.
- **Schedulers & time** — `delay` and friends are `setTimeout` + the
  existing primitives; no formal impact.
- **`shareReplay`, share config** — plain rxjs `share()` semantics only
  (refcounted, reset on refcount zero, registration-only replay for late
  subscribers). One delivery-order corner is outside the verified
  contract: a ref that closes *during the subscription frame* (e.g.
  `take(0)(x)` as the first ref) resets the share mid-unfolding, moving
  its reconnection slot — the oracle's model assumes one hot life.

## Running the checks

From `typescript/`:

```sh
npm test                                  # the full jest suite
npm run typecheck
npm run oracle                            # one run of the property oracle (~500 random programs)
npm run oracle:sweep -- 50                # N oracle runs; prints the counterexample on failure
npm run oracle:replay -- <seed> "<path>"  # replay a recorded fast-check failure
npm run agda                              # typecheck agda/src/Everything.agda
```

## Repository layout

| Path | What |
| --- | --- |
| [typescript/src/v5/](typescript/src/v5/) | The implementation: emission trees, primitives, joins, `batchSimultaneous` |
| [typescript/src/v5/\_\_tests\_\_/](typescript/src/v5/__tests__/) | 93 jest tests: every primitive, every join, the diamond in many shapes, feedback loops, `takeUntil`, `expand`, and side-by-side rxjs comparisons |
| [typescript/src/model/](typescript/src/model/) | A pure *timed-list* model of the same semantics + a deep-embedded expression type, used as a [fast-check](https://fast-check.dev/) oracle: random combinator trees are run through both the rxjs machinery and the model, and must agree |
| [agda/](agda/) | **Formal verification** of `batchSimultaneous` — see [agda/README.md](agda/README.md) for the full approach |

```sh
cd typescript && npm install && npm test   # jest + property-based oracle
cd agda && agda src/Everything.agda        # typecheck the proofs (Agda ≥ 2.6.2, no stdlib needed)
```
