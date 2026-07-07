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
every emission carries **provenance**: which root cause (which instant) it
traces back to. The usual primitives — `of`, `empty`, `map`, `take`, `share`,
`scan`, `mergeAll`, `concatAll`, `switchAll`, `exhaustAll` — are reimplemented
to preserve provenance through the pipeline, and
`batchSimultaneous : Instantaneous<A> → Instantaneous<A[]>` groups emissions
that share a root cause:

```ts
const s = new InstantSubject<number>();
const tenfold = s.pipe(map((n) => n * 10));

merge(s, tenfold)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

s.next(5); // logs [5, 50]  — one batch, not two emissions
s.next(6); // logs [6, 60]
```

Independent events stay in separate batches, and a branch that filters an
instant out still releases the batch (a filtered diamond logs `[1]` for the
odd value, `[2, 2]` for the even one).

> **Spec status.** The semantics below — *burst batching* — was ratified in
> July 2026 and is machine-checked in [agda/](agda/): the timed denotation
> in [Burst.agda](agda/v1/src/Burst.agda), the clockless counting machine in
> [Protocol.agda](agda/v1/src/Protocol.agda). The Agda development is the
> design authority; the TypeScript implementation is validated against a
> line-by-line transcription of it by a property-based oracle.

### The counting machine

How can `batchSimultaneous` know a batch is over, without time travel? Two
mechanisms, one per kind of root cause
([typescript/src/batch-simultaneous.ts](typescript/src/batch-simultaneous.ts)):

- **The subscription frame** is bounded by the subscribe call itself:
  everything delivered synchronously during subscribe is one batch.
- **After the frame, it counts.** Every emission carries the provenance of
  the root that caused it, and the protocol carries registration events
  (`init`/`close`) alongside values — so the machine always knows how many
  live subscription chains each root has. When an instant's first emission
  arrives, the machine knows exactly how many more it is owed, and flushes
  when the count drains. No clock, no scheduler tricks — this is the
  mechanism proven correct in [Protocol.agda](agda/v1/src/Protocol.agda)'s
  `endgame` theorem.

## The semantics: burst batching

"Simultaneous" is a **causal** notion, not a temporal one. The whole
semantics is one rule:

> **Every emission belongs to the instant of the event that caused it**,
> transitively — mapped values, spawned inner subscriptions, completion
> cascades all inherit their trigger's instant. The only *fresh* instants
> are the root causes, and there are exactly two kinds: **one `subscribe()`
> call** (the entire synchronous subscription frame is one instant) and
> **one `.next()` call** (each subject firing is its own instant, even
> back-to-back).

Everything below is that rule playing out.

### One `subscribe()` call is one batch

```ts
const now = of(1, 2);
const alsoNow = of(3);
const later = timer(100); // emits 0 after 100 ms

merge(now, alsoNow, later)
  .pipe(batchSimultaneous())
  .subscribe(console.log);
// logs [1, 2, 3] — immediately: the whole subscription frame is one instant
// logs [0]       — 100 ms later: an async event is its own instant
```

Everything that fires synchronously *during* the subscribe call shares one
root cause: the subscribe call itself. It doesn't matter how the sync values
are wired — separate `of`s, `concat(of(1, 2), of(3))`, nested merges — a
static (subject-free) program lands entirely in one batch. Anything that
arrives after the frame ends is caused by some later event and batches with
*that*.

### Each `.next()` call is its own instant

```ts
const a = new InstantSubject<number>();
const b = new InstantSubject<number>();
const doubled = a.pipe(map((n) => n * 2));

merge(a, doubled, b)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

a.next(5); // logs [5, 10] — the diamond: both copies of a's event, one batch
b.next(7); // logs [7]     — a different subject is a different root cause
a.next(6); // logs [6, 12]
```

A `.next()` call is a fresh root cause. Two subjects fired back-to-back in
the same JavaScript tick are still two instants — batching follows causation,
not wall-clock adjacency. (A `.next()` called reentrantly, from inside a
subscriber callback, is likewise a fresh instant, strictly after the batch it
reacts to — feedback never extends the instant it's reacting to.)

### Cascades inherit their trigger's instant

```ts
const s = new InstantSubject<number>();
const spawned = s.pipe(mergeMap((n) => of(n * 10, n * 10 + 1)));

merge(s, spawned)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

s.next(5); // logs [5, 50, 51] — the spawned inner's values batch with their cause
```

When an event spawns an inner subscription (`mergeMap`, `concatMap`, …), the
inner's synchronous output was *caused by* that event, so it joins the
event's batch — transitively, through any nesting depth.

### Completion cascades inherit too

```ts
const s = new InstantSubject<number>();
const firstOnly = s.pipe(take(1));
const thenSeven = concat(firstOnly, of(7));

merge(s, thenSeven)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

s.next(5); // logs [5, 5, 7] — take(1) closes on this event, so the queued
           //                  of(7) subscribes at the same instant
s.next(6); // logs [6]
```

A completion is an event like any other. When `concat` advances its queue
because an inner closed, the next inner's subscription flush belongs to the
closing instant — the final value, the close, and the freshly subscribed
values are one batch.

### `share`: connect at first subscription, no replay

```ts
const shared = of(5).pipe(share());

merge(shared, shared)
  .pipe(batchSimultaneous())
  .subscribe(console.log);
// logs [5] — once, not twice
```

A `share` subscribes its source exactly once: when its **first** subscriber
arrives. That first subscriber triggers the connection and receives the
source's synchronous values; the second subscriber arrives a moment later,
after those values already fired, and a hot stream does not replay — so it
gets nothing. (Contrast the unshared diamond above, where each branch got its
own copy of the source.)

### Late subscribers see only later events — diamonds grow

```ts
const src = new InstantSubject<number>();
const shared = src.pipe(share());
const trigger = new InstantSubject<void>();

// each trigger event adds one more live subscription of `shared`
const growing = trigger.pipe(mergeMap(() => shared));

merge(shared, growing)
  .pipe(batchSimultaneous())
  .subscribe(console.log);

trigger.next();
src.next(7);    // logs [7, 7]    — the static subscription plus one spawned
trigger.next();
src.next(8);    // logs [8, 8, 8] — a third subscriber now
```

A subscriber that joins a hot stream late sees only events **strictly after**
its subscription instant. So multiplicity grows over time, one copy per
spawned subscription. The strictly-after rule is also what makes feedback
loops (`shared.pipe(mergeMap(() => shared))`, rxjs-`expand`-style)
well-founded: an event never triggers a subscription that sees that same
event, so each event adds exactly one subscriber.

### `take` counts values, even mid-batch

```ts
const s = new InstantSubject<number>();
const doubled = s.pipe(map((n) => n * 2));
const firstThree = merge(s, doubled).pipe(take(3));

firstThree
  .pipe(batchSimultaneous())
  .subscribe(console.log);

s.next(5); // logs [5, 10]
s.next(6); // logs [6] — take(3) cuts the second batch in half
```

`take(n)` counts values, exactly like rxjs — even across a diamond.
`take(1)` of a diamond emits one `5`, not the "whole instant" `[5, 5]`. The
alternative would make `take` aware of a `batchSimultaneous` applied *later*
in the pipeline, which no user would expect.

### Batch order is delivery order

```ts
const src = new InstantSubject<number>();
const shared = src.pipe(share());
const doubled = shared.pipe(map((n) => n * 2));
const sums = merge(shared, doubled).pipe(scan((acc, n) => acc + n, 0));

sums
  .pipe(batchSimultaneous())
  .subscribe(console.log);

src.next(5); // logs [5, 15]  — the accumulator sees 5, then 10, in delivery order
src.next(1); // logs [16, 18]
```

Within a batch, values appear **in the order plain rxjs delivers them**: a
source fires its subscribers in subscription order, and statically wired
branches subscribe in expression order — so for ordinary programs the batch
reads exactly like the expression. A `share`'s subscribers fire consecutively
as one block, and a spawned inner delivers inside its trigger's slot. `scan`
folds in this same order (it stays a cheap stateful map that never waits for
a batch to assemble), so the fold always reads as a left fold over the
displayed batch. If a specific order matters to you, make it explicit: tag
values before merging (`map((v) => ["left", v] as const)`) and sort the batch
array.

### The serial joins mirror rxjs

```ts
const burst = of(1, 2);
const exhausted = burst.pipe(exhaustMap((n) => of(n * 10)));

exhausted
  .pipe(batchSimultaneous())
  .subscribe(console.log);
// logs [10, 20] — one batch (one subscription frame), and BOTH inners ran:
// a synchronous inner completes immediately, freeing the slot before 2 arrives
```

`switchMap`, `concatMap` and `exhaustMap` keep their rxjs value semantics,
including the subtle cases: `exhaustMap` only drops an arrival while the
previous inner is still open; `switchMap` on a synchronous burst runs every
inner's sync values and keeps only the last one live; the outer completing
does not kill a live inner. The one thing rxjs never had to care about —
telling downstream batch accounting that a switched-away or cut inner's
registrations ended, so no batch waits forever on a dead branch — is handled
by the protocol.

### Out of scope, on purpose

- **Errors** — prefer `Either`-style values; a try/catch boundary at the
  cold/`Subject` constructors may come later.
- **Schedulers & time** — `delay` and friends are `setTimeout` + the
  existing primitives; no formal impact.
- **`shareReplay`, share config** — plain `share()` only, with its default
  rxjs *lives*: the share resets when its source completes or its refcount
  drains to zero, and a later subscriber reconnects and replays a cold
  source (derived in [Protocol.agda](agda/v1/src/Protocol.agda):
  `shareLives`, `cold-share-lives`, `reset-replay`).
- **One known open corner (the upstream race)** — a subscriber of a share
  spawned by a trigger derived from the share's *own source*, wired before
  the share connects, receives the in-flight value in real rxjs while the
  spec's strictly-after rule says it misses it. Pinned in the test suite;
  resolution pending.

## Running the checks

From `typescript/`:

```sh
npm test           # the full jest suite (pinned Agda-theorem cases + the oracle)
npm run typecheck
npm run oracle     # one run of the property oracle (500 random programs)
npm run agda       # typecheck agda/src/Formal-Verification.agda (+ the v1 tower)
```

## Repository layout

| Path | What |
| --- | --- |
| [typescript/src/types.ts](typescript/src/types.ts) | The protocol: `InstEmit`, `Instantaneous`, the `init`/`value`/`close`/`fin` events |
| [typescript/src/primitives.ts](typescript/src/primitives.ts) | The canonical primitives — `of`, `empty`, `map`, `take`, `scan`, `share`, and the four `*All` joins over streams-of-streams; `merge`/`concat`/`mergeMap` are derived one-liners |
| [typescript/src/batch-simultaneous.ts](typescript/src/batch-simultaneous.ts) | The counting machine (the Agda `Protocol.machine`, transcribed) |
| [typescript/src/model.ts](typescript/src/model.ts) | The pure timed-list model — a line-by-line transcription of [Burst.agda](agda/v1/src/Burst.agda) |
| [typescript/src/\_\_tests\_\_/](typescript/src/__tests__/) | Pinned Agda-theorem cases + the [fast-check](https://fast-check.dev/) oracle: random combinator trees run through both the rxjs machinery and the model, compared exactly |
| [agda/](agda/) | **The design authority** — the ratified spec and proofs; see [agda/README.md](agda/README.md) |

```sh
cd typescript && npm install && npm test   # jest + property-based oracle
cd agda && agda src/Formal-Verification.agda # typecheck the proofs (Agda ≥ 2.6.2, no stdlib needed)
```
