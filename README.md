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

## Repository layout

| Path | What |
| --- | --- |
| [typescript/src/v5/](typescript/src/v5/) | The implementation: emission trees, primitives, joins, `batchSimultaneous` |
| [typescript/src/v5/\_\_tests\_\_/](typescript/src/v5/__tests__/) | 50 jest tests: every primitive, every join, and the diamond in many shapes |
| [typescript/src/model/](typescript/src/model/) | A pure *timed-list* model of the same semantics + a deep-embedded expression type, used as a [fast-check](https://fast-check.dev/) oracle: random combinator trees are run through both the rxjs machinery and the model, and must agree |
| [agda/](agda/) | **Formal verification** of `batchSimultaneous` — see [agda/README.md](agda/README.md) for the full approach |

```sh
cd typescript && npm install && npm test   # jest + property-based oracle
cd agda && agda src/Everything.agda        # typecheck the proofs (Agda ≥ 2.6.2, no stdlib needed)
```
