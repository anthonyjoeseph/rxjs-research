# The oracle's pinned corpus

Programs replayed by `scripts/run-oracle.sh --cases <file>`, alongside the
seeded sweep rather than instead of it. A pinned row is here because a
RANDOM draw is not guaranteed to redraw it: the sweep's yield is thin (see
`src/generator.ts`'s header — most of what it draws emits nothing), and a
shape that decides a design question is not something to re-find by luck.

One serialized `TestCase` per line, which is exactly what a failing case
prints — so a divergence the sweep finds is pinned by copying the line.

`burst-carrier` and `depth-first` pin ONE mechanism between them, which is
worth knowing before reading a green over them. Twelve of their fifteen rows
read a single shared slot as both a flattener's outer and its inner, and that
is exactly the shape a batching carrier gets wrong: the subscriber set is
re-read between two values of one synchronous emission. Those rows accumulated
one divergence at a time and converged on it without anyone choosing that, so
the two files are a deep sample of a narrow region — a carrier passing all
fifteen has been checked against re-entrant subscription and against almost
nothing else.

`obs-accumulator` is the other kind of file: pinned by SEARCH rather than by
divergence, because the region it holds is the one the proof's store obligation
is about and the draw barely reaches it. A fold whose accumulator type contains
an observable is what makes a scan cell's contents something a reducibility
argument has to carry; ten of the draw's four hundred emitting programs have
one, so a green sweep is thin evidence there and a redraw is not to be relied
on. Nine of the ten agree under both carriers and are here to stay agreeing.

Its last five rows are HAND-BUILT, because the draw reaches the region without
reaching its hard half: in every drawn row the fold REPLACES its accumulator,
and in none of them does it plug the accumulator into the observable it
produces. That one shape is what makes a scan cell deepen by a flattener per
folded value, and it is the case a syntactic bound on the store cannot cover —
so a file holding only drawn rows would read as covering the region while
testing the easy half of it. `f (acc , x) = strm (mergeAll (of [ acc , strm
(of [ x ]) ]))` over a three-value source is the whole of the shape; both
carriers agree with rxjs on all five.
