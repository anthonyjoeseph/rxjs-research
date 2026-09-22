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

`depth-first`'s last two rows are HAND-BUILT and each decides a different
question about a fan-out run at the connect. The NESTED one reads slot 1 as a
plain alias of slot 0 and runs the re-entrant shape over slot 1, so one share's
emission is delivered through another's; rxjs answers it exactly as the
un-nested row, which says a share transposes LOCALLY and no ordering across
nested shares is wanted. It decides a second thing, and that one is a
refutation: its answer drops a value unless a SHARE's fold of each value is
COMPLETE before the next value is read, because that fold is what subscribes
the inner whose chain the next value is delivered to. Collecting a share's
emissions and folding them afterwards cannot produce this row, whatever order
it keeps them in. It says nothing about a FLATTENER's walk, whose inners
arrive in one burst and whose feedback path, if it has one, no row here
reaches. The ORDER one is the mirror of the row above it —
`of[of[7], share]` against `of[share, of[7]]` — and the pair is a refutation
rather than a sample: both carry the same values out of the flattener and the
same values out of the share, and rxjs answers `[7,1,2]` and `[1,2,7]`. So a
subscribe answering with a burst at its own element type PLUS a stream already
at the root cannot be read by any fixed rule, whichever order the two are
concatenated in; what a subscribe emits has to be pushed where it is produced.
Both rows agree under the burst carrier today, and the ORDER row is a guard
rather than a divergence.

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
