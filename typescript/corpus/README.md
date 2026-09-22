# The oracle's pinned corpus

Programs replayed by `scripts/run-oracle.sh --cases <file>`, alongside the
seeded sweep rather than instead of it. A pinned row is here because a
RANDOM draw is not guaranteed to redraw it: the sweep's yield is thin (see
`src/generator.ts`'s header — most of what it draws emits nothing), and a
shape that decides a design question is not something to re-find by luck.

One serialized `TestCase` per line, which is exactly what a failing case
prints — so a divergence the sweep finds is pinned by copying the line.

`burst-carrier` and `depth-first` pin ONE mechanism between them, which is
worth knowing before reading a green over them. Fourteen of their sixteen rows
read a single shared slot as both a flattener's outer and its inner, and that
is exactly the shape a batching carrier gets wrong: the subscriber set is
re-read between two values of one synchronous emission. Those rows accumulated
one divergence at a time and converged on it without anyone choosing that, so
the two files are a deep sample of a narrow region — a carrier passing all
sixteen has been checked against re-entrant subscription and against almost
nothing else. The two rows that read the shared slot only as an inner are the
exchanged pair below, which is pinned for a different question entirely.

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
on. Eight of the ten agree today; the two that do not fail with the region's
own signature, a strict prefix of what rxjs emits, so they are that bug seen
from here rather than anything this file is about.

Its last five rows are HAND-BUILT, because the draw reaches the region without
reaching its hard half: in every drawn row the fold REPLACES its accumulator,
and in none of them does it plug the accumulator into the observable it
produces. That one shape is what makes a scan cell deepen by a flattener per
folded value, and it is the case a syntactic bound on the store cannot cover —
so a file holding only drawn rows would read as covering the region while
testing the easy half of it. `f (acc , x) = strm (mergeAll (of [ acc , strm
(of [ x ]) ]))` over a three-value source is the whole of the shape; both
carriers agree with rxjs on all five.

`deferred-push` pins ONE mechanism, and it is the consequence of the sentence
`depth-first` ends on: what a subscribe emits has to be pushed where it is
produced. A flattener's inner subscribe answers with a burst at its own
element type, and that burst crosses the path BELOW the flattener later —
once the walk that produced it is over. A share connecting does not wait: its
connect fans out through the chains already registered, and a registered chain
is the whole path, so those values cross that path AT THE SUBSCRIBE. Two
routes, one deferred and one eager; the concatenation that reassembles them
puts the emissions back in the right ORDER, so nothing below can tell — unless
something below is COUNTING.

That is the axis the file's last twenty-four rows are built on, and they are
HAND-BUILT as a matrix rather than a sample: three flatteners (`switchAll`,
`mergeAll`, `exhaustAll`) against two orders (a literal inner before the share
and after it) against four frames sitting between the flattener and the root.
The twelve rows whose frame is `map` all agree; the twelve whose frame is
`take`, `scan` or `batchSync` diverged, every one of them, in both orders and
under all three flatteners, until a subscribe's answer started being folded
down the path AT the subscribe. A frame with no cell cannot see the
difference and a frame with one always does — which is what makes the split a
claim about the mechanism rather than about twelve programs, and what makes
the matrix's green a statement about one mechanism rather than twelve
programs happening to agree.

Whoever reads the matrix's twelve `scan` and `take` rows should know the
binder they turn on, because a hand-built row got it wrong once and read as a
divergence far louder than the one it was pinning. A fold's function binds ONE
variable, the PAIR of accumulator and value — so an arithmetic step is
`add (fst var₀) (snd var₀)`, and a bare `var₀` at the element type is a
program the evaluator is right to refuse. Six rows here carried that shape and
answered with nothing, which is exactly what a real divergence in this region
would look like.

The seventy-seven rows before them are DRAWN, shrunk one at a time from a
sweep of eight hundred thousand generated programs — of which they are every
divergence found. Fifty-six are the matrix's red half met in the wild: a
flattener reading a shared slot, with a `batchSync`, a `take` or a `scan`
between that flattener and the root. What they add is the DENOMINATOR, and a
sweep that size turning up no other shape is what says the region is one
region.

The remaining twenty-one are the reason the matrix is not the whole statement.
They carry a flattener and a counting frame and NO share — the eager side is a
cold slot subscribed twice (whose sync values re-anchor at each subscription),
or a `mu` feeding back, or a second flattener's inner. Read that way they are
one mechanism with the matrix, because a share is not what makes the other
route eager; RE-ENTRY is, and a share is only its most reliable source. That
reading is not itself pinned by anything here, which is why the matrix holds
the share form alone: the twenty-one say the fix cannot be special-cased to
shares, and they do not say more than that.

The matrix is now GREEN and the drawn half is not, and the gap between the
two is the finding this file currently holds. Folding a subscribe's answer at
the subscribe closes the matrix outright — all twenty-four rows, both orders,
all three flatteners — and closes fifty-four of the seventy-seven drawn rows
with it. Of the twenty-three that remain, nineteen carry a mergeAll with a
CONCURRENCY LIMIT, which is the one other place an answer is still collected
and folded after the fact: a queued inner is subscribed when a lane frees, and
that subscribe's own emissions are carried back through the finishing inner's
burst rather than pushed where they were produced. The four that carry no
limit are not explained by that and are not yet explained by anything.

Every remaining divergence has the same SHAPE, which is worth more than the
count: rxjs and the evaluator emit the same multiset, and a value the
evaluator delivers is one the evaluator delivers LATE. So what is left is
the same deferral seen through a second route, not a second defect.

The twelve `map` rows stay CONTROLS whatever the rest of the file does —
they are what says a divergence here is the frame's cell and not the share.
