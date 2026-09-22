# The oracle's pinned corpus

Programs replayed by `scripts/run-oracle.sh --cases <file>`, alongside the
seeded sweep rather than instead of it. A pinned row is here because a
RANDOM draw is not guaranteed to redraw it: the sweep's yield is thin (see
`src/generator.ts`'s header — most of what it draws emits nothing), and a
shape that decides a design question is not something to re-find by luck.

One serialized `TestCase` per line, which is exactly what a failing case
prints — so a divergence the sweep finds is pinned by copying the line.

These rows pin ONE mechanism, which is worth knowing before reading a green
over them. Twelve of the fifteen read a single shared slot as both a
flattener's outer and its inner, and that is exactly the shape a batching
carrier gets wrong: the subscriber set is re-read between two values of one
synchronous emission. Rows accumulated one divergence at a time and converged
on it without anyone choosing that, so the file is a deep sample of a narrow
region rather than a spread — a carrier passing all fifteen has been checked
against re-entrant subscription and against almost nothing else.
