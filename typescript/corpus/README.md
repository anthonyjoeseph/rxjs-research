# The oracle's pinned corpus

Programs replayed by `scripts/run-oracle.sh --cases <file>`, alongside the
seeded sweep rather than instead of it. A pinned row is here because a
RANDOM draw is not guaranteed to redraw it: the sweep's yield is thin (see
`src/generator.ts`'s header — most of what it draws emits nothing), and a
shape that decides a design question is not something to re-find by luck.

One serialized `TestCase` per line, which is exactly what a failing case
prints — so a divergence the sweep finds is pinned by copying the line.
