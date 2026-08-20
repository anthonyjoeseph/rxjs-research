# The cost model — what actually makes a module slow

**All measured timings live in `typecheck-performance-numbers.md`, and nowhere else.**
That includes the gate's cost, per-module costs, the pass attribution, the split
before/afters and every closed experiment. Numbers age far faster than rules, so
quoting one here would mean maintaining it in two places and getting it wrong in both.
`make agda` and `make agda-dev` append their own timings to that file, so it stays
current on its own — read it before re-opening any performance question, and re-measure
before acting on it.

## Mutual-BLOCK membership is everything; file size is nearly irrelevant

Most of the gate is Agda's occurrence/polarity (`Positivity`) pass, it runs over a
whole mutual block, and it **cannot be switched off** — every route was measured and
closed. TERM SIZE drives it, not member count.

Before proposing any split: run `make agda-dev ARGS='--list <file>'` (free) to see
which members are in a genuine cycle, then MEASURE on a coherent cache — **a rebuilding
dependency masquerades as module cost and has produced four phantom "slow module"
diagnoses, each off by up to ~50×.** Attribute whole-module passes with
`--profile=internal` on a genuinely dirty module; `--profile=definitions` files them
under "Miscellaneous".

**The splits are DONE and the question is CLOSED:** Caps-Face and Wet are both split,
and Wet/Part2's remaining block is irreducible.

## But run `--list` before believing any of the above

A module with no mutual block cannot be paying for one. Positivity needs a block; when
`--list` says `0 multi-member`, that whole story is ruled out for free and the cost is
somewhere else.

The measured somewhere-else is **`Typing.With`**. `with` and `rewrite` abstract their
scrutinee out of the GOAL whether or not the clause needs case analysis, so a `with`
that merely destructures a Σ is pure loss, and it is charged in proportion to the goal's
term size. That makes a body whose goal is a **fully-applied closed term** (a top-line
theorem over `evaluate …`, not over variables) the expensive place to write one, and a
**short, non-recursive, slow** definition the tell. Prefer irrefutable `let` patterns
and `subst` there. The worked case, the profile that found it, and the sweep that found
no second instance: `typecheck-performance-numbers.md`.

## Module granularity: keep typechecks short

- **Cut at mutual-SCC boundaries.** A mutual block is an indivisible checking unit and
  cannot span modules; everything else can and should. A module holds at most one
  heavyweight SCC and as little else as possible. **Never restructure genuine
  mutuality** (indirection layers, WF recursion) just to shrink a module — proof shape
  wins over check time.
- **A new lemma family not mutual with an existing SCC gets its own module**, even when
  it is "about" that SCC — consuming another family's results as finished facts is an
  import, not mutuality. `open import X public` chains keep the namespace flat, so
  consumers never notice where a lemma physically lives.
- **Target ≤20 s solo recheck for every non-SCC module**; past that, split at the next
  natural seam. SCC modules pay their SCC's price, which is irreducible in a real check —
  so keep it from being paid per-mistake: iterate with `agda-dev`, land bodies in
  verified batches, and detach the big recheck while writing the next batch.

## Parallelism ceiling

This machine has **24 GB RAM and 14 cores**, ~12 GB free at rest, and a single
heavyweight check peaks in the multi-GB range.

- **At most TWO heavyweight checks at once** (the Subscribe-Face / Wet class). Two fit
  the headroom; three do not, and an OOM costs more than the wait. Re-measure with
  `ps -eo rss` before assuming otherwise.
- **Cheap modules parallelize freely** — non-SCC modules solo-check in seconds and cost
  well under a GB.
- The dev loop and the gate share ONE interface cache, so they must not run
  concurrently — see [agda-dev.md](agda-dev.md).

## A proof body on the `budget-sufficient` spine MUST be sealed (`abstract`)

Or VWF dies. Three OOMs (`Killed: 9`, tens of GB and tens of minutes) came from turning
a postulate on this spine into a real definition whose unfoldable body reached the
`opIterD-dominated` / `lvls-mono` towers; sealed, VWF checks in about a minute at a
fraction of the memory.

**Whenever a postulate consumed transitively by `budget-sufficient` becomes a
definition, seal it in the SAME edit** — no consumer ever needs more than the type.

A plain `abstract` block rejects untyped `where`-bindings and with-abstractions, so
those bodies use private-impl + abstract-alias: `private f-go : T; f-go = …` then
`abstract f : T; f = f-go`.
