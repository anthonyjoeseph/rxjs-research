# `docs/` — one file per tool, and why they are not in CLAUDE.md

CLAUDE.md is the **file of record for directives**: rulings, standing rules, laws.
It is read in full at the start of every session, so every byte in it is paid for
by every worker. These files hold the part that is **not a directive** — how a
tool works, what its flags mean, which trap cost a day, what a measurement
showed. A session reads one of these when it is about to USE the thing.

**The split is by KIND, not by length.** A rule that must be obeyed
prophylactically — before you have any reason to open a doc — stays in CLAUDE.md.
Mechanics, error catalogues, and the evidence behind a rule come here.

**These files are under the same no-dates rule as CLAUDE.md**, enforced by
`make roadmap-check`. A tool doc describes the tool as it is; when it happened is
not a property of the tool. The one file that legitimately carries dates is
`typecheck-performance-numbers.md`, because a timing's age IS information about
the timing — and that is why it is not in the scan.

## Which gate — `make gate` routes

Start at [gate.md](gate.md). **Type `make gate`** — it asks for a free verdict
and takes the light path (the cheap block below, plus a real dev check of the
modules this tree touched) or the heavy one (that block plus the full tower),
printing which and why. The escalation triggers are a touched multi-member
mutual block, a file outside `agda/src`, too many changed modules, or too many
commits of drift since the last heavy run — so the choice is the machine's, not
yours. `gate-light` and `gate-heavy` force a path.

## The cheap block, in order — both paths run all of it

| Target | Doc | What it will not let you do |
| --- | --- | --- |
| `wiring-selftest` | [wiring.md](wiring.md) | ship a wiring checker that has stopped firing |
| `wiring-gate` | [wiring.md](wiring.md) | leave a definition, postulate or module with no route to Main |
| `wiring-refuted` | [wiring.md](wiring.md) | leave a refutation `Refuted.Main` does not claim |
| `wiring-probed` | [evidence.md](evidence.md) | leave a probe `Probed.Main` does not claim |
| `evidence-selftest` | [evidence.md](evidence.md) | ship an evidence checker that has stopped firing |
| `evidence-check` | [evidence.md](evidence.md) | let proof code depend on a probe or a refutation, or keep a probe whose target is discharged |
| `unsafe-check` | [unsafe-check.md](unsafe-check.md) | slip an unsafe pragma onto the proof path |
| `dup-selftest` | [find.md](find.md) | ship a duplicate checker that has stopped firing |
| `dup-check` | [find.md](find.md) | prove the same fact twice under two names |
| `imports-selftest` | [imports-check.md](imports-check.md) | ship an import checker that has stopped firing |
| `imports-check` | [imports-check.md](imports-check.md) | leave an import no name in the file spends, or one that names nothing it takes |
| `roadmap-selftest` | [roadmap-check.md](roadmap-check.md) | ship a roadmap checker that has stopped firing |
| `dev-changed-selftest` | [gate.md](gate.md) | ship a light gate that passes while checking nothing |
| `roadmap-check` | [roadmap-check.md](roadmap-check.md) | leave PROOF-STATE stale, unsorted, verbose, or dated — or date CLAUDE.md |
| `comments-selftest` | [comments-check.md](comments-check.md) | ship a comment checker that has stopped firing |
| `comments-check` | [comments-check.md](comments-check.md) | date a source comment, record what happened to a declaration, bury the evidence mid-paragraph, cite a twin or probe that is not there, or let an explanation grow into an essay |
| `agda` | [agda-build.md](agda-build.md) | land anything that does not typecheck, warnings included |
| `refuted` | [evidence.md](evidence.md) | land a refutation that does not typecheck |
| `probed` | [evidence.md](evidence.md) | land a probe that does not typecheck |
| `bug-cache` | [bug-cache.md](bug-cache.md) | regress a known impl counterexample |

## The rest

| Doc | Subject |
| --- | --- |
| [agda-build.md](agda-build.md) | the `AGDA` variable, `-W error`, and the comment-stripped mirror Agda actually checks |
| [agda-dev.md](agda-dev.md) | `make agda-dev` — the per-member iteration loop |
| [gate.md](gate.md) | `make gate` routing, `gate-light` / `gate-heavy` — the four escalation triggers, and the consumer cone the light path does not reach |
| [bg.md](bg.md) | `make bg` / `bg-check` / `bg-wait` — detaching a build that outlives a tool call |
| [find.md](find.md) | `make find` and `make dup-check` — search by the shape of the STATEMENT |
| [imports-check.md](imports-check.md) | `make imports-check` / `imports-fix` — dead imports, blanket imports, the claim root, the orphan guard, and why an edge costs |
| [harness.md](harness.md) | `make harness` — the compiled calculator, and why its numbers prove nothing |
| [typecheck-cost.md](typecheck-cost.md) | the cost model: what actually makes a module slow, and the `abstract` mandate |
| [agda-traps.md](agda-traps.md) | language and stdlib traps, each of which reports against the wrong thing |
| [evidence.md](evidence.md) | `agda/evidence/` — the library boundary that makes a `src` import of a probe or a refutation unresolvable, and how a probe expires |
