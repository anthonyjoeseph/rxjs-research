# `docs/` — one file per tool, and why they are not in CLAUDE.md

CLAUDE.md is the **file of record for directives**: rulings, standing rules, laws.
It is read in full at the start of every session, so every byte in it is paid for
by every worker. These files hold the part that is **not a directive** — how a
tool works, what its flags mean, which trap cost a day. A session reads one of
these when it is about to USE the thing.

**The split is by KIND, not by length.** A rule that must be obeyed
prophylactically stays in CLAUDE.md. Mechanics, error catalogues, and the
evidence behind a rule come here.

**These files are under the same no-dates rule as CLAUDE.md**, enforced by
`make roadmap-check`.

## `make gate` — the cheap block, in order, then `make agda`

| Target | Doc | What it will not let you do |
| --- | --- | --- |
| `wiring-selftest` | [wiring.md](wiring.md) | ship a wiring checker that has stopped firing |
| `wiring-gate` | [wiring.md](wiring.md) | leave a definition, postulate or module with no route to Main |
| `unsafe-check` | [unsafe-check.md](unsafe-check.md) | slip an unsafe pragma onto the proof path |
| `dup-selftest` | [find.md](find.md) | ship a duplicate checker that has stopped firing |
| `dup-check` | [find.md](find.md) | prove the same fact twice under two names |
| `imports-selftest` | [imports-check.md](imports-check.md) | ship an import checker that has stopped firing |
| `imports-check` | [imports-check.md](imports-check.md) | leave an import no name in the file spends, or one that names nothing it takes |
| `roadmap-selftest` | [roadmap-check.md](roadmap-check.md) | ship a roadmap checker that has stopped firing |
| `roadmap-check` | [roadmap-check.md](roadmap-check.md) | leave a postulate out of PROOF-STATE's groups, overrun a budget, or date PROOF-STATE, CLAUDE.md or docs |
| `comments-selftest` | [comments-check.md](comments-check.md) | ship a comment checker that has stopped firing |
| `comments-check` | [comments-check.md](comments-check.md) | date a source comment, record what happened to a declaration, bury the evidence mid-paragraph, cite a twin that is not there |
| `ts-gate` | — | land TypeScript that does not typecheck or lint |
| `agda` | [agda-build.md](agda-build.md) | land anything that does not typecheck from Main, warnings included |

Beside the gate, in its own CI job: `bug-cache` — [bug-cache.md](bug-cache.md).

## The rest

| Doc | Subject |
| --- | --- |
| [agda-build.md](agda-build.md) | the `AGDA` variable, `-W error`, the GHC backend's own failures |
| [bg.md](bg.md) | `make bg` / `bg-check` / `bg-wait` — detaching a build that outlives a tool call |
| [find.md](find.md) | `make find` and `make dup-check` — search by the shape of the STATEMENT |
| [find-prose.md](find-prose.md) | `make find-prose` — search FINDINGS: dead routes, rulings, traps |
| [imports-check.md](imports-check.md) | `make imports-check` / `imports-fix` — dead imports, blanket imports, the claim root, the orphan guard |
| [agda-traps.md](agda-traps.md) | language and stdlib traps, each of which reports against the wrong thing |
| [delegation.md](delegation.md) | worker model pinning and directives |
| [split.md](split.md) | `make split` — cut a long module into parts and retarget its consumers |
| [notify.md](notify.md) | `make notify` — the ntfy.sh push a gate sends on the way out |
