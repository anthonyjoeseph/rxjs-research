# The build: `make agda`, the `AGDA` variable, `-W error`

## `make agda` checks `agda-impl/Main.agda`

`cd agda-impl && $(AGDA) Main.agda`. Main's imports ARE the build's coverage:
anything Main does not reach is not checked. `make gate` runs it after the cheap
block. A cold check of the whole tree is short, but detach it anyway when
unsure — see [bg.md](bg.md).

## A WARNING IS A BUILD FAILURE

Every Agda invocation goes through the Makefile's `AGDA` variable, which carries
`-W error`; Agda exits 42 on a warning. Never call bare `agda` in the Makefile —
`grep -E '&& agda '` must stay empty.

**Rationale.** A warning that costs nothing gets ignored. A `RewritesNothing` — a
`rewrite` step doing literally nothing — rode every build for weeks, printed twice
per run, and nobody stopped, because green was green.

`DeprecationWarning` is deliberately included (Anthony): when the stdlib bumps,
the gate stays red until every call site is migrated, rather than filtered.

- **Every target that checks or compiles Agda shares one interface cache**, and
  Agda records the warning mode in an interface's validity key — a target running
  a different `-W` invalidates the whole tree on every alternation. The single
  `AGDA` variable exists so they cannot drift. `grep AGDA Makefile` is the list.
- **Do NOT silence a warning to get green.** Fix the cause. A warning you believe
  is wrong is a finding.

## The GHC backend has its own failures

`make bug-cache` compiles through MAlonzo and GHC (`-Werror`). A module can
typecheck and still fail there — e.g. a record with one runtime field compiles to
a `newtype`, and GHC rejects one whose field mentions `IO` bare. A postulate with
no `COMPILE` pragma compiles fine and fails only when the binary forces it.

## A DELETED MODULE'S INTERFACE CAN CRASH THE BUILD

Delete a module and its `.agdai` is orphaned at `_build/<ver>/agda/<rel>.agdai`
(not beside the source). Agda may die with an `__IMPOSSIBLE__` internal error
naming the last module it checked SUCCESSFULLY and nothing about the orphan, so
the symptom points at healthy code. Repair: delete `agda-impl/_build`.

## `--safe` is the finish-line certificate, not today's flag

`--safe` rejects `postulate`, and the tree has them by design. The day the
ledger is empty, `agda --safe Main.agda` certifies "no postulates AND no unsafe
pragma" in one command. Until then the policing is by grep — see
[unsafe-check.md](unsafe-check.md).

## Invocation hygiene

- **Pin the working directory in every build command** and guard with
  `ls Makefile &&`. The tell that agda never started: no `Checking <Module>` line.
  Never pipe a build: a pipeline exits with the LAST command's status.
- **`touch` does NOT dirty a module — invalidation is by CONTENT.**
