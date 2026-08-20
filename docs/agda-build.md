# The build: the `AGDA` variable, `-W error`, and the mirror

## `make agda` is the merge gate

It takes many minutes; the Bash tool's ceiling is 600 s per foreground call, so it
must be detached — see [bg.md](bg.md). Iterate with
[`make agda-dev`](agda-dev.md) and reach for the long build only to merge.
Current timings: `typecheck-performance-numbers.md`.

## A WARNING IS A BUILD FAILURE

Every Agda invocation goes through the Makefile's `AGDA` variable, which carries
`-W error`; Agda exits 42 on a warning. Never call bare `agda` in the Makefile —
`grep -E '&& agda '` must stay empty.

**Rationale.** A warning that costs nothing gets ignored. A `RewritesNothing` — a
`rewrite` step doing literally nothing — rode *every single build for weeks*,
printed twice per run, and nobody stopped, because green was green. Warnings are
cheap to fix at the moment they appear and invisible forever after.

`DeprecationWarning` is deliberately included (Anthony): when the stdlib bumps,
the gate stays red until every call site is migrated, rather than filtered.

- **The flag must be IDENTICAL in the Makefile and in `scripts/agda-dev.py`'s
  `agda_flags()`. Change one, change both, in the SAME commit.** Agda records the
  warning mode in an interface's validity key, so a target running a different
  `-W` than the dev loop invalidates the whole cone on **every alternation** —
  measured at ~120 modules rebuilt per switch, the cost landing on whatever module
  came next, with each tool blaming the other's module. Every target that checks or
  compiles Agda shares the one interface cache, and the single `AGDA` variable
  exists so they cannot drift. `grep AGDA Makefile` is the list, and it is longer
  than you remember.
- **Changing it costs one full cold rebuild**, since it invalidates every
  interface. Budget for that before touching it, and never toggle it to quiet
  output.
- **Do NOT silence a warning to get green.** Fix the cause. If a warning is
  genuinely wrong, that is a finding worth reporting, not a filter.

## Agda never checks `agda/src`

It checks `agda/_stripped-comments/`, **and that is why a comment edit is free.**
`scripts/strip-comments.py` mirrors `src` + `refuted` with every FULL-LINE `--`
comment DELETED, so a comment-only edit leaves the mirror byte-identical and Agda
rebuilds NOTHING.

Why it exists: 29% of this tree is comment lines, and the campaign's rules
*require* writing findings into headers (`-- PROBED`, `-- DEAD ROUTE`), so before
the mirror every such line cost a full cone rebuild. Measured with the control run
FIRST: a real definition appended to `Rx/Prim` rechecks its dependents; three
comment lines inserted into the same module recheck **zero**.

- **NEVER run `agda` against `agda/src` directly.** That builds a SECOND interface
  cache, and every alternation between the two invalidates the other's cone — the
  same thrash the single `AGDA` variable prevents for `-W`, and for the same
  reason. All six call sites and `agda-dev` go through the mirror; `stripped` is a
  prerequisite of every one of them and costs ~50 ms.
- **Positions are mapped back to `src/` by `scripts/unmap-positions.py`**, off a
  sidecar `.linemap.json`. The map is only valid for the source that produced it —
  which is why the strip is a hard prerequisite rather than a convenience, and why
  a hand-rolled `agda` invocation reports positions against a stale map.
- **`agda-dev` generates INTO the mirror (`_stripped-comments/_dev/`) and runs with
  the mirror as its cwd.** Do not "tidy" it back to `agda/_dev`: Agda finds a
  project by walking UP from the file it is checking, so a dev module there lands
  on `agda/rxjs-research.agda-lib`, whose `include: src` puts the REAL sources on
  the path beside the mirrored ones — every module name then matches two files and
  Agda dies with `AmbiguousTopLevelModuleName` before checking anything. Generating
  inside the mirror stops that walk at the mirror's own `.agda-lib`, and as a bonus
  gives the dev loop and the gate ONE `_build`. Consequently the stripper's orphan
  sweep walks only `src` and `refuted`, never the mirror wholesale — a wholesale
  sweep would delete `_dev` on every run, which is every run.
- **The map cannot live inside the mirror.** A `-- source line N` marker in the
  stripped files would itself change whenever a comment is added above it, making
  the mirror maximally sensitive to exactly the edits it exists to absorb. Anything
  Agda hashes is off limits for this datum.

### Why the stripper is safe

This is the whole question, since a wrong strip typechecks a DIFFERENT program and
reports green.

- It only touches lines whose first non-whitespace run is the dashes, so the `--`
  is unambiguously at a token start and `x--y` can never match.
- It applies Agda's actual rule: dashes then end-of-line or a NON-symbol character,
  so `-->` and `--|` are operators.
- It copies VERBATIM any file containing a non-pragma `{-`, which retires the
  block-comment and string-literal questions entirely at a cost of two files.
- Agda has no multi-line string literal, which is what makes a line-local rule
  sound.
- The invariant asserted on every file on every run is `output[i] ==
  source[kept[i]]`, so a bug can only DROP a line — and a dropped code line is a
  parse error, which is loud.

**`make strip-selftest`** pins the lexical traps and the property that matters:
inserting a comment line does not change the stripped output.

## `--safe` is the finish-line certificate, not today's flag

`make agda` runs a plain `agda src/Main.agda`, and a live `{-# TERMINATING #-}`
already sits in the QuickCheck module, off the proof path. `--safe` cannot be
enabled today — it rejects `postulate`, and we have dozens by design. But it IS
the certificate: the day `The-Proof.agda` is discharged, `agda --safe src/Main.agda`
verifies "no postulates AND no unsafe pragma" in one command. Until then the
policing is by grep — see [unsafe-check.md](unsafe-check.md). Changing a flag
invalidates interfaces; it is not a free query.

## Invocation hygiene

- **Pin the working directory in every build command** — `cd agda/` for a raw
  `agda`, repo root for `make` — and guard with `ls Makefile &&` so a mis-resolved
  path aborts instead of looking green. The tell that agda never started:
  `Total 0ms`, or no `Checking <Module>` line. Never pipe agda through `head`; it
  hides OOM kills.
- **`touch` does NOT dirty a module — invalidation is by CONTENT.** Unchanged
  content reuses the interface, so you cannot force a remeasurement without a real
  edit, and re-appending an IDENTICAL marker line measures nothing.
