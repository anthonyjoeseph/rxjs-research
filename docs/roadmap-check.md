# `make roadmap-check` — the gate on PROOF-STATE.md (and CLAUDE.md's dates)

`make gate` is necessary, not sufficient: the roadmap is the file every session reads
FIRST, so a stale row misdirects the next session's whole leg. One already did, naming
two postulates that had become real definitions. This target makes the parts a machine
can see into build failures.

## Four checks

1. **Sort** — each tier is ordered riskiest-class-first (FALSITY, SHAPE, VACUITY,
   DIFFICULTY, GRINDABLE). Priority that lives only in prose gets spent on whatever is
   nearest.
2. **Coverage** — every live postulate in `agda/src` is named by some row. A branch of
   the proof cannot hide from the roadmap.
3. **Row budget** — each row's PROSE is within `ROW_BUDGET` characters (names are
   free). Research belongs in the postulate's own source header, where it sits in front
   of the next person to pick the row up; a roadmap row is a hook.
4. **No calendar dates** — anywhere in PROOF-STATE.md, and anywhere in the files listed
   in `DATE_ONLY_FILES` (CLAUDE.md and `docs/*.md`), which get this check only.

## Why the date check covers two kinds of file

The reasons are neighbouring, not identical: **PROOF-STATE must be CURRENT; CLAUDE.md
and the docs must be TIMELESS.** A ruling in the file of record is in force whatever
its age, which is what "file of record" means; and a tool doc describes the tool as it
is.

It is the half a machine can see with no judgement, and **it catches most of the rest
by proxy**: history arrives WITH a timestamp attached, because the writer knows the
reader will want to know when.

The one file that legitimately carries dates is `typecheck-performance-numbers.md`,
because a timing's age IS information about the timing. Source headers keep them too —
a `-- PROBED` or `-- DEAD ROUTE` receipt is only as good as the code being unmoved
since, so its age is a signal about the evidence.

## `make roadmap-selftest`

Also in the gate. It pins every check against fixtures under
`scripts/roadmap-selftest/`, including a **rowless** rules-file fixture — so the date
scan is proven to fire on a file the row parser cannot read, which is exactly
CLAUDE.md's shape.

## The hygiene rules a machine cannot check

They live in PROOF-STATE.md's own header and are also part of the gate, by review: one
line per item (name + risk class + hook), NO numbering of any kind (list indices,
conjunct positions, source sections, timings), research in source headers rather than
here, completed items DELETED rather than marked done, no dated narrative. Re-read that
header when you touch the file; every one of those rules exists because it was
violated.
