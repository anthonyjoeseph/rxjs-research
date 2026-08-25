# `make roadmap-check` — the gate on PROOF-STATE.md (and CLAUDE.md's dates)

`make gate` is necessary, not sufficient: the roadmap is the file every session reads
FIRST, so a stale row misdirects the next session's whole leg. One already did, naming
two postulates that had become real definitions. This target makes the parts a machine
can see into build failures.

## Eight checks

1. **Sort** — each tier is ordered riskiest-class-first (FALSITY, SHAPE, VACUITY,
   DIFFICULTY, GRINDABLE). Priority that lives only in prose gets spent on whatever is
   nearest.
2. **Coverage** — every live postulate in `agda/src` is named by some row. A branch of
   the proof cannot hide from the roadmap.
3. **Staleness** — coverage run BACKWARDS: no row head names a postulate that is no
   longer live. This is the direction that has actually bitten — the two rows in the
   paragraph above.
4. **Row budget** — each row's PROSE is within `ROW_BUDGET` characters (names are
   free). Research belongs in the postulate's own source header, where it sits in front
   of the next person to pick the row up; a roadmap row is a hook.
5. **Tier-preamble budget** — the same charge applied to a tier's section text, within
   `TIER_BUDGET`. It exists because check 4 has an escape hatch and the hatch was used:
   with every bullet inside 280, one tier's preamble reached 4387 characters of
   refutation history, a deletion story, and research already written into the source
   header it belonged in. A check that only reads bullets cannot see that.
6. **No calendar dates** — anywhere in PROOF-STATE.md, and anywhere in the files listed
   in `DATE_ONLY_FILES` (CLAUDE.md and `docs/*.md`), which get this check only.
7. **The evidence field** — every classed row carries a backticked field directly after
   its risk class, naming the durable markers its postulates' own headers carry, and
   matching them. `make roadmap-evidence` writes it; nobody types it.
8. **An unearned GRINDABLE** — a GRINDABLE row whose postulates carry no `TWIN` fails.
   The class means "here is the worked instance"; absent one the row is DIFFICULTY.

## What the preamble check charges, and the one bug it was written after

A tier's preamble is every line in the section that is not row text — so it is collected
by the SAME loop that parses rows, not by an independent scan. That is not tidiness: a
wrapped row's continuation lines are indented and carry no bullet, so any scan that does
not already know where rows end reads them as section text and reports a preamble at
several times its real size. The fixture pins this from both sides — one tier whose
preamble is genuinely fat while every row is inside the row budget (so a passing row
check proves nothing), and one tier whose short preamble sits under three near-budget
wrapped rows that would push it over if they were ever mischarged.

What a preamble is FOR is the tier's shape: the one statement it exports, the doors in
and out of its tree, and what orders its rows. Everything else is a finding, and a
finding has a home — the header of the postulate or definition it is about.

## Why staleness is checked over ROW HEADS and not every name

The roadmap CITES far more names than it CLAIMS, and it must: a row earns GRINDABLE by
naming the proven twin that makes it mechanical, so its prose is full of definitions,
record fields and module names that are legitimately not postulates. A reverse check
over every backticked token would fire on all of them.

So the head's own syntax says which kind it is. A head that is **nothing but names** —
backticks and separators — CLAIMS them, and each must be a live postulate. A head
carrying **prose** ("`X`'s residue", "the `glob-*` family") names a PARENT, so its
names need only still exist in `agda/src`; that is the failure a descriptive head can
have. A claim head's dead names are split by what became of them, because the repair
differs: still declared in `agda/src` means DISCHARGED, absent means deleted or
misspelled.

**The boundary, and it is a real gap.** A family row schedules its siblings in the
HOOK, and a sibling discharged out from under such a row is NOT caught. It cannot be
without marking claims apart from citations in the prose, and the coverage check needs
those hook names to keep counting — narrowing the forward token set to heads would
leave dozens of live postulates unscheduled. **The way to bring a name under this check
is to give it a head of its own.**

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
CLAUDE.md's shape — and a **stale** fixture exercising all three arms of the staleness
check, beside a clean fixture whose rows deliberately cite a proven precedent and carry
a descriptive head, so the two exemptions are pinned as load-bearing rather than
assumed. Two further fixtures pin the evidence field in both of its failing directions —
a row with no field at all, and a row whose field disagrees with the census — against a
`--census` fixture standing in for a scan of `agda/src`. A third pins the unearned
GRINDABLE, against a second census in which the fixture's twin is absent.

## The evidence field, and why a derived field may be mandatory

A row reads `— SHAPE, `REFUTED`:` or `— DIFFICULTY, `NO EVIDENCE`:`. The field lists
`REFUTED`, `DEAD ROUTE`, `TWIN`, `PROBED`, `RECOVERY` in that order — the same
vocabulary and the same rank order `make comments-check` validates — with `×N` when a
header carries a marker more than once.

**Write it with `make roadmap-evidence`.** The field is derived from the headers, and
`roadmap-check` recomputes it and fails on any disagreement, so a hand-typed one is
merely a slower way to reach the same answer or a wrong one.

Two design points worth keeping straight, because they look like contradictions of
rules stated elsewhere:

- **A source header's `TWIN:` is optional-when-absent; this field is mandatory.** The
  optionality argument is about AUTHORED sections, where a required field produces
  filler and a filler `TWIN:` earns a class the row has not earned. A derived field
  cannot be filled with anything. The blank is the product: `NO EVIDENCE` on a FALSITY
  row is a statement nobody has instantiated or refuted a route through, which was
  previously invisible because absence had no marker to be absent.
- **A count is not a copy.** Moving receipts themselves into the roadmap would
  duplicate content, and duplicated content drifts. A count is a function of the
  headers, so the two cannot disagree without the gate saying so.

The field is also what makes check 8 possible. A precedent named in a row's PROSE
resolves nowhere, so GRINDABLE drifted into the place rows nobody wants to think about
get parked — ten of twelve carried no `TWIN` at all when the check was added, and were
demoted to DIFFICULTY. Re-earning the class means putting a `TWIN:` section in the
postulate's own header, where `comments-check` refuses a twin that is itself still a
postulate.

There are deliberately **no aggregates** — no per-tier or whole-file totals. The
per-row blank carries the signal; a total is a number someone has to keep true for no
decision it changes.

Which markers a block reaches is decided by indentation: a header associates with every
declaration under it until the next comment run or the next construct at **column 0**.
That is why splitting a refuted postulate out of a shared `postulate` block into its own
is what gives it its own markers, and why siblings in one block share a header's `TWIN`.

## The hygiene rules a machine cannot check

They live in PROOF-STATE.md's own header and are also part of the gate, by review: one
line per item (name + risk class + hook), NO numbering of any kind (list indices,
conjunct positions, source sections, timings), research in source headers rather than
here, completed items DELETED rather than marked done, no dated narrative. Re-read that
header when you touch the file; every one of those rules exists because it was
violated.
