# `make roadmap-check` — the gate on PROOF-STATE.md (and CLAUDE.md's dates)

`make gate` is necessary, not sufficient: the roadmap is the file every session reads
FIRST, so a stale row misdirects the next session's whole leg. One already did, naming
two postulates that had become real definitions. This target makes the parts a machine
can see into build failures.

## Eleven checks

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
9. **A DIFFICULTY row standing on nothing** — a DIFFICULTY row whose postulates carry no
   marker at all fails. The class claims the statement is true and correctly stated, and
   that is a claim about evidence; absent one the row is SHAPE or FALSITY.

10. **The leg count** — each tier opens with a `### Big picture tier roadmap` naming
    exactly three legs, dropping below three only when the tier has fewer live
    postulates than that to plan over.
11. **The leg budget** — each leg's prose is within `LEG_BUDGET`, which is several times
    `ROW_BUDGET`.

## The roadmap is the schedule; the rows are the ledger

Checks 10 and 11 are the newest and they change what the file IS. A tier now has two
subsections: the roadmap, naming the next three units of work, and the ledger under
`### The ledger`, carrying one row per postulate. A leg is a GROUP aggregated across the
whole ledger — statements sharing a currency, a claim together with the sites that
consume it, one shelf of mechanical obligations — and legs are ranked riskiest-first
without being bound to the class order as tightly as rows are. Where a grouping is not
real, a leg falls back on the classes and may name one row.

The legs do NOT partition the tier. They are the next three units of work; coverage of
the ledger is the rows' job, and check 2 already enforces it. What lies past the third
leg is left unnamed on purpose — it gets re-grouped by whatever the first three find.

The count is fixed rather than bounded because both failures are real. Fewer than three
is a tier planning one leg ahead, which is what reading down the ledger already does.
More than three is a backlog, and the rows already are the backlog — a roadmap that
grows without limit stops being a decision and becomes a second copy of the ledger,
which is what "there is no second roadmap" rules out.

The budget is several times a row's for a reason the row budget does not have: a row
sends its research to the postulate's own header, and a GROUP has no header. So a leg is
allowed to carry its own reasoning — why these postulates are one unit, what risk the leg
retires, why it is above the next. Past the budget it has stopped saying that and started
proving something, and the proof has a home.

Parsing: any `###` heading opens a subsection, and only the roadmap heading makes the
bullets under it legs. That is why the ledger heading closes the roadmap by starting,
and why the roadmap can sit at the top of the tier, where a schedule belongs.

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
GRINDABLE, against a second census in which the fixture's twin is absent, and a fourth
the unevidenced DIFFICULTY, against a third census with the marker removed — that one
also pins the must-NOT direction, since the blank stays legal on a SHAPE row. Two more
pin the legs, and each is built to isolate ONE of them: `legs-count.md` plans two legs in
a tier with the rows for three while every leg is inside budget, and `legs-fat.md` names
three legs of which one carries an argument instead of a reason, with the ROW budget
silent — so neither can pass by tripping the other's check.

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

The field is also what makes checks 8 and 9 possible. A precedent named in a row's PROSE
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

## Why the two class checks are one law read from both ends

Check 8 and check 9 police the same sentence — a class is a property of EVIDENCE, not of
confidence — at the two classes that make a positive claim. GRINDABLE says the shape is
already known, so it owes a worked instance and nothing else will do: `TWIN`. DIFFICULTY
says the statement is true and correctly stated, which any of the durable markers can
buy — a probe that reached the risky region, a refutation pinning this form, a proven
mirror.

The three classes below them are exempt, and that is not leniency. FALSITY, SHAPE and
VACUITY assert nothing about the statement being right, so `NO EVIDENCE` is the honest
reading of a row nobody has instantiated, and a check demanding evidence there would
demand it precisely where there is none to have. It is also what the repair looks like:
a DIFFICULTY row that cannot name its evidence does not acquire a marker, it is
reclassified down — SHAPE where the statement's own gap is written down, FALSITY where
nothing is.

What the check cannot see is whether a marker is evidence about THIS row. A row naming
several postulates merges their markers, so one marked sibling covers a family — which
is correct where the row really is one statement and wrong where it is a bag. When the
census answers a family row with a single marker, the question to ask is whether the row
should be SPLIT, and the answer is usually yes.

## `make roadmap-moved` — the roadmap cannot stay the same across commits

`scripts/check-roadmap-moved.py` compares the working tree's `PROOF-STATE.md`
against `git show HEAD:PROOF-STATE.md` and fails when they are the same — that
is the check mid-work, disk carrying a pending edit against the last commit.
Once that edit is committed, disk and HEAD are identical by construction (a CI
checkout is always in exactly this state), so the same comparison would always
read "unchanged" no matter what the commit did — it would be comparing HEAD
against itself. The script detects this (this file matches its ref *and* the
whole tree is clean — not merely this file, since a dirty tree that just hasn't
touched the roadmap YET must still fail) and falls back to comparing HEAD
against HEAD~1 instead, which is the question a clean checkout actually needs
answered: did HEAD's own commit move the file. Five details:

- **Normalisation.** Trailing whitespace on each line, and trailing blank lines,
  are stripped before comparing — so the cheapest way to satisfy the check is to
  say something rather than to add a space. `roadmap-moved-selftest` pins that
  arm specifically, since it is the one an author reaches for under pressure.
- **`--baseline-file F`** replaces the git lookup with a plain file, which is how
  the selftest drives both directions without touching the repo's history.
  `--ref R` compares against another commit; `--file F` picks another roadmap.
  The HEAD~1 fallback and the exemption below only apply at the default ref —
  an explicit `--ref` is a deliberate comparison point and is read literally.
- **No `PROOF-STATE.md` at the ref** (a first commit, an orphan branch) passes,
  because there is nothing to have moved away from.
- **Infra-only exemption.** An unchanged roadmap is only a finding when there
  was proof work to report: if nothing under `agda/` changed either (over the
  same two endpoints the movement comparison used — disk-vs-ref mid-work,
  HEAD-vs-HEAD~1 once committed), the commit had no leg to retire or restate,
  and the check prints SKIP rather than FAIL. "Changed" means changed once
  full-line comments are stripped, reusing `strip-comments.py`'s own
  stripper — the same principle the `agda/_stripped-comments/` mirror already
  rests on, that a comment-only edit is invisible to Agda. A file the stripper
  refuses to touch (a block comment present) or one that was added or deleted
  is conservatively treated as changed, since comment-only-ness cannot be
  established. Any edit that survives stripping gets no pass, however small.
- **`make gate` runs from a clean CI checkout**, so in practice it is almost
  always the HEAD~1 branch that fires there; the disk-vs-ref branch is what
  the local dev loop exercises before a commit exists to fall back to.

**Why a dumb check is the right one here.** A **leg is one commit of work** —
that is what the unit means — so every commit either retires a leg (promote the
other two, write a new third) or fails to finish one (rewrite the first leg as
the remainder). Both write to the file. What a machine cannot check is the part
that matters: `check-roadmap.py` resolves a row's NAME against the ledger, and
nothing resolves whether the plan a leg describes is still the plan. Forcing the
file to change is the only hold available, and it works by making the author
read the three legs before each commit — which is when the question "is this
still what we are doing?" actually gets asked.

