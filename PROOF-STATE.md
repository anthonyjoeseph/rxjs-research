# PROOF-STATE — the roadmap

**What this file is.** The ordered worklist for the one goal: discharging
`agda/src/Verify-Batch-Simultaneous/The-Proof.agda` — no postulates, everything
typechecks. This file holds the SCHEDULE — each tier's next legs — over a
LEDGER of one-line hooks; everything else lives in the code.

**Hygiene — the rules this file lives by:**

- **Stay current.** This file describes the repo's present state and the work
  ahead — never its history. No dated narrative, no "was X, now Y", no
  superseded plans, no references to code that no longer exists. Git history
  is the archive.
  **`make roadmap-check` ENFORCES THE DATE HALF** — this file names no calendar
  date, anywhere, and one is a build failure. The same scan holds CLAUDE.md to
  the rule, for the neighbouring reason: this file must be CURRENT, that one
  must be TIMELESS. It is the half a machine can see
  with no judgement, and it catches most of the rest by proxy: history arrives
  here WITH a timestamp attached, because the writer knows the reader will want
  to know when. Dates are wanted in a postulate's header, where their age is
  the point, and in CLAUDE.md, where a ruling's attribution belongs. A "was X,
  now Y" that carries no date still has to be caught by eye — which is a reason
  to read the file, not a reason to catch none of it.
- **Completed items are DELETED, not marked complete.** No ~~strikethrough~~,
  no "✅ DONE" rows, no discharged-count bookkeeping in tier headings. The
  deletion happens in the same commit as the discharge, and the commit
  message carries what was proven. A completed row left in place is the seed
  of dated-narrative rot.
- **Research lives in source comments**, in the header of the postulate or
  definition it is about — probe receipts (`-- PROBED`), failed routes
  (`-- DEAD ROUTE`), proof sketches, coverage residue, recovery pointers.
  If a note here outgrows its one line, it belongs in a header instead.
  **`make roadmap-check` ENFORCES A CHARACTER BUDGET, on a row's hook AND on
  a tier's PREAMBLE.** The second is not redundant: holding every bullet to a
  line while writing the finding into the section text above them satisfies
  the row budget exactly, and one tier's preamble reached 4387 characters
  that way — a deleted face's refutation history, a superseded predecessor's
  deletion story, and the research for a currency swap that was already in
  the source header it belongs in. A preamble says what the tier IS: the one
  statement it exports, the doors in and out, and what orders the rows.
- **No numbering.** Items are referred to BY NAME (postulates are unique,
  greppable names — the wiring law guarantees it). Order within a tier is
  the schedule: top item first. Reorder freely, in the same commit as the
  finding that reorders it. This covers EVERY positional scheme, not just
  list indices: conjunct positions ("conjunct (8)" — say `the hasDry
  conjunct`), source section numbers ("§ 5a" — say the postulate's name),
  timing figures (those live in typecheck-performance-numbers.md alone).
  A position silently re-aims when the thing it indexes is edited; a name
  greps or it errors.
- **THE BIG PICTURE TIER ROADMAP IS WHAT YOU FOLLOW; THE ROWS ARE THE LEDGER
  IT IS DRAWN FROM (Anthony).** Every tier opens with a
  `### Big picture tier roadmap` ... `### The ledger` carrying
  the rows. A leg is a GROUP: several postulates sharing a currency, a
  statement together with the sites that consume it, one shelf of mechanical
  rows. Group where the grouping is real and fall back on the risk classes
  where it is not; a leg naming a single row is still a leg.
  **AND A LEG IS ONE COMMIT OF WORK (Anthony).** That is the unit — not a theme
  and not a region, but the chunk this session intends to land next. So the legs
  are the next COMMITS, and every leg after the first may aim at the very same
  postulates as the first; what the set owes is a coherent vision for reducing
  the most risk, cut at commit boundaries. Pick the risk order first, then cut —
  never pick topics and hope each is commit-sized.
  **SO THE FILE MOVES WITH EVERY COMMIT, and `make roadmap-moved` fails when it
  does not.** Three outcomes. The leg landed: retire it, promote the rest, write
  a new last one. It did not finish: **rewrite the first leg as the work that
  remains**, the only record of what it turned out to cost. Or its ROUTE DIED:
  **discard it** — a refuted framing rewritten smaller is still steering, so the
  finding goes to the header of the statement it constrains and the leg that
  replaces it is written from the risk as it now stands.
  **THE LEGS DO NOT HAVE TO COVER THE TIER (Anthony).** They are the NEXT ones,
  not a partition of the remaining work — the coverage rule is the LEDGER's job,
  and the rows already discharge it. Work beyond the last leg is left unnamed on
  purpose: it will be re-grouped by what the earlier ones find, so naming it now
  writes a plan that ages before it is read.
  **Pick up the top LEG, not the top row.** Reading straight down the ledger
  works exactly one postulate at a time, and the expensive part of this
  campaign is never the clause — it is discovering, after the clause is ground,
  that the statement's neighbours had to move with it.
  **`make roadmap-check` ENFORCES THE COUNT AND A PROSE BUDGET PER LEG.** At
  least three — unless the tier has fewer live postulates than that to plan over
  — and at most seven. Fewer than three is a tier planning one leg ahead; more
  than seven is a backlog, and the rows already are the backlog. Between them
  the schedule is free, because a route already decided and cut into commits is
  written down rather than displaced by the next one. The budget is several
  times a row's, because a leg carries its own reasoning and a group has no
  header to send research to; past it, the leg has stopped saying why this group
  is next and started proving it.
- **A TIER MAY OPEN AN `### Open questions` SECTION, AND IT IS NOT A SECOND
  ROADMAP (Anthony).** A question is what the tier does not yet KNOW that
  several of its FALSITY rows are all waiting on — the thing a row cannot
  say, because a row is about one statement and the uncertainty is shared.
  So it names at least two, and answering one moves all of them at once.
  It is capped at three for the roadmap's reason: past that the entries are
  rows wearing headings, or two phrasings of one question.
  **BUT IT IS NOT REQUIRED TO MOVE, AND NOT REQUIRED AT ALL.** A leg is a
  commit, so it moves with every commit; a question outlives many, and
  forcing one to change per commit would produce a rewritten question rather
  than an answered one. Nor is the section mandatory per tier — a required
  question is a filler question, exactly as a required `TWIN:` is filler,
  and filler here is worse than blank because it reads as research.
  **WHAT IS HELD INSTEAD IS THE `relevant:` LINE, and `make roadmap-check`
  enforces it.** Every name on it must still be a LIVE postulate, must be a
  row of that same tier, and must still be FALSITY or SHAPE. Nothing else
  would notice this section aging, so that list is the one thing kept
  current: a name off the ledger means the question is answered or its row
  was restated. SHAPE counts because a question's rows convert FALSITY →
  SHAPE as it is ANSWERED — that is what a half-answer leaves behind, and
  holding the list to FALSITY retired a question at the very moment the
  narrowing it exists to record had happened. When nothing risky is left,
  the question goes. The list is FREE of the prose budget, so a question is
  never shortened by dropping a postulate from it — the same asymmetry the
  rows carry, for the same reason.
- **EVERY TIER IS SORTED RISKIEST-FIRST, AND THE SORT IS AN INVARIANT —
  NOT A ONE-TIME TIDY.** Within a tier, rows appear
  in risk-class order: FALSITY, then SHAPE, then VACUITY, then DIFFICULTY,
  then GRINDABLE. **Re-sort in the SAME commit as any edit that could move a
  row** — a class raised or lowered, a postulate added, discharged, split, or
  renamed. A split is the easy one to miss: it can put a SHAPE child in a
  parent's GRINDABLE slot.
  **Why it is an invariant and not cosmetics:** the ledger's order is what the
  roadmap above it is drawn FROM, so a stale sort silently re-aims the next leg
  — and it re-aims it toward the SAFE end, because grinding is what
  looks like progress. A riskiest row buried below four safer ones goes
  untouched for exactly one reason: the list said it was ninth.
  **`make roadmap-check` ENFORCES THIS — it is part of `make gate`.** It fails
  the build when a tier's classes improve and then worsen, naming the row and
  the row it must move above. Order WITHIN a class is a judgement call and is
  deliberately NOT checked: if two rows share a class, order them by what
  unblocks more. A row naming no class is reported but not ordered, so an item
  cannot dodge the check by omitting its class.
  **It is machine-checked rather than trusted because the by-eye version is
  satisfiable while still failing** — a hand re-sort fixes the tier being
  looked at and silently leaves the others. `make roadmap-selftest` pins the failing
  path against fixtures, including the row that must NOT fire: a row whose
  prose mentions a better class later still reads at its declared one.
- **One line per item: name + risk class + hook.** The hook says where
  the risk lives and where the full story is (always a source header) —
  it does not TELL the story. An entry that has grown sentences of
  mechanism, receipts, or history is a header that leaked; move it to the
  postulate's header and cut the entry back to its line.
  **`make roadmap-check` ENFORCES A CHARACTER BUDGET on each row's PROSE**,
  names excluded, and over budget is a FAILURE. Names are free because the
  coverage rule below requires every scheduled postulate to be named — charging
  for them would put the two checks in conflict and the shorter file would win
  by deleting a name. The budget is set from the distribution and lives in
  `scripts/check-roadmap.py`; re-scan before moving it, since it is the GAP
  between the compliant rows and the leaked ones that makes it safe.
  A leaked row is not merely untidy: it puts the finding far from the postulate
  someone picks up six weeks later, which is the locality argument behind
  `-- DEAD ROUTE` running backwards.
- **The evidence field is DERIVED — never type it, run `make roadmap-evidence`.**
  Every classed row carries a backticked field directly after its risk class,
  naming the durable markers that row's postulates carry in their own source
  headers — `REFUTED`, `DEAD ROUTE`, `TWIN`, `PROBED`, `RECOVERY`, with `×N` for
  a repeat — or `NO EVIDENCE` when they carry none. **`make roadmap-check`
  RECOMPUTES IT and fails on any disagreement**, which is the only reason it is
  allowed to live here: a count is a function of the headers, not a copy of
  them, so the two cannot drift the way a duplicated receipt would. The blank is
  the point rather than a gap to fill — a row reading `NO EVIDENCE` says nobody
  has instantiated the statement, refuted a route through it, or found it a
  twin, and an unprobed probeable postulate is the cheapest unmanaged risk in
  the repo. It reads as nothing today only because absence had no marker.
- **The ledger is the source of truth, not this file.** `make postulates` lists
  every live postulate by name; every one of them appears in exactly one tier
  below, and a name here that no longer greps is a bug in this file — fix on
  sight. **`make roadmap-check` ENFORCES THE COVERAGE HALF** — a live postulate
  no row names fails the build, so a postulate cannot be added and never
  scheduled. Unscheduled debt is exactly the kind the wiring law exists to
  prevent, one level up: `make wiring` proves every postulate is CONSUMED, and
  nothing else proves any of them is PLANNED. Shorthand counts as naming —
  `{a,b}` expansion, `readme-*` globs, and a `-suffix` after a sibling in the
  same row — but a collective phrase does not: a row reading "nine postulated
  abstractions" names nothing the check can see.
- **There is no second roadmap.** Not a session task list, not a worker's
  notes, not a scratch file. A parallel list is outside the repo, so no gate
  and no `grep` can see it rot: it keeps its completed rows, it survives this
  file's rewrites, and it gets read in preference to this file because it is
  the one the session wrote. The tell is citing work by a NUMBER — names come
  from here and from the ledger, numbers come from somewhere that should not
  exist. Find it and delete it.

**The tier law and the risk classes are DEFINED IN CLAUDE.md** — the
lowest-numbered tier below finishes first, strictly, and an emptied tier is
DELETED rather than renumbered, so the numbers are names and not positions;
classes worst-first are FALSITY, SHAPE, VACUITY, DIFFICULTY, GRINDABLE. This
file only ASSIGNS them, and schedules them into legs. Read that section
before re-classifying anything: what counts as evidence for lowering a class, the
convergence test for whether a spawned FALSITY is progress, and why GRINDABLE is
the delegation boundary, all live there. A GRINDABLE row must name its worked
precedent in the postulate's own header — if the hook here cannot point at one,
the row is DIFFICULTY.

## The theorem chain (top → leaves)

```
formal-verification-batchSimultaneous    The-Proof.agda — REAL, module postulate-free
 ├─ batch-agreement                      proven
 └─ evaluate-well-formed                 Verify-Well-Formed.agda — REAL, one match
     └─ burst-drain-well-formed          one postulate — tier 2

  evaluate↓ = proj₁ ∘ evaluate!           Rx/Evaluator/Builder.agda — tier 1
     └─ every value-path leaf is a body; the corpus runs

  every tier above is stated over Rx.Exp's syntax
```

The descent is the evaluator's own and is stated nowhere else: a Girard–Tait
reducibility candidate `Red`, recursing on the TYPE rather than on any measure
read off the program. The three edges no structural reading reaches — the μ
peel, the flattener's hop, a share's connect — are answered by it and by
nothing else; every other member of the subscribe cycle descends on a term or
shortens a list, which Agda reads for itself. The evaluator is `proj₁` of a
builder that returns a run together with its derivation, which is what let
every guard, every `<?` and the dry marker leave the machine entirely.

A row's class must agree with its postulate's header, which is where the
research lives; where they disagree, the header wins.

## Tier 1 — the evaluator runs again

**THE TIER IS A PROJECTION, AND THE PROJECTION NOW COMPUTES.** `evaluate↓` is
`proj₁` of `evaluate!`, which hands back a run TOGETHER with its `evaluate⇓`
derivation, so the descent is a proof obligation rather than a reading the
machine computes and the dry marker is unemittable — no constructor of the
relation builds one.

**AND THE TIER RETIRES ON NO POSTULATE AT ALL (Anthony).** `reducible` is a
body recursing structurally on the term, and its remaining leaves are the arms
with no subterm to recurse on. This tier is done when that definition stands on
NONE of them. The shape they end up taking is free — what is not free is leaving
one postulated, which is risk carried under every tier above rather than work
deferred beside it.

### Big picture tier roadmap

- **THE FIXPOINT PEEL, TAKEN FIRST BECAUSE IT IS THE ONE THAT COULD STILL BE
  FALSE (Anthony).** The peel and the substitution commute, which is what the
  partner's μ arm spends. Its induction is over the guarded ELIMINATION rather
  than over the telescope, so nothing the renaming shelf buys transfers to it,
  and a wrong telescope shows here and nowhere else. The rows now reach that
  shape and hold, so what the leg carries is no longer whether the statement
  survives it but whether the eliminator's six families can be walked under the
  identity transport the empty substitution already spends.

- **THEN THE EMBEDDING ARM, WHICH IS ALL THAT IS LEFT OF THE TELESCOPE LEG.**
  A weakened-from-closed term is now proven inert under substitution, and
  reify-then-read at an observable — the half of this leg that read as riskiest,
  since its literal carries a whole expression to close — fell straight out of
  it. What remains is the stream literal met on the TERM side, where the reading
  does not read but CLOSES, so the arm is substitution COMPOSITION: two
  substitutions in sequence against their concatenation, which is the renaming
  shelf's statement with the right half reassociated rather than emptied.

- **THEN RUN A SELF-REFERENTIAL μ, IN THE CORPUS RATHER THAN IN A PROBE.** The
  peel is now paid for by a size the unfolding does not move, and what funds that
  size is a SYNTACTIC claim: the μ variable is bound into the guarded context,
  `varᵉ` reads only from the usable one, and the guarded elimination substitutes
  nowhere except through its gate clause. Every leaf under it now rests on that.
  The claim is about the ELIMINATOR rather than about any statement, so nothing
  can carry a receipt for it and its home is the corpus — programs whose μ really
  does refer to itself, run end to end. Cheap, and the one thing that would catch
  the guard being right on paper and wrong in the code.

- **THEN THE MECHANICAL SHELF, WHICH IS NOW ONE ROW.** The flattener's consume
  fallback, where an arrival at a usable node is subscribed and the inner's own
  derivation is what comes back. It comes last of the named legs because the
  legs above can still change what it must be written against — a walk that
  reaches a live inner subscribes it, and that is the site this row is stated
  at. Grinding it before the risk above settles buys work a restatement upstream
  would throw away, which is why the ordering is written down rather than left
  to whatever happens to be nearest.

- **THEN COLLECT THE BUG CACHE, WHOSE SUSPENSION EXPIRES WITH THE LAST LEAF.**
  `make bug-cache` self-suspends while the reducibility body holds live
  postulate leaves, because a corpus run through a postulated arm is a run
  through nothing. That suspension is written to expire on its own: the day
  the last leaf falls the runner is live again, over a corpus that has been
  appended to throughout and never executed against this body. This leg is
  the collection — run it, and whatever it reports is a counterexample the
  proof above was never checked against.

- **THEN WHATEVER DESIGN WORK REMAINS.** The candidate funds `Runs` and nothing
  else; the other eight `*Runs` families have no candidate and the bet is that
  once subscription is independently total their recursion is structural. That
  bet is decided by CI rather than by argument, and whatever it leaves open is
  this leg — it is named rather than planned because its content is exactly what
  the three legs above turn up.

- **THEN WHATEVER GRINDING REMAINS.** The leaves the legs above leave behind,
  once each has a settled shape and a named route. This is the delegation
  boundary and the first leg here that is not the design session's own work.

### The ledger

- **`sub-unfoldμ`** (Rx/Evaluator/Reducible) — FALSITY, `PROBED`: the fixpoint
  peel commutes with the environment substitution. This is what the partner's μ
  arm spends, and it is where a wrong telescope would show.

- **`sub-evalStrm`** (Rx/Subst-Eval) — FALSITY, `PROBED`: the term face handing
  back to the expression face. Not an induction hypothesis but substitution
  COMPOSITION, since a stream literal is closed rather than read.


- **`red-thru`** (Rx/Evaluator/Reducible) — DIFFICULTY, `PROBED`: the consume
  fallback is pinned now, so an arrival at a usable node is subscribed and the
  inner's own derivation is what comes back. The queue it fills is never read
  back from here. Rows at all three operators.

## Tier 2 — Verify-Well-Formed (parked behind tier 1)

Built on the run's own derivation, so proving anything here while tier 1 is
open bets on ground a failure of the descent would move.

**THE TIER IS ONE STATEMENT OVER ONE LEAF.** `The-Proof` draws
`evaluate-well-formed` and nothing else from this face. That name is a real
body: it splits the descent's dry-freeness across the subscribe frame and the
drain, and hands the two halves to the leaf. The split is what CONSUMES tier 1
— a leaf handed the descent's own conclusion directly would assert its
sufficiency without ever checking it, which is the shape the leaf law refuses.

**AND THE BOOKKEEPING IS DELIBERATELY UNCARVED.** The protocol argument's shape
is a function of a recursion tier 1 may still restate, so pieces cut against
today's machine are inventory and not progress. One leaf at full strength; carve
it when the descent under it settles.

### Big picture tier roadmap

- **instantiate the leaf before carving it** — `burst-drain-well-formed`. Both
  its hypotheses and its conclusion compute at a closed program, so the whole
  statement is decidable by `refl` at canonical shapes — and nothing has ever
  run the protocol automaton over an evaluator emit stream, at any program. The
  commit is the probe alone: which operators the rows reach, which they do not,
  and whatever a red row forces on the statement. It is taken first because
  every way of carving this face into pieces is a bet on the leaf being true,
  and a leaf refuted after the carve costs the carve as well.

### The ledger

- **`burst-drain-well-formed`** (Verify-Well-Formed) — FALSITY, `PROBED`:
  everything the protocol argument owes about a run whose subscribe frame and
  whose drain are each dry-free. The sweep decides its conclusion at every
  program it runs, so what is open is the fragment the generator cannot write.

## Tier 3 — the top-line semantic claims (parked behind tier 2)

The second ledger: claims Main asserts beside the main theorem, off its
critical path.

### Big picture tier roadmap

- **probe the `readme-*` family** — the `readme-*` rows. Nothing has ever
  instantiated them and they are stated over defined machinery, so they are
  probeable today and the whole family shares one harness: one context, many
  similar obligations. One commit for the sweep and its receipts. A refutation
  here is SPEC-level — surface it, do not patch it.
- **probe the two inheritance claims** — `id-inheritance`, `batch-online`.
  Separated from the family above because they are stated over the batching
  pipeline rather than the readme's programs, so they need their own harness;
  same shape of commit, and unprobed is unprobed whatever the statement reads.
- **draft the abstractions and ASK** — `locality`, `non-interference`,
  `timing-invariance`, `causality`, `μ-guarded`, `defer-shift`, over `Node`,
  `NodeSt`, `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`, `retime`,
  `truncateIn`, `emittedBefore`. De-risking any of these means DEFINING the
  abstraction under it, which is claim authoring and Anthony's call. The
  commit is the drafted definition set and the question, not a discharge.

### The ledger

- **`id-inheritance`, `batch-online`, `readme-*`** — FALSITY, `NO EVIDENCE`:
  the twelve top-line claims nothing has ever instantiated. A refutation of a
  `readme-*` claim is SPEC-level: surface to Anthony, do not patch.
- **Vacuous-by-abstraction — VACUITY**, `NO EVIDENCE` — `locality`,
  `non-interference`, `timing-invariance`, `causality`, `μ-guarded`,
  `defer-shift` (the one allowlisted honest gap). De-risking these means
  DEFINING the abstractions: claim authoring that needs Anthony. **Not
  GRINDABLE and never will be** — no precedent can make them mechanical,
  because nothing is stated yet.
- **The abstractions those claims quantify over — VACUITY**, `NO EVIDENCE` —
  `Node`, `NodeSt`, `Inbox`, `inboxOf`, `stAt`, `cascade`, `δ`, `Retiming`,
  `retime`, `truncateIn`, `emittedBefore`. Named individually because they are
  what makes the row above vacuous, and a collective phrase is invisible to the
  coverage check.
- **`μ-unfold`, `fuel-coherent`** (Evaluator-Theorems) — DIFFICULTY,
  `PROBED×2`: the two evaluator laws a spent battery instantiated at every
  canonical program without refuting. Split from the twelve below, which have
  no receipt at all.
- **FFI, permanently trusted** — `_>>=_`/`getContents`/`putStr` (CLI/IO),
  `randFold`/`natMod` (QuickCheck). Carried, not counted.

