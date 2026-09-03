# EVIDENCE.md — `agda/evidence/`, what is CHECKED but never CLAIMED

Two trees live here, and one sentence covers both: **evidence is typechecked,
and nothing in `src` may depend on it.**

    agda/evidence/refuted/Refuted/   a proven `… → ⊥` — a route that CANNOT work
    agda/evidence/probed/Probed/     a `refl` receipt at concrete inputs — a
                                     statement that HELD, at the shapes it was
                                     instantiated at

    make refuted        typecheck the refutations  (agda Refuted/Main.agda)
    make probed         typecheck the probes       (agda Probed/Main.agda)
    make evidence-check the laws below — the boundary, expiry, and a probe's kind

A **refutation is conclusive negative evidence**; a **probe is inconclusive
positive evidence**. Neither is a claim, which is why neither is in `src` and
why the collective noun is *evidence* rather than *proof*.

## Why not in `src` — two separate reasons, and both are load-bearing

**For refutations, it is that `src` pays to keep a dead route STATE-ABLE.** The
round-3 anchor vocabulary is the measured case: seven definitions (`walkCap`,
`anchorᴬ`, `sucV≤d`, `d≤walkCap`, `walkCap≤walkArg`, `d≤walkArg`, `ℓ≤walkCap`)
whose only remaining consumers were the six refutations that mention them. Kept
in `src`, that is a whole vocabulary carried so its own obituary can compile.
**Code is cost.**

**For probes, it is that a probe in `src` can be BELIEVED.** A probe's rows are
`refl`s at three or four concrete programs; its conclusion is a receipt bounded
by the shapes it covered, never a theorem. Sitting in `src` it looks like the
rest of `src` — reachable, gated, typechecked — and the one thing that must
never happen is a proof coming to rest on it.

## The distinction that matters: they DECAY differently

This is the whole reason they are two trees under one roof rather than one
tree.

- A **refutation dies when `src` can no longer STATE it** — its vocabulary is
  gone or now means something else. That death **announces itself**: `make
  refuted` goes red the moment it happens.
- A **probe dies when its TARGET dies** — the postulate it was evidence for is
  discharged, restated, or deleted. That death is **silent**. The rows still
  compute, the `refl`s still hold, the file stays green forever, and it is now
  evidence for a question nobody is asking.

So a refutation needs no expiry machinery and a probe does. That asymmetry is
E2.

## The laws — `make evidence-check`

- **E1 — THE ONE-WAY BOUNDARY. Nothing in `src` may import from an evidence
  tree.** Imports go `evidence/` → `src`, freely and deeply: a refutation must
  be stated in the real vocabulary, and a probe must instantiate the real
  evaluator.

  **The MECHANISM is the library layout, not the checker.**
  `agda/rxjs-research.agda-lib` says `include: src` and nothing else, so from
  `src`'s side the names `Refuted.*` and `Probed.*` **do not exist** — such an
  import fails to RESOLVE rather than failing a policy.
  `agda/evidence/rxjs-evidence.agda-lib` says `include: refuted probed ../src`,
  and that asymmetry is the whole boundary: evidence can see the proof, the
  proof cannot see evidence. E1 is the fast, legible
  failure on top of it: a grep-level report in a second rather than an Agda
  scope error minutes into a build, and a check that survives someone
  "fixing" the include path.

- **E2 — A PROBE NAMES A LIVE TARGET.** Every file under `probed/` carries at
  least one `-- TARGET: <postulate>` line, and every name it declares is a
  **live postulate** on `make postulates`' ledger. When the target is
  discharged or deleted, E2 fires, and the probe is **deleted or retargeted**.

  If what a probe actually pins is the **evaluator** rather than a statement,
  it is not a probe — it is a unit test, and its home is the bug cache
  (`Implementation/Unit-Test.agda`, `make bug-cache`).

- **E6 — A PROBE IS A RECEIPT OR A FORK, NEVER NEITHER AND NEVER BOTH.** The
  two products are different. A `-- TARGET:` probe instantiates ONE statement
  and reports that it held: its product is a coverage receipt. A `-- FORK:`
  probe stands at a design choice between two candidate MECHANISMS and its
  product is a separation — these two disagree, so instantiating decides
  between them. Neither marker is E2's finding already; both at once is E6's,
  because a receipt written from a file that also separates claims coverage
  the separating rows never bought.

  **A FORK PROVES ITS SEPARATION IN A TYPE.** The alternatives are two real
  definitions of one signature and the probe inhabits `Separates f g` — a
  witness plus `f at ≢ g at`, whose `apart` field is UNINHABITED when the
  candidates agree. So the marker decides only which law applies and **Agda
  decides whether the claim is true**: the same division as `-- TARGET:`,
  where the marker is free and the obligation it creates is not. This is what
  a comment convention could never buy — a declared fork that decides nothing
  is refused by the typechecker, not by a reviewer's memory.

  A fork **expires exactly as a target does**: E2 reads either marker, so a
  fork whose statement is settled fails the gate and is deleted. E5 stamps
  only targets — a fork's rows are taken against two candidate definitions
  rather than against the target's text.

  **The witness must be REACHED, not constructed**, and that half no type
  carries: it is the hand-built-state failure under PROBE BEFORE GRINDING,
  unchanged.

- **E7 — A RECEIPT'S ROWS ARE TIED TO ITS TARGET'S STATEMENT IN A TYPE.** A
  probe used to restate its target's predicate by hand — a local
  `held d = regP? (λ p → …) …` — and pin THAT by `refl`, so nothing held the
  row to the postulate: a mistyped or quietly weaker predicate stayed green
  and earned a `PROBED:` receipt for a claim nobody had instantiated. Every
  target now has at least one row of type `Confirms (<target> <args>)`, where
  `Confirms` (in `Probed.Apparatus`) takes the postulate APPLIED at the
  probe's own arguments and returns that application's type. Agda generates
  the row's type from the statement as it reads; **the probe chooses only the
  point.** A restated statement changes every row's type under it, which is
  E5's fingerprint law arriving inside the typechecker.

  **THE BODY MAY NAME NO POSTULATE, BECAUSE ANY INHABITANT WOULD TYPECHECK.**
  The postulate itself, handed back as its own proof, inhabits the row, and a
  row discharged out of some OTHER unproven statement is evidence for one
  claim exactly as far as another is true. So the body is free to spend
  anything this tower has PROVEN — `refl` where the claim reduces, a stdlib
  inequality where it does not — and may name no postulate at all.

  **IT IS A LAUNDERING TEST AND NOT A COMPUTATION TEST, AND THE DIFFERENCE IS
  WHAT MAKES THE RULE SATISFIABLE.** Held to a numeral, the rule would ask for
  a conclusion that REDUCES at the chosen point — and a conclusion denominated
  in a family this tower SEALS for cost reduces at no point whatever, so a
  probe whose target is stated in one could never write the row and the
  finding could never be cleared. A weakening through a proven inequality is a
  stronger receipt than a numeral, not a weaker one. And
  **the head under `Confirms` must be a declared `-- TARGET:`**, reached only
  through the statement's own eliminators — `proj₁`/`proj₂`, application at
  a point, a record conclusion's field — since an arbitrary function applied
  to the postulate returns whatever type it likes and the tie is gone.

  **What E7 does not do.** It does not discharge a HYPOTHESIS: the arguments
  handed to the target are the probe's, and a hypothesis it cannot compute
  (`refl` on a decidable one, a real proof otherwise) means the point is
  outside the statement's domain and the file is not a receipt for it — say
  so in the header and cover what the conclusion alone can. Rows reading
  exact numerals (a margin, a count, a non-vacuity pin) stay as they are: a
  `Confirms` row says the claim held, and those rows say by how much.

- **E8 — A LIVE POSTULATE CARRIES AT MOST SEVEN RECEIPTS (Anthony).** A probe
  AIMS a grind or REFUTES a statement. Past a handful of green receipts on one
  target it is doing neither: the seventh has not told anyone what the sixth
  did not, the ledger row is still open, and what the evidence is buying is
  more evidence to DELETE on the day the statement is discharged. Seven rather
  than three because a coverage LATTICE over genuinely separate axes is
  legitimate and this tree has one; rather than twelve because past seven the
  evidence has stopped converting into proof.

  **THE COUNT IS OVER `-- TARGET:` DECLARATIONS, NOT FILES**, so a probe
  carrying three targets pays three — and **the repair is to DISCHARGE the
  postulate or to DELETE the receipts that no longer earn their place, NEVER
  to merge probe modules.** Merging satisfies a file count and changes
  nothing, which is the same laundering as trading a postulate for a
  hypothesis; the selftest pins it by failing eight receipts consolidated into
  two files.

  **DELETING A RECEIPT DOES NOT DELETE ITS FINDING.** A coverage boundary, a
  blocked verdict or a dead route belongs in the header of the statement it
  constrains, and that is where it goes — with `git show <sha>` as the
  recovery route, exactly as a spent probe's receipt already carries one.

  **A REFUTATION IS UNCAPPED, and that is not leniency:** it kills a statement
  that is then GONE, so it cannot accumulate against a live row, and `make
  refuted` goes red the day `src` can no longer state it. **A FORK is uncapped
  from the other side** — it declares no target, and deciding between two
  mechanisms is the one job a single file does. And the cap is **off a
  DISCHARGED target**, whose receipts are E2's finding rather than a second
  one.

Plus, per tree, the wiring law with no exemptions:

- **`make wiring-refuted`** and **`make wiring-probed`** run the reachability
  checker over each tree with `Refuted/Main.agda` / `Probed/Main.agda` as the
  root. A witness the root does not name, and any helper nothing reaches, fails
  exactly as a dead lemma in `src` does. **This is what replaced the probes'
  old `MODULE_ROOTS` entries** — each of which was a self-granted exemption
  *inside the proof's own reachability scan*, which is precisely how a probe
  came to look wired to Main when it was not. A root-based claim cannot
  self-certify; a name-based exemption always can.

## `refuted/` — the rules

- **`Refuted.Main` names every witness**, exactly as `src/Main.agda` names
  every claim. A refutation not listed there is not checked, and an unchecked
  refutation is worth nothing.
- **`src` refers to a refutation in a `-- REFUTED:` comment**, never in code.
  This is safe *precisely because a refuted route does not change* — the
  comment cannot go stale the way a comment about live code does. It also
  preserves LOCALITY: the note sits in front of the next person about to try
  the same thing.
- **A `-- DEAD ROUTE` note is a different artifact and stays in `src`.** It is
  prose in a live postulate's header, for the case where there is no `⊥` to
  state: the statement may well be true, but *this way of proving it* cannot
  work. No code is involved, so the wiring law never applies to it.

### When `src` moves under a refutation (Anthony)

**A JUDGEMENT CALL, and the criterion is state-ability.** If `src` has changed
so much that the refutation can no longer be *stated* — the types it quantifies
over are gone, renamed past recognition, or mean something else now — then
**delete it**. Do not resurrect vocabulary in `src` to keep an obituary
compiling; that is the exact cost this tree exists to avoid, arriving from the
other direction.

Short of that, repair it: a refutation that still states the same impossibility
in today's vocabulary is worth keeping, and `make refuted` going red is the
signal to make that call rather than a thing to route around.

### A refutation must STATE the currency it refutes, not import it

**A refutation that reads a MEASURE out of `src` tracks whatever that measure
means today, and what it refutes is therefore whatever the statement says
today — which is not what it was written against.** The failure is silent in
the direction that matters: a repair that enlarges the measure enlarges the
right-hand side too, and the crossing the witness established quietly becomes
an equality. Nothing goes red. The refutation still typechecks, still gets
counted, still reads as a live finding, and is now evidence for nothing.

So when a repair moves a measure, **localise the old one in the refutation** —
`fooOld` beside the imported `foo` — with a line saying which repair moved it.
That is the same reasoning as the state-ability rule above, one level in: the
statement being refuted includes the definitions it is written over, so keeping
the finding state-able can mean re-deriving a definition and not only a type.

**AND THE NUMERIC ROWS BESIDE THE WITNESS ARE WHAT CATCH IT.** A witness whose
figures are pinned by `refl` — store 7, depth 9, right-hand side 8 — fails
loudly the moment any of them moves, naming the number. A witness that computes
its sides inline does not. This is the strongest argument for spelling the
figures out even where the `⊥` does not need them.

### Keeping a refutation after its route is settled (Anthony)

**Do not reflexively delete a refutation because the surrounding goal has since
been proven some other way.** Nothing in this campaign is settled until
`The-Proof.agda` is discharged, and until then there is always some chance of
having to reopen a region. A refutation that says "not that way" keeps its
value across a reopening; the proof that superseded it does not carry that
information.

This is a deliberate exception to *keep the repo lean*: the carrying cost out
here is one `make refuted` run, and it is paid outside the gate.

## `probed/` — the rules

- **`Probed.Main` names every probe module**, same law as `Refuted.Main`.
- **`-- TARGET: <name>` is a DECLARATION, not prose.** One per line, bare
  postulate names, and E2 reads it. A probe may name several targets. The
  header prose that says what was covered stays — it is the part no machine
  can check — but the target itself is now machine-read, which is what makes
  expiry a build failure instead of a habit.
- **EVERY ROW IS LABELLED `LOAD-BEARING` OR `DEGENERATE`**, and a probe says
  what would make it fail. Unchanged from CLAUDE.md's de-risk rules; repeated
  here because this is where probes now live. The three ways a probe lies
  green — a vacuous quantifier, a hand-built unreachable state, an assembly
  read backwards — are in CLAUDE.md under PROBE BEFORE GRINDING.
- **The RECEIPT still goes in the postulate's own header, in `src`**, as
  `-- PROBED:` saying which shapes were covered — undated, since
  `make comments-check` outlaws a date in a source comment and a coverage
  statement is re-runnable, so its age says nothing a reader can act on. The
  probe is the apparatus; the receipt is the finding, and the finding belongs
  next to the statement it is about. This is the same locality rule as
  `-- DEAD ROUTE`.
- **AND THE RECEIPT IS CHECKED (E3), BECAUSE IT OUTLIVES EVERYTHING ELSE.** The
  probe expires and is deleted; the receipt stays, and for most of this
  campaign's probes it is the only surviving trace in the tree. So it carries
  the same discipline E2 puts on a probe's `-- TARGET:`. A receipt is
  `-- PROBED:` — ONE spelling, with no dated and no historical variant — and it
  must sit above a declaration whose statement is still a POSTULATE, so that
  DISCHARGING one fails the gate until the receipt has been re-read and
  DELETED (a receipt above nothing is evidence about nothing; a receipt above a
  proven definition is a coverage claim the theorem has already superseded).
  An invented marker is a finding rather than a silent skip —
  a spelling the check does not know is a receipt it cannot audit, which reads
  as evidence and is enforced as nothing.
  **The value is WHEN it fires: at the discharge.** Proving a statement turns
  every receipt above it into a claim about something no longer open, and that
  is precisely the moment a live risk class left standing in prose becomes a
  lying comment. Failing then puts the re-read in the hands of whoever has the
  statement in front of them. The marker is mechanical; re-reading the PROSE
  under it is the actual obligation.
- **AND WHEN A POSTULATE BECOMES AN ASSEMBLY, THE RECEIPT FOLLOWS THE OPEN
  STATEMENT DOWNWARD.** E3 admits a receipt over a live postulate and over
  nothing else, and the repo's central move produces a statement that is
  neither open nor settled: a real body over leaves that are still open. The
  parent can carry no receipt at all, and a marker invented to let it says the
  parent is settled — the lying comment E3 exists to prevent, arriving from the
  other side. **Do not invent one** — a spelling the check does not know is a
  receipt it cannot audit, which is the finding E3 already reports. Move the
  receipt into
  the header of the LEAF, and say in it which instantiation the rows reached:
  rows that pin the parent's conclusion instantiate the leaf at whatever the
  assembly passes, and the leaf's generality is the part they do not touch. E3
  reads an indented receipt on a `postulate` block member, so the leaf's own
  header is a legal home.

- **A `-- PROBED` RECEIPT MAY OUTLIVE ITS PROBE, AND THAT IS FINE.** A receipt
  names the probe it came from; when the probe has been deleted, that name will
  not be in `probed/`. It is not a dangling reference to repair — the target is
  still a live postulate, which is all E3 holds the receipt to, and the probe
  was the apparatus while the receipt is the finding. **Then the receipt
  CARRIES THE SHA**, because that is the whole recovery route:
  `git show <sha>:<path>` reads the probe back, and
  `git log -S'<name>' --all` finds it — by the NAME it
  tested, not by a path, since probes have not always lived in `probed/` and a
  path-scoped search over a moved directory answers ALL-CLEAR. CLAUDE.md carries
  the standing rule to run that search before probing any non-GRINDABLE row. What is
  NOT fine is a receipt left standing over a statement that has been DISCHARGED;
  E3 fails there, and the repair is to re-read the prose and DELETE it, never to
  restamp it into a tense the check does not have.
- **A probe is DELETED when E2 fires.** Not parked, not commented out, not
  kept "in case the region reopens" — that licence belongs to refutations,
  which carry information across a reopening ("not that way"). A probe carries
  no such information: it says a statement held at four programs, and once the
  statement is proven that is worth nothing, while once the statement is
  RESTATED the rows may not even correspond to it.

## What stays in `src`

A `… → ⊥` with a **real consumer** is not a refutation record — it is an
ordinary lemma that happens to be negative, and it belongs in `src` like any
other. Today: `f≡t-absurd` (`.Measures`) and `applyEvents-val-done-absurd`
(`Verify-Well-Formed/Part7`), both applied as proof terms.

Likewise a `refl` pin with a real consumer is not a probe; and a `refl` pin
with no consumer that captures a known implementation BUG is not a probe
either — it is a bug-cache entry, append-only, with its own end-of-life
(`make bug-cache`).

The test is consumption, not the name. Nothing is classified by its suffix.
