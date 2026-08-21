# EVIDENCE.md — `agda/evidence/`, what is CHECKED but never CLAIMED

Two trees live here, and one sentence covers both: **evidence is typechecked,
and nothing in `src` may depend on it.**

    agda/evidence/refuted/Refuted/   a proven `… → ⊥` — a route that CANNOT work
    agda/evidence/probed/Probed/     a `refl` receipt at concrete inputs — a
                                     statement that HELD, at the shapes it was
                                     instantiated at

    make refuted        typecheck the refutations  (agda Refuted/Main.agda)
    make probed         typecheck the probes       (agda Probed/Main.agda)
    make evidence-check E1 + E2, the two laws below

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

## The two laws — `make evidence-check`

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
  `-- PROBED <date>:` saying which shapes were covered. The probe is the
  apparatus; the receipt is the finding, and the finding belongs next to the
  statement it is about. This is the same locality rule as `-- DEAD ROUTE`.
- **AND THE RECEIPT IS CHECKED (E3), BECAUSE IT OUTLIVES EVERYTHING ELSE.** The
  probe expires and is deleted; the receipt stays, and for most of this
  campaign's probes it is the only surviving trace in the tree. So it carries
  the same discipline E2 puts on a probe's `-- TARGET:`. A receipt is
  `-- PROBED <date>` when its subject is a LIVE postulate and
  `-- PROBED-HISTORICAL <date>` once that statement is PROVEN, it must sit in
  the header of a declaration (a receipt above nothing is evidence about
  nothing), and an invented marker is a finding rather than a silent skip —
  a spelling the check does not know is a receipt it cannot audit, which reads
  as evidence and is enforced as nothing.
  **The value is WHEN it fires: at the discharge.** Proving a statement turns
  every receipt above it into a claim about something no longer open, and that
  is precisely the moment a live risk class left standing in prose becomes a
  lying comment. Failing then puts the re-read in the hands of whoever has the
  statement in front of them. The marker is mechanical; re-reading the PROSE
  under it is the actual obligation.
- **A `-- PROBED` RECEIPT MAY OUTLIVE ITS PROBE, AND THAT IS FINE.** A receipt
  names the probe it came from; when the probe has been deleted, that name will
  not be in `probed/`. It is not a dangling reference to repair — the receipt is
  a historical note in the header of what is now a proven definition, and
  `git log -S'<name>' --all` finds the probe that produced it — by the NAME it
  tested, not by a path, since probes have not always lived in `probed/` and a
  path-scoped search over a moved directory answers ALL-CLEAR. CLAUDE.md carries
  the standing rule to run that search before probing any non-GRINDABLE row. What is
  NOT fine is a receipt asserting a live RISK CLASS on a discharged statement;
  that is a lying comment, and it is fixed by deleting the assertion.
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
