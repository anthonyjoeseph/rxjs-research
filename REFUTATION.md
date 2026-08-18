# REFUTATION.md — `agda/refuted/`, the machine-checked dead ends

A **refutation** is a proven `… → ⊥`: a theorem saying a route *cannot* work.
They live in `agda/refuted/`, a second include root, checked by `make refuted`.

    make refuted        typecheck the whole tree (agda refuted/Refuted/Main.agda)

## Why they are not in `src`

Because keeping a dead route in `src` forces `src` to keep whatever machinery
makes that route **state-able**, and that machinery is otherwise deletable.

Measured 2026-08-18: the round-3 anchor vocabulary — `walkCap`, `anchorᴬ`,
`sucV≤d`, `d≤walkCap`, `walkCap≤walkArg`, `d≤walkArg`, `ℓ≤walkCap` — was seven
live definitions in `.Measures`, retired since 2026-08-13, held up by nothing
but the six refutations that mention them. `src` was carrying a whole retired
vocabulary so that its own obituary could be written. **Code is cost.**

The move also closed a real hole. Refutations used to be exempted from the
wiring law by a **suffix match** on `*-absurd`, which meant any definition
could exempt itself from the wiring law by choosing its name. Out here they
need no exemption at all, so the checker has none: `make wiring` scans
`agda/src` only.

## The rules

- **IMPORTS GO ONE WAY: `refuted/` → `src`, never back.** The tree imports
  freely and deeply from `src` — that is the point, a refutation must be
  stated in the real vocabulary. Nothing in `src` may import `Refuted.*`, and
  that is what keeps `make agda` from ever paying for this tree: it compiles
  `src/Main.agda`, which cannot reach here.
- **`Refuted.Main` names every witness**, exactly as `src/Main.agda` names
  every claim. A refutation not listed there is not checked, and an unchecked
  refutation is worth nothing.
- **`src` refers to a refutation in a `-- REFUTED:` comment**, never in code.
  This is safe *precisely because a refuted route does not change* — the
  comment cannot go stale in the way a comment about live code does. It is
  also what preserves LOCALITY: the note sits in front of the next person
  about to try the same thing.
- **A `-- DEAD ROUTE` note is a different artifact and stays in `src`.** It is
  prose in a live postulate's header, for the case where there is no `⊥` to
  state: the statement may well be true, but *this way of proving it* cannot
  work. No code is involved, so the wiring law never applies to it.

## When `src` moves under a refutation (Anthony, 2026-08-18)

**A JUDGEMENT CALL, and the criterion is state-ability.** If `src` has changed
so much that the refutation can no longer be *stated* — the types it quantifies
over are gone, renamed past recognition, or mean something else now — then
**delete it**. Do not resurrect vocabulary in `src` to keep an obituary
compiling; that is the exact cost this tree exists to avoid, arriving from the
other direction.

Short of that, repair it: a refutation that still states the same impossibility
in today's vocabulary is worth keeping, and `make refuted` going red is the
signal to make that call rather than a thing to route around.

## Keeping a refutation after its route is settled (Anthony, 2026-08-18)

**Do not reflexively delete a refutation because the surrounding goal has since
been proven some other way.** Nothing in this campaign is settled until
`The-Proof.agda` is discharged, and until then there is always some chance of
having to reopen a region. A refutation that says "not that way" keeps its
value across a reopening; the proof that superseded it does not carry that
information.

This is a deliberate exception to *keep the repo lean*: the carrying cost out
here is one `make refuted` run, and it is paid outside the gate.

## What stays in `src`

A `… → ⊥` with a **real consumer** is not a refutation record — it is an
ordinary lemma that happens to be negative, and it belongs in `src` like any
other. Today: `f≡t-absurd` (`.Measures`) and `applyEvents-val-done-absurd`
(`Verify-Well-Formed/Part7`), both applied as proof terms.

The test is consumption, not the name. Nothing is classified by its suffix any
more.
