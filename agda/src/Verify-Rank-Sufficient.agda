------------------------------------------------------------------
-- THE EVALUATOR NEVER GETS STUCK: no run of any program emits the dry
-- marker.
--
-- `evaluate` descends on an accessibility witness, and three of its
-- clauses are guarded by a decidable comparison that can fail — the
-- share connect's unconnected count, the inner subscribe's rank, the μ
-- unfold's syncSize.  A failing guard is not an error: the clause
-- returns a `dry` emit and the run continues, so exhaustion is VISIBLE
-- in the output rather than fatal.  This says the guards never fail at
-- the triple the evaluator actually enters at, which is what makes the
-- descent discipline invisible to every statement above it.
--
-- IT IS THE WHOLE OF WHAT THE DESCENT COSTS, and stating it in one line
-- is the point.  Its type mentions no witness, no triple and no order:
-- `evaluate` seeds its own entry, so every consumer sees a total
-- function on `Fuel`, and this is the only place the seeding has to be
-- shown adequate.  A statement anywhere above that had to know which
-- triple a subterm runs at would be a statement the descent had leaked
-- into.
--
-- WHAT IS OWED, and it is three separate readings rather than one
-- arithmetic.  The μ guard is the easy one: `syncSizeᵉ` is strictly
-- monotone on subterms, so an unfolded body is strictly under its own
-- redex and the entry seeds the whole program's reading.  The connect
-- guard is the next: a connect moves one shared slot out of the
-- unconnected count and nothing puts one back, so the count the entry
-- seeds bounds the connects any run can make.  THE RANK GUARD IS THE
-- OPEN ONE — the claim that an emitted inner's nesting is strictly
-- under its emitter's — and it is this development's nesting face
-- restated at the one place it is actually spent.
------------------------------------------------------------------
module Verify-Rank-Sufficient where

open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Fuel)
open import Rx.Exp   using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (evaluate; hasDry)

-- WHAT EACH READING ACTUALLY COSTS, which is what to know before picking
-- this row up, because the three are not three grinds of one size.  TWO OF
-- THEM ARE ONE LINE over a fact already proven, and the evaluator's own
-- guard is the statement: the μ peel wants `syncSizeᵉ (unfoldμ body)` under
-- the size it entered at, which is `ltS` applied to an unfold equation; the
-- connect peel wants the unconnected count to drop when a fresh share joins
-- the connected list, which is `ltU` applied to an insertion lemma, under a
-- freshness premise the machine establishes for itself before the clause
-- fires.  THE RANK PEEL'S OWN ≺-WITNESS IS `ltR` APPLIED TO ITS HYPOTHESIS
-- AND SO SAYS NOTHING — every gram of that reading is establishing the
-- hypothesis, and that asymmetry is the whole schedule of this tier.

-- SO THE RISK IS ONE HYPOTHESIS, AND THAT IS A FINDING ABOUT THIS STATEMENT
-- RATHER THAN A PLAN FOR IT.  Of the three peels only the rank one asks
-- what a RUN did.  The μ peel reads its own body — an equation on syntax.
-- The connect peel reads the slot telescope and the connected list, and the
-- telescope is unchanged across a run, so its premise is an equation too
-- rather than an invariant something must preserve.  NOTHING HERE IS
-- CIRCULAR, which was the standing doubt against replacing a counter with
-- an order: neither settled peel needs the descent to have gone well in
-- order to say that its own edge drops.
--
-- What both DO need is the entry invariant — that the triple the evaluator
-- stands at is the READING OF THE TERM it is about to subscribe, seeded at
-- the root and re-seeded at a connect.  That is the motive to state first,
-- and the two settled peels are its cheap arms.

-- THE RANK READING, AND ITS SHAPE IS A STRENGTHENING RATHER THAN A MEASURE.
-- The inner is a runtime VALUE — an observable a sibling call emitted —
-- structurally unrelated to the term the caller was subscribing, so no
-- equation on syntax reaches it.  What does reach it is where it came FROM:
-- it rode a burst some subscribe produced, so its nesting can travel as a
-- STRENGTHENED RETURN TYPE on the burst-producing functions, invariant in
-- the motive, rather than as a fourth measure nobody has.  Ordinary
-- induction; the thing to get right is the strengthening, not arithmetic.
--
-- AND THE SEED IS EXPONENTIAL IN PROGRAM SIZE, WHICH IS THE PART NO
-- RECOVERED APPARATUS HANDS OVER.  This machine seeds the rank at
-- `2 ^ (sizeᵉ e + slotsSize sl)`, re-seeds it at `2 ^ sizeᵉ d` on a
-- connect, and peels ONE per nesting hop, so the conclusion owed is that
-- the count is never spent — not a comparison.  The generation that
-- measured nesting before this one carried a hop DEPTH under its own cap,
-- a different currency answering a different question, so its rows are a
-- lead to read rather than a statement to cite.
--
-- THE OTHER RECURSIONS OWE NOTHING AND THAT IS ALREADY WRITTEN DOWN, at the
-- descent discipline in `Rx.Evaluator` for the routes that hold the witness
-- fixed, and at `dispatchShare` for the cascade counter, whose real order is
-- the telescope position and whose premise a shared slot carries in its own
-- type.  Neither needs anything from here.

-- THE RANDOM SWEEP REACHES THE REGION, and that is a number rather than a
-- claim.  `QuickCheck` emits `μᵉ`, `varᵉ` and `deferᵉ` with the binder scopes
-- carried as INDICES, so a synchronous self-reference is not a program it can
-- write down and be rejected for; and its recursion is linear by grammar,
-- since a body reading its own var twice respawns per tick and real rxjs hangs
-- on that program too.  Every case reads `hasDry` off the run, which is this
-- statement instantiated rather than a proxy for it.  Twenty seeds at depth
-- four and five at depth five — 4500 programs, a third of them carrying a live
-- recursion — report no dry run.  IT IS MEASURED, NOT RECHECKED: a compiled
-- binary's row discharges nothing here, and what it buys is the coverage
-- doubt, which was that the three peels had been reached only at shapes one
-- author chose.

-- TWO OF THE THREE GUARDS HAVE THEIR CURRENCY ALREADY PROVEN, and it is
-- deleted rather than absent — a different starting position from the one
-- this row's class describes, and the class is still right, because a
-- measure is not an instantiation.  What is recoverable is postulate-free
-- and, for the μ guard, stated in this evaluator's own order rather than in
-- the grant the tower spent it on, so it transports as a CLAIM and not
-- merely as a harness.  The `≺` it is stated over is the live one,
-- constructor for constructor, and both settled edges are there in that
-- form.  WHAT DOES NOT TRANSPORT IS THE FLATTENING — a fold of the triple
-- into one ℕ, which existed so a counter could dominate the order
-- structurally; this evaluator descends on the order itself, so the fold
-- and every cap that fed it are apparatus for a machine that is gone.
-- None of it needs this header to be FOUND:
-- the sha is in `scripts/attic.txt`, so `make find` and `make find-prose`
-- already reach the statements and the dead routes on their own.
--
-- PROBED: `Probed.Descent` — twelve recursive programs, every one green, and
--   they are the first rows ever run against this statement.  What they cover,
--   guard by guard: the μ peel at every program, since all twelve are `μᵉ`;
--   the connect peel at the five carrying a slot, `shared` and `scripted`
--   both, one of them a diamond reaching the share twice in an instant; and
--   the RANK peel at the recursive self-reference, which is an emitted inner
--   that unfolds to its own emitter, at μ nested directly in μ, and at a share
--   holding a recursion — the shape whose nesting the guard cannot read off
--   the term it compares.  Each row pins its run's EVENT COUNT beside it, so
--   none is `false` by an empty stream.  THE BOUNDARY: one fuel, hand-written
--   programs, μ nested two deep and no deeper.  These rows are `refl` pins and
--   buy exactly the twelve shapes they name, which is why the coverage past
--   them is bought by an instrument that is not a pin.
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Measures.agda`
--   restores BOTH settled readings, each postulate-free.  The μ guard's:
--   `unfoldμ-shrinks` is two lines over `syncSize-unfoldμ`, which is one line
--   over a `syncSize-elimG` whose clauses run over the constructors this
--   `Exp` still has.  The connect guard's: `unconn-insert` drops the count
--   when a fresh share joins, taking exactly the slot equation and the
--   freshness the clause already tests.  The sibling `Wet/Part6.agda` then
--   carries `mu-edge≺` and `connect-edge≺`, one line each, which are those
--   two facts under `ltS` and `ltU` — the guards' obligations verbatim.  Its
--   `hop-edge≺` is `ltR` handed its own hypothesis and buys nothing.
-- RECOVERY: `git show 919f115:agda/src/Rx/Layer-Count.agda` restores a
--   payload-blind layer count and a μ depth, BOTH POSTULATE-FREE, whose two
--   unfold equations are the rank guard's currency proven at the operation
--   the guard is about: the layer count is INVARIANT under `unfoldμ`, and
--   the μ depth drops exactly one.  A measure surviving the unfold is the
--   half of a nesting descent that is not bookkeeping.
-- RECOVERY: `git show 919f115:agda/src/Rx/Clos-Size.agda` restores
--   `syncSizeᵉ` with the slot telescope substituted in, also postulate-free
--   — the μ guard reads the UNSUBSTITUTED size, and a slot reference is one
--   symbol standing for a definition of any size, so this is where that gap
--   was already measured.
postulate
  rank-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false
