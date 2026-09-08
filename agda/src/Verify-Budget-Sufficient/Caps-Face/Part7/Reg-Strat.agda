-- Verify-Budget-Sufficient.Caps-Face.Part7.Reg-Strat
-- entStrat? … registry-entStrat
module Verify-Budget-Sufficient.Caps-Face.Part7.Reg-Strat where

open import Data.Bool using (Bool; true; _∧_; _∨_)
open import Data.Nat using (_≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Prim using (Source)
open import Rx.Evaluator using (Sched; EvalSt; Path)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathFloor; pathStrat?)
open import Verify-Budget-Sufficient.Delivery-Walk using (regQ?)

-- THE ONE READING BOTH ENTRY FACES WANT OF THE REGISTRY, and it is
-- stated at an entry rather than at a path because half of it is about
-- the REGISTRATION.  A chain's frames are stratified, and its floor is
-- at or above the source it listens to.  The second is what makes the
-- first usable at a fan: values leaving a slot are known below that
-- slot's index, and raising a floor only weakens that, so a
-- continuation floored at or above the source inherits them.
--
-- ONLY THE ORDERING IS GUARDED, and the asymmetry is the shape of the
-- statement rather than an economy.  The frame reading is asked of
-- every entry because nothing exempts a frame; the ordering is asked
-- only of sources the slot telescope reaches, because there is an arm
-- where it is false and the guard is what a carried conjunct already
-- pays for.
entStrat? : ∀ {n} {Γ : Ctx n} {u t} → Source → Path Γ u t → Bool
entStrat? {n = n} s p = ((n ≤ᵇ s) ∨ (s ≤ᵇ pathFloor p)) ∧ pathStrat? p

-- AND THE GUARD IS ON THE SOURCE, WHICH IS NOT WHERE IT SAT.  Guarding
-- on the PATH's floor instead -- exempting a chain that terminates at
-- `root`, and asking the ordering of every other -- makes this reading
-- FALSE, and the arm is written down in `regStrat?`'s own header rather
-- than merely possible: a cold slot subscribed from inside a share's
-- definition mints a fresh source, `srcFloor?` puts every minted source
-- at or above the slot count, and the continuation it registers ends at
-- the ENCLOSING share's sink, which is below it.  At such an entry a
-- root guard is false and the ordering is false under it, so nothing
-- can hold the conjunction.  On the source the same entry discharges
-- the disjunct outright, which is why that sibling can afford to state
-- the ordering at all.
--
-- WHAT THE FACES LOSE BY IT IS NOTHING, and that is the check that the
-- guard moved rather than the claim.  A source the fan admits IS a slot
-- index, so the guard is false there and the ordering arrives; the
-- cascade's face reads only the frame half and never meets the guard.

-- AND THE ORDERING HALF IS A SIBLING'S STATEMENT, NOT A NEW ONE.
-- `walk-share-strat` asks a registry-wide reading of the same registry
-- for the same purpose, out of the DISPATCH bundle rather than the caps
-- one, and its `sinkAbove?` is this ordering at a strict inequality.
-- The two differ in their receipt and in whether the frame half rides
-- along, so neither is today derivable from the other -- but they are
-- one fact about one list, and the merge is owed at whichever receipt
-- can be handed to both faces.

-- THE WALK CARRIES NO ABSTRACT LEDGER, SO THERE IS NOTHING HERE TO
-- GENERALISE.  The burst walk does thread a registry reading across
-- its steps, but it REBUILDS it entrywise at each one out of two
-- faces that exist for other reasons: the size half falls out of the
-- new `capsOK?`, because `regsSz?` IS that half of the reading, and
-- the Ψ half has its own per-step face.  The peel-and-glue pair
-- between them exists precisely because neither face hands back the
-- conjunction.  `entStrat?` has no half inside `capsOK?` and no
-- per-step face, so nothing recombines and abstracting that ledger
-- over an arbitrary predicate buys this statement nothing.
--
-- AND THE PRESERVATION IS THE CHEAP HALF; THE CARRIER IS NOT.  The
-- registry has exactly ONE growth site -- `register` appends a single
-- entry, and every other write in the evaluator is the empty initial
-- list or a FILTER, `cutThrough`'s kept list and `dropSource`, which
-- cannot break a reading of the shape `all`.  So this reading is free
-- at every step but the mint, and at the mint it asks exactly the
-- per-registration side condition the telescope pays at four of the
-- five sites.  What is missing is therefore not a proof but a
-- CARRIER: a reading nothing threads has to become a conjunct of the
-- state predicate, and seventy-six faces re-establish that predicate.
-- `srcFloor?` is the precedent rather than an analogy -- it names no
-- cap, it is the one conjunct `capsOK?-mono` hands straight back, and
-- it already crosses all of them.

-- WHAT IS OPEN, AND IT IS THE WHOLE OF WHAT THE TWO SITES USED TO ASK
-- SEPARATELY.  The telescope is what should supply this: a
-- sink-floored chain is registered by the CONNECT, which subscribes
-- the slot's def under `share-sink i`, so a frame the descent pushes
-- is a subterm of that def -- and `Rx.Slots.shared` admits a def only
-- with its inputs below the slot's own index, which is definitionally
-- what `frameStrat?` asks at the floor such a chain reports.  That
-- covers four of the five registration sites; the fifth subscribes an
-- observable that arrived as a VALUE, and `Val Γ (obs t)` is arbitrary
-- closed syntax the telescope never checked.
--
-- AND THE RECEIPT IS NOT ONE, WHICH IS A FACT RATHER THAN A DOUBT.
-- `capsOK?` prices the registry by LENGTH and by per-chain SIZE, and
-- reads no frame and no source, so it cannot separate a state the
-- evaluator built from one holding a chain that reads the very slot
-- its own sink sits at.  The caps are universally quantified, so a
-- counterexample picks them generous and both registry conjuncts fall
-- out at a one-entry registry.  What the statement below asserts is
-- therefore that a caps-legal state is a BUILT one, which no conjunct
-- of that reading says.
--
-- SO THE FACT IS OWED AT THE MINT, which is where the two siblings
-- this reading was to be handed to are already owed theirs.  The
-- repair is neither a weaker statement here nor a bigger cap: it is a
-- conjunct on the state predicate, obliging every producer, and
-- cascading it through the faces that re-establish that predicate is
-- the cost of the fact being true rather than a reason to avoid it.
--
-- REFUTED: `Refuted.Fan-Chain-Registry`, at a one-slot program whose
--   registration reads its own sink's slot.  The FRAME half is what
--   fails there, so the row stands wherever the guard sits and did
--   not die with the repair that moved it.
-- DEAD ROUTE: a free path quantified after the receipt cannot be
--   asked for at all, and the refutation of that form is recorded at
--   `cascade-admit-sink`'s own site -- which is why the subject here
--   is the registry the receipt is already about.
postulate
  registry-entStrat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    regQ? {t = t} (λ {u} → entStrat? {u = u}) (EvalSt.registry st) ≡ true
