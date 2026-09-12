-- THE DESCENT DOES GO DRY, AND THE AXIS THAT TAKES IT THERE IS THE ONE
-- THE READING IS BLIND TO.
--
-- `rank-sufficient` asserts that no run of any program emits the dry
-- marker.  It is false.  The witness is one run: four literals, one unit
-- of fuel, and a `close … dried` in the output.
--
-- WHY THIS FAMILY.  The sibling witness established that a burst's
-- deliveries are exponential in the source length while every additive
-- syntactic measure is linear in it, and concluded that the surviving
-- reading is the one parameterised by the store's own bound.  This
-- witness is the other half of that sentence, and it is the half nobody
-- instantiated: the store's bound is the FUEL, fuel counts ARRIVALS, and
-- the accumulator this family doubles is refolded once per DELIVERY.  So
-- the reading is parameterised by a quantity that does not bound what it
-- is spent on, and lengthening the source walks straight past it.
--
-- WHAT MAKES IT A CROSSING AND NOT A DEGENERATE ALLOWANCE.  A single row
-- would not say this, because the scan clause's allowance is a V-th
-- power and a small V makes it small for reasons of its own.  So the
-- rows come in pairs that move ONE axis each.  Lengthen the source at a
-- fixed bound and a dry-free run goes dry -- twice, at two different
-- bounds, and the length it crosses at MOVES with the bound.  Raise the
-- bound on a program that crossed and it is rescued -- twice, the same
-- two programs.  Together those say the guard is deciding on exactly the
-- quantity the premise is about, and that no fixed bound survives the
-- source growing, which is the claim: not that some run is dry, but that
-- for every allowance there is a program past it.
--
-- WHAT IT KILLS.  `k ≤ V` -- the premise that a scan refolds at most
-- store-bound times, argued from the accumulator being stored.  With it
-- goes the repair that reads as obvious from a single dry row, namely
-- conditioning the statement on a larger fuel: the rescue rows are the
-- ones that rule it out, since they show a bigger allowance fixes THAT
-- program while the crossing rows show a longer source defeats THAT
-- allowance.  What has to move is what the bound counts.
--
-- THE FAMILY IS THE SIBLING'S, IMPORTED RATHER THAN RE-TYPED, so a
-- repair that moves the programs moves both witnesses together and
-- neither can drift into being evidence about a different fold.
--
-- THE ROWS ARE `hasDry` AND `evaluate` THEMSELVES, so there is no
-- measure here to localise: the currency refuted is the refuted
-- statement's own, verbatim.
module Refuted.Rank-Cross where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Prim using (Fuel)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (evaluate; hasDry)

open import Refuted.Sync-Count using (ins₀; prog₁; prog₂; prog₃; prog₄)

----------------------------------------------------------------------
-- THE STATEMENT, quoted rather than imported: `src` states this as a
-- postulate, and a refutation that named it would be asserting it.
----------------------------------------------------------------------

RankSufficient : Set
RankSufficient = ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
                 (ins : Slots Γ) → hasDry (evaluate fuel e ins) ≡ false

----------------------------------------------------------------------
-- THE ROWS.  Each is LOAD-BEARING and each could have gone the other
-- way.  Read them as two pairs plus their controls: within a bound,
-- lengthening the source crosses; within a program, raising the bound
-- rescues.  The dry-free rows are what make the dry ones mean
-- something -- a family that was dry at every length would be a broken
-- program rather than a crossing.
----------------------------------------------------------------------

-- BOUND ZERO: the allowance is a zeroth power, so one refold is all
-- there is.  One literal survives it; two do not.
_ : hasDry (evaluate 0 prog₁ ins₀) ≡ false
_ = refl

_ : hasDry (evaluate 0 prog₂ ins₀) ≡ true
_ = refl

-- BOUND ONE RESCUES THE PROGRAM THAT JUST CROSSED, which is what says
-- the guard was deciding on the allowance and not on the program.
_ : hasDry (evaluate 1 prog₂ ins₀) ≡ false
_ = refl

-- AND THEN THE SAME CROSSING HAPPENS AGAIN, one literal further out.
-- Three still fits; four does not.
_ : hasDry (evaluate 1 prog₃ ins₀) ≡ false
_ = refl

row₁₄ : hasDry (evaluate 1 prog₄ ins₀) ≡ true
row₁₄ = refl

-- AND IS RESCUED AGAIN.  Two rescues and two crossings: the pattern is
-- the allowance racing the source, and the source is free.
_ : hasDry (evaluate 2 prog₄ ins₀) ≡ false
_ = refl

----------------------------------------------------------------------
-- THE ⊥, spent at the second crossing.  Any of the two would do; this
-- one is taken at an ordinary fuel rather than at zero, so nothing here
-- rests on the degenerate bound.
----------------------------------------------------------------------

rank-sufficient-false : RankSufficient → ⊥
rank-sufficient-false h = cross row₁₄ (h 1 prog₄ ins₀)
  where
    cross : ∀ {b : Bool} → b ≡ true → b ≡ false → ⊥
    cross refl ()

----------------------------------------------------------------------
-- WHAT IS NOT COVERED, and it is the honest boundary.  The crossing is
-- exhibited at two bounds only.  A third would cost a doubling of the
-- run -- the delivery count is 2, 6, 14, 30 along this family, and the
-- length that crosses grows with the bound -- so the general claim,
-- that EVERY bound is crossed by some length, is an extrapolation from
-- two instances and their four controls, not a row here.  What the rows
-- do establish without extrapolation is that no run-independent reading
-- of the fuel is the right allowance, which is what the premise needed.
--
-- The flattening axis is not swept either: the root is a merge in every
-- row, so nothing here says which registry clause carries the crossing.
----------------------------------------------------------------------
