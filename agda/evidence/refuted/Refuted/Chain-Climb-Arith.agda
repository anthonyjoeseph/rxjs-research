-- ══════════════════════════════════════════════════════════════════
-- THE CHAIN DOOR'S CLIMB PRICE IS FALSE AS ARITHMETIC, AND NO STATE
-- ENTERS IT.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  The door prices one chain's level climb at
-- a rung per frame: a free `L′`, an upper bound on it from the caps
-- ladder, and a conclusion bounding it by the path length times the
-- per-frame charge.  `L′` occurs in exactly two places -- that upper
-- bound and the conclusion -- and the state predicate beside them does
-- not mention it at all.  So the statement holds only if the ladder's
-- own ceiling is already under the per-frame product, and that is a
-- question about two closed functions of numbers.
--
-- WHERE IT BREAKS.  It is not under it, and the direction that decides
-- it is a LOWER bound on the ceiling rather than a tighter upper bound
-- on the climb.  One `dLvl` rung provably dominates a fold tower of
-- any height the size cap admits, and a fold tower squares per storey
-- while the per-frame charge is quadratic in the cap and linear in the
-- path.  Two storeys already put the ceiling past every path a program
-- can have.
--
-- AND EVERY PARAMETER IS TAKEN AT THE VALUE THAT FAVOURS THE
-- STATEMENT, which is what makes the row say something about the
-- postulate rather than about a chosen instance.  The cap sits at the
-- floor the caps package forces, the width at one, the depth fuel at
-- zero and the delivery count at one -- each of them a value that
-- SHRINKS the ceiling, since the ladder is monotone in all four.  The
-- only parameter left free is the path length, and the second row
-- takes it to a million.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Climb-Arith where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Evaluator using (lvls; dLvl; iterFold)
open import Verify-Budget-Sufficient.Fold-Room using (fold≤dLvl)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (frameCh)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  It is the door's
-- climb price with the state predicate dropped and the path replaced
-- by its LENGTH, which is the only thing the conclusion reads off it.
-- Dropping the predicate makes this the STRONGER statement, so the
-- refutation is correspondingly weaker -- what remains is recorded
-- below the witnesses.
----------------------------------------------------------------------
ChainClimbArith : Set
ChainClimbArith = ∀ (S W H Lc L′ D P : ℕ) → 8 ≤ S → 1 ≤ W →
  Lc + L′ ≤ lvls S W H Lc (suc D) →
  L′ ≤ suc P * frameCh S S

----------------------------------------------------------------------
-- THE FIGURES THE FIRST ROW TURNS ON: two fold storeys at the cap
-- floor and a width of four, the per-frame charge that cap buys, and
-- what a path of eight frames may spend of it.
----------------------------------------------------------------------
figures : List ℕ
figures = iterFold 8 1 4 ∷ frameCh 8 8 ∷ suc 8 * frameCh 8 8 ∷ []

figures≡ : figures ≡ 32768 ∷ 72 ∷ 648 ∷ []
figures≡ = refl

-- LOAD-BEARING: the ceiling genuinely admits the climb the conclusion
-- forbids, and it is a PROVEN lemma that puts it there rather than a
-- computed rung -- the ladder itself is a tower and never reduces.
-- It would fail for a `k` the size cap does not admit.
ceil₁ : iterFold 8 1 4 ≤ dLvl 8 4 0 0
ceil₁ = fold≤dLvl 8 4 0 0 1 (s≤s (s≤s z≤n)) (s≤s z≤n)

chain-climb-arith-absurd : ChainClimbArith → ⊥
chain-climb-arith-absurd pr =
  ≤⇒≤ᵇ (pr 8 4 0 0 32768 0 8 ≤-refl (s≤s z≤n) ceil₁)

----------------------------------------------------------------------
-- AND NO PATH LENGTH REPAIRS IT, which is the row that makes the first
-- one a statement about the postulate.  Every parameter now sits at
-- its floor -- the width at one too -- and one more fold storey puts
-- the ceiling past a path of a million frames.  The gap is not a
-- constant to be absorbed: a storey SQUARES while the charge is linear
-- in the path.
----------------------------------------------------------------------
ceil₂ : iterFold 8 2 1 ≤ dLvl 8 1 0 0
ceil₂ = fold≤dLvl 8 1 0 0 2 (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n))

-- LOAD-BEARING: the crossing is decided by computation on both sides,
-- so nothing here rests on the ladder normalising.  It would be `true`
-- for a ceiling one storey lower.
gap₂ : (iterFold 8 2 1 ≤ᵇ suc 1000000 * frameCh 8 8) ≡ false
gap₂ = refl

chain-climb-arith-wide-absurd : ChainClimbArith → ⊥
chain-climb-arith-wide-absurd pr =
  ≤⇒≤ᵇ (pr 8 1 0 0 (iterFold 8 2 1) 0 1000000 ≤-refl (s≤s z≤n) ceil₂)

----------------------------------------------------------------------
-- WHAT THIS DOES NOT SHOW.  It does not exhibit the state predicate at
-- these numbers, so what is refuted is the door's price standing free
-- of it.  The gap that leaves is narrow and nameable: the predicate
-- would have to force the path length above the ceiling itself, since
-- it cannot touch the climb variable -- which it does not mention --
-- and the three ladder parameters are already at the floor it permits.
-- A path with more frames than the ceiling has units is not a path any
-- program has.
----------------------------------------------------------------------
