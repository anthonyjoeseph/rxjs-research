-- THE SPLIT AT THE ROW'S OWN BUDGET, ON THE FAMILY WHERE THE RIGHT
-- SUMMAND IS LOAD-BEARING.  Two probes already stand under this target
-- and neither can reach this point.  One runs a wrap corpus at the
-- row's own gas, but on programs whose LEFT summand alone pays, so it
-- spends the right one nowhere and says so.  The other drives the
-- registry past the unit -- which is what makes the sum the weakest
-- surviving reading -- but at padded gas, so what it covers is the
-- shape of the climb and not any margin.  This file crosses them: the
-- carrying fold with a carrying map above it, at `budgetAt e ins 0`.
-- That is the one point where both summands are spent AND the budget
-- is the target's own.
--
-- WHY THAT BUDGET IS REACHABLE AT ALL, since what it is built from
-- carries a standing dead route against probing it.  `budgetAt` is a
-- PAD over a tower, `Gas` is unary, and `gasPad` hands its tail on
-- unforced -- so a run that finishes inside the pad never forces the
-- height, and the height is the whole of the blowup.  The pad is a
-- power of two in the program's own size, which is a numeral here.
-- The seal therefore costs this file nothing, and the failure mode is
-- safe in the direction that matters: a run OUTLIVING its pad would
-- fail to typecheck rather than read a smaller answer.  The rows
-- MEASURE that rather than assuming it: every figure below is the one
-- the same corpus reads at `gasPad 400 g0`, so these runs finish
-- inside the pad and the height is never reached.
--
-- WHAT THE MARGIN ROW IS FOR.  The `Confirms` row says the claim held
-- at this point and no more; the figures say by how much, and by how
-- much is the entire question the leg asks, because a sum that clears
-- by nothing at the row's own gas is a sum with no room to lose when
-- the bound is later widened at a consumer.  The two summands are
-- reported apart for the same reason -- a total that clears tells you
-- nothing about which half was carrying it.
--
-- NOT COVERED: retirement, since this family keeps every registration
-- it makes and that is exactly why it is the family that separates; a
-- registration minted anywhere but a delivery or the walk's own
-- descent; and any instant but the subscribe frame, the budget being
-- read at zero.
-- TARGET: burst-regs-split @e95363
module Probed.Regs-Split-Budget where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; _+_; _*_; _≤ᵇ_; _∸_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Decide using (T-to)
open import Probed.Apparatus using (Confirms)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Evaluator
  using (subscribeE; root; sched-init; st-init; budgetAt; EvalSt)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nestUnit)
open import Verify-Budget-Sufficient.Caps-Bridge using (burst-regs-split)
open import Refuted.Reg-Nest-Reached using (Γ₂; slots)
open import Probed.Regs-Store-Currency using (nodesN; prog1; prog3)

-- the run the TARGET is stated over, letter for letter: the row's own
-- budget at instant zero, from the initial schedule and state
atBudget : (e : Closed Γ₂ natᵗ) → EvalSt e
atBudget e = proj₂ (proj₂ (subscribeE (budgetAt e (slots 5) 0) e root 0 0
                             (sched-init e (slots 5)) (st-init e)))

regsB : Closed Γ₂ natᵗ → ℕ
regsB e = regsNestMax (EvalSt.registry (atBudget e))

------------------------------------------------------------------
-- THE FIGURES, base one hundred and least significant first: at each
-- of the two composed programs, the registry, then the two summands
-- apart -- the node table the delivered half is read off, and the
-- program's own unit.
------------------------------------------------------------------

pack : List ℕ → ℕ
pack = foldr (λ x acc → x + 100 * acc) 0

figures : ℕ
figures = pack ( regsB prog1
               ∷ nodesN (atBudget prog1)
               ∷ nestUnit prog1 (slots 5)
               ∷ regsB prog3
               ∷ nodesN (atBudget prog3)
               ∷ nestUnit prog3 (slots 5)
               ∷ [])

figures≡ : figures ≡ 70608050606
figures≡ = refl

-- THE MARGIN ITSELF, which is what padded gas could not report: the
-- sum less the registry, at each program.  LOAD-BEARING -- a zero here
-- is a sum clearing by nothing at the gas the target names, which is a
-- finding about the statement rather than about the run.
margins : ℕ
margins = pack ( (nestUnit prog1 (slots 5) + nodesN (atBudget prog1)) ∸ regsB prog1
               ∷ (nestUnit prog3 (slots 5) + nodesN (atBudget prog3)) ∸ regsB prog3
               ∷ [])

margins≡ : margins ≡ 505
margins≡ = refl

-- AND THE JOIN STILL DIES HERE, which is what says the budget did not
-- quietly make the weaker reading work: LOAD-BEARING at the composed
-- program, where the sum holds and the maximum of the two summands
-- does not.
joinAtBudget : Bool
joinAtBudget = regsB prog3 ≤ᵇ nestUnit prog3 (slots 5)

sumAtBudget : Bool
sumAtBudget = regsB prog3 ≤ᵇ nestUnit prog3 (slots 5) + nodesN (atBudget prog3)

verdicts : List Bool
verdicts = joinAtBudget ∷ sumAtBudget ∷ []

verdicts≡ : verdicts ≡ false ∷ true ∷ []
verdicts≡ = refl

------------------------------------------------------------------
-- THE TARGET AT THIS POINT, generated by Agda from the statement as it
-- reads.  The body spends the decidable reading above and nothing
-- else, so the row stands on a stdlib inequality rather than on the
-- statement it is evidence about.
------------------------------------------------------------------

confirm1 : Confirms (burst-regs-split prog1 (slots 5))
confirm1 = ≤ᵇ⇒≤ _ _ (T-to refl)

confirm3 : Confirms (burst-regs-split prog3 (slots 5))
confirm3 = ≤ᵇ⇒≤ _ _ (T-to refl)
