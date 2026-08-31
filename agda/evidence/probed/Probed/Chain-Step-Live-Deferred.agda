-- ══════════════════════════════════════════════════════════════════
-- THE LIVE ARM, AT THE ONLY SHAPE THAT CAN MOVE IT — AND REACHED BY
-- RUNNING RATHER THAN BY BUILDING THE PATH.
--
-- TARGET: chainStep-nest-liveC @358ade
--
-- WHY THIS PROGRAM.  A live source's nesting is the nesting of its
-- PENDING values, and the evaluator mints a live carrying a nested
-- value in one clause only: subscribing a `deferᵉ`, whose pending entry
-- is the body at observable type.  A scripted slot cannot deliver one,
-- since scripts are data-typed by construction, so the body has to be
-- produced by the program mid-chain.  `progL` does exactly that: a
-- `mapᵉ` over the async input hands the outer *All a deferred nest per
-- arrival, so the chain the evaluator presents subscribes it and the
-- fold moves.  Every other family here reads zero on both sides, which
-- is a fact about their syntax and not about the arm.
--
-- WHAT IS LOAD-BEARING.  The left side is the evaluator's own live fold
-- after a real `chainStep`, the right names the program and the slot
-- vocabulary alone, and the depth axis is swept — the fold moves with
-- the nest and the charge moves with the syntax, so the ordering is a
-- race between two growing quantities rather than a constant against
-- zero.  Both sides are pinned before the ordering is taken.  The
-- charge is the syntactic surrogate the tree proves the arms' increment
-- dominates, so green here implies the arm at this program and red here
-- does not refute it.
-- ══════════════════════════════════════════════════════════════════
module Probed.Chain-Step-Live-Deferred where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; foldr)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Exp; natᵗ; sizeᵉ; syncSizeᵉ; ofᵉ; mapᵉ; mergeAllᵉ;
         switchAllᵉ; deferᵉ; strmᵗ; nat̂; input)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next; cascadeLatch; chainStep;
  chainsOf)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Nest-Store using (liveNest; nestUnit)
open import Refuted.Demand-Programs using (Γ₂; insF)

slots : Slots Γ₂
slots = insF 1 1 2

-- a nest the depth measure reads all the way down
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE 0       = ofᵉ (nat̂ 0 ∷ [])
deepE (suc m) = switchAllᵉ (ofᵉ (strmᵗ (deepE m) ∷ []))

-- one deferred nest per arrival on the async input
progL : ℕ → Closed Γ₂ natᵗ
progL m = mergeAllᵉ nothing (mapᵉ (strmᵗ (deferᵉ (deepE m))) (input (fsuc fzero)))

sucGL : ℕ → ℕ
sucGL m = suc (syncSizeᵉ (progL m) + hopDᵉ 0 (slotHop 0 slots) (progL m))

sub : (m : ℕ) → Sched Γ₂ × EvalSt (progL m)
sub m = let r = subscribeE (gasPad (sucGL m) g0) (progL m) root 0 0
                           (sched-init (progL m) slots) (st-init (progL m))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

charge : ℕ → ℕ
charge m = nestUnit (progL m) slots + (2 + sizeᵉ (progL m))

-- the fold before and after the first chain of the first arrival's
-- cascade, taken off states the evaluator reached
row : (m : ℕ) → ℕ × ℕ
row m with sched-next (proj₁ (sub m))
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub m))
...   | []            = 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub m))
            r   = chainStep 1 a c sd st₀
        in liveMax sd , liveMax (proj₁ (proj₂ r))

packed : ℕ
packed = proj₁ (row 1) + 100 * proj₂ (row 1) + 10000 * charge 1
       + 1000000 * proj₁ (row 3) + 100000000 * proj₂ (row 3)
       + 10000000000 * charge 3

figures≡ : packed ≡ 260300180100
figures≡ = refl

fits : (proj₂ (row 1) ≤ᵇ proj₁ (row 1) ⊔ charge 1)
     ∧ (proj₂ (row 3) ≤ᵇ proj₁ (row 3) ⊔ charge 3) ≡ true
fits = refl
