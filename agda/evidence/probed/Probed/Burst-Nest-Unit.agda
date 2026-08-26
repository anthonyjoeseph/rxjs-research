-- THE SUBSCRIBE FRAME'S NESTING RECEIPT, INSTANTIATED -- and the point
-- is that it did not need the seal opened.  The grant at instant one is
-- `nestFacAt` times the rest, and `nestFacAt` is written over
-- `nestBurstAt`, which the seal exports no equation for; so the cap
-- cannot be transcribed into numerals and a direct row is impossible.
-- What the seal DOES export is a floor: the cap at instant zero is the
-- program's own unit, and the step lemma carries that under the cap at
-- instant one with the factor unexamined.  So a row pinning the store's
-- nesting under `nestUnit` -- entirely unsealed, entirely computable --
-- lifts through the exported introduction to the target's OWN
-- conclusion, at these programs, as a checked proof rather than a
-- numeral.
--
-- DEGENERATE ON THE FACTOR, and deliberately so: no row here can fail
-- by `nestFacAt` being too small, because none of them reads it.  What
-- they can fail by is the store outgrowing the unit inside a single
-- subscribe frame, which is the whole question at this instant, and
-- which the wrap corpus below makes the descent actually work for.
--
-- TARGET: burst-nest
module Probed.Burst-Nest-Unit where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m+n; ≤ᵇ⇒≤)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Decide using (T-to)

open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (subscribeE; root; sched-init; st-init; budgetAt; Sched; EvalSt)
open import Rx.Nest-Depth using ()

open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; nestUnit; nestCapAt; nestCapAt-0; nestCap-mono;
         nestOK?; nestOK?-intro)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

pM : ℕ → Closed Γ₂ (obs natᵗ)
pM k = mergeAllᵉ (just 1) (wrapped k)

pS : ℕ → Closed Γ₂ (obs natᵗ)
pS k = switchAllᵉ (wrapped k)

pX : ℕ → Closed Γ₂ (obs natᵗ)
pX k = exhaustAllᵉ (wrapped k)

-- THE FLOOR, spelled once: the unit sits under the instant-one cap
-- whatever the factor is, because the factor is at least one and the
-- increment is a summand.
unit≤cap : ∀ {t} (e : Closed Γ₂ t) →
  nestUnit e slots ≤ nestCapAt e slots 1
unit≤cap e =
  ≤-trans (≤-reflexive (sym (nestCapAt-0 e slots)))
          (≤-trans (m≤m+n _ _) (nestCap-mono e slots 0))

-- what the descent actually leaves behind, at the gas the target uses
schedOf : ∀ {t} (e : Closed Γ₂ t) → Sched Γ₂
schedOf e = proj₁ (proj₂ (subscribeE (budgetAt e slots 0) e root 0 0
                                     (sched-init e slots) (st-init e)))

stOf : ∀ {t} (e : Closed Γ₂ t) → EvalSt e
stOf e = proj₂ (proj₂ (subscribeE (budgetAt e slots 0) e root 0 0
                                  (sched-init e slots) (st-init e)))

storeOf : ∀ {t} (e : Closed Γ₂ t) → ℕ
storeOf e = storeNestMax (schedOf e) (stOf e)

-- LOAD-BEARING: the store's nesting against the program's own unit.  A
-- program whose frame installs something deeper than its unit fails
-- here, and that is a near miss worth reporting rather than a
-- refutation, since the factor above would still have to be spent.
storeM≡ : ℕ
storeM≡ = storeOf (pM 2)

storeS≡ : ℕ
storeS≡ = storeOf (pS 2)

storeX≡ : ℕ
storeX≡ = storeOf (pX 2)

unitM : ℕ
unitM = nestUnit (pM 2) slots

-- packed base-1000 so one build returns every figure: Agda aborts a
-- module at its first mismatch, so a tuple of pins leaks one number per
-- build and a sum leaks all of them at once
figures : ℕ
figures = storeM≡ + 1000 * storeS≡ + 1000000 * storeX≡ + 1000000000 * unitM

-- the store reads one at every head and the unit is five, so the floor
-- clears with room -- and the room is what says the factor is not being
-- leaned on
figures≡ : figures ≡ 5001001001
figures≡ = refl

-- AND THE LIFT, which is the whole point of the floor: each row above
-- is a `≤ᵇ` at numerals, and the exported introduction turns it into
-- the target's own conclusion at that program.
fit : ∀ {t} (e : Closed Γ₂ t) → Set
fit e = (storeOf e ≤ᵇ nestUnit e slots) ≡ true

ok : ∀ {t} (e : Closed Γ₂ t) → fit e →
  nestOK? e slots 1 (schedOf e) (stOf e) ≡ true
ok e h =
  nestOK?-intro e slots 1 (schedOf e) (stOf e)
    (≤-trans (≤ᵇ⇒≤ (storeOf e) (nestUnit e slots) (T-to h)) (unit≤cap e))

okM : nestOK? (pM 2) slots 1 (schedOf (pM 2)) (stOf (pM 2)) ≡ true
okM = ok (pM 2) refl

okS : nestOK? (pS 2) slots 1 (schedOf (pS 2)) (stOf (pS 2)) ≡ true
okS = ok (pS 2) refl

okX : nestOK? (pX 2) slots 1 (schedOf (pX 2)) (stOf (pX 2)) ≡ true
okX = ok (pX 2) refl
