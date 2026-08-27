-- ══════════════════════════════════════════════════════════════════
-- THE RESTATED SLOT ARM, AT THE FAMILY THAT KILLED THE OLD ONE.
--
-- `Refuted.Shared-Slot-Nest-Arr` refuted the additive grant at a
-- four-layer SUBSTITUTING definition: delivered `1 2 4 8` against a
-- grant of `2 3 4 5`.  The arm is now keyed on the slot's CLOSURE --
-- one more than the definition's own size with the telescope
-- substituted in -- and these rows are that same family read against
-- the new key.
--
-- WHAT WOULD MAKE THEM FAIL, since a row that could not fail is not a
-- row: the closure key buys a factor of two per unit of the
-- DEFINITION's size, and the delivery doubles per LAYER.  A layer that
-- doubled without enlarging the definition would outrun it, and the
-- fourth row is where the additive form was already dead.  Both
-- columns are pinned, so the margin is visible rather than asserted.
--
-- COVERED, LOAD-BEARING: the value conjunct of the arm at the
-- substituting family, layers zero to three, and at the CONTAINED
-- family over the same layers.  NOT covered: the two store conjuncts,
-- which this shape leaves at `0 ≤ _`.  The telescope here has ONE
-- entry, so the staged environment is never consulted; the two-slot
-- reading is `Probed.Shared-Slot-Telescope`.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: sharedConnect-nest-arr @094c83
module Probed.Shared-Slot-Clos-Key where

open import Data.Bool using (T; true)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (sharedConnect; splitBurst; root; sched-init; st-init; Path; _↠_;
  thru-outer; mergeAllᵒ)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))

prog : Closed Γₛ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

deep : ℕ → Closed Γₛ natᵗ
deep zero    = ofᵉ (nat̂ 0 ∷ [])
deep (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

dDeep : ℕ → Closed Γₛ (obs natᵗ)
dDeep k = ofᵉ (strmᵗ (deep k) ∷ [])

dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

κ : Path Γₛ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

burstOf : (d : Closed Γₛ (obs natᵗ)) (ok : T (inputsBelowᵉ 0 d)) → ℕ
burstOf d ok =
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γₛ natᵗ}
    (proj₁ (sharedConnect gasBig fzero d κ 0 0
              (sched-init prog (sl d ok)) (st-init prog)))))

-- the RESTATED grant: keyed on the definition's closure, at the `B`
-- the head hands down, which is zero
GOf : (d : Closed Γₛ (obs natᵗ)) (ok : T (inputsBelowᵉ 0 d)) → ℕ
GOf d ok = arrD (nestUnit prog (sl d ok)) (nestUnit prog (sl d ok))
             (closSizeᵉ (slotClos (sl d ok)) d)

-- THE KEY ITSELF, packed base 100: the four substituting layers cost
-- 11 26 41 56, one more than the closure at each, so the exponent
-- grows by fifteen per doubling
keys : ℕ
keys = suc (closSizeᵉ (slotClos (sl (dDup 0) tt)) (dDup 0))
     + 100 * suc (closSizeᵉ (slotClos (sl (dDup 1) tt)) (dDup 1))
     + 10000 * suc (closSizeᵉ (slotClos (sl (dDup 2) tt)) (dDup 2))
     + 1000000 * suc (closSizeᵉ (slotClos (sl (dDup 3) tt)) (dDup 3))

keys≡ : keys ≡ 56412611
keys≡ = refl

-- AND THE CONJUNCT, at every layer of both families
fitDup0 : (burstOf (dDup 0) tt ≤ᵇ GOf (dDup 0) tt) ≡ true
fitDup0 = refl

fitDup1 : (burstOf (dDup 1) tt ≤ᵇ GOf (dDup 1) tt) ≡ true
fitDup1 = refl

fitDup2 : (burstOf (dDup 2) tt ≤ᵇ GOf (dDup 2) tt) ≡ true
fitDup2 = refl

fitDup3 : (burstOf (dDup 3) tt ≤ᵇ GOf (dDup 3) tt) ≡ true
fitDup3 = refl

fitDeep3 : (burstOf (dDeep 3) tt ≤ᵇ GOf (dDeep 3) tt) ≡ true
fitDeep3 = refl
