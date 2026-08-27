-- ══════════════════════════════════════════════════════════════════
-- THE SCAN HEAD OF THE ARRIVAL-KEYED WALK, INSTANTIATED.
--
-- The row it serves is the last tier-1 statement with nothing under
-- it: a scan REFOLDS its accumulator once per value of the burst it
-- is handed, so the delivered nesting carries a term in the burst's
-- LENGTH, while `arrD` is keyed on the arrival's own syntax and has
-- no such term.  The statement deliberately carries no width premise.
--
-- WHY THE LENGTH IS NOT BOUNDED BY THE SYNTAX, which is what makes
-- this worth instantiating rather than reasoning about: one instant
-- can emit more values than the sync measure allows -- the doubling
-- scan below emits `2^(K+1) - 2` values against a measure linear in
-- K, and `Rx.Exp`'s own header records the refutation of the bound
-- that said otherwise.  So the two sides genuinely race.
--
-- WHAT WOULD MAKE THESE ROWS FAIL: a delivered nesting above the
-- grant at the same program.  Both columns are pinned, so the margin
-- is read rather than asserted.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeE-nest-arr-scan
module Probed.Scan-Arr-Key where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; Tm; natᵗ; obs; _×ᵗ_; ofᵉ; mergeAllᵉ; scanᵉ;
         nat̂; strmᵗ; varᵗ; fstᵗ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

-- the doubling step: the accumulator lands TWICE under one merge, so
-- each folded value adds a level and doubles the emission
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                             fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

-- k literal values in one instant, so the fold runs k times there
vals : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
vals 0       = []
vals (suc k) = nat̂ 0 ∷ vals k

src : ℕ → Closed Γ₀ natᵗ
src k = ofᵉ (vals k)

arr : ℕ → Closed Γ₀ (obs natᵗ)
arr k = scanᵉ step liveSeed (src k)

prog : Closed Γ₀ (obs natᵗ)
prog = arr 1

burst : ℕ → ℕ
burst k =
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₀ (obs natᵗ)}
    (proj₁ (subscribeE gasBig (arr k) root 0 0
              (sched-init prog ins₀) (st-init prog)))))

grant : ℕ → ℕ
grant k = arrD (nestUnit prog ins₀) 0 (closSizeᵉ (slotClos ins₀) (arr k))
