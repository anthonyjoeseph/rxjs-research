-- THE SAME DEFECT REACHES `emit-scan`, and its clause's existing product
-- does not absorb it — the two multiply different things.
--
-- `nestDᵉ sl (scanᵉ f z e) = nestDᵗ sl z + outWᵉ n sl e * nestDᵗ sl f
-- + nestDᵉ sl e`.  The `outWᵉ` factor was put there for the axis
-- `Refuted.Depth-Nest` found: a step function re-wraps its own
-- ACCUMULATOR once per delivered payload, so the layers multiply by the
-- payload COUNT.  What follows multiplies by the number of times the
-- step's template mentions the payload — an axis of the SYNTAX, not of
-- the run — and `outWᵉ` is 1 here, so nothing absorbs it.
module Refuted.Emit-Scan where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Data.Bool using (false)
open import Data.Product using (proj₁; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; _×ᵗ_; obs; nat̂; strmᵗ;
  varᵗ; sndᵗ; ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; applyFn)
open import Rx.Frame-Width using (outWᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init;
  subscribeE)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Verify-Budget-Sufficient.Depth-Compositional
  using (innerNest; burstND?; EmitCap)

g20 : Gas
g20 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

deep : Closed Γ₀ natᵗ
deep = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- ONE payload, so `outWᵉ` cannot be what pays
eS : Closed Γ₀ (obs natᵗ)
eS = ofᵉ (strmᵗ deep ∷ [])

-- a seed with no nesting of its own
zS : Tm Γ₀ [] [] [] (obs natᵗ)
zS = strmᵗ emptyᵉ

-- THE WITNESS: the step's template mentions the incoming payload — the
-- pair's SECOND component, not the accumulator — under both operands of
-- an inner `mapᵉ`.  Index 1 inside the map's own binder, index 0 outside.
fS : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
fS = strmᵗ (mergeAllᵉ (mapᵉ (sndᵗ (varᵗ (there (here refl))))
                            (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))))

progS : Closed Γ₀ (obs natᵗ)
progS = scanᵉ fS zS eS

schedS : Sched Γ₀
schedS = sched-init progS slots₀

stS : EvalSt progS
stS = st-init progS

------------------------------------------------------------------
-- THE ARITHMETIC
------------------------------------------------------------------

seedNest : nestDᵗ slots₀ zS ≡ 0
seedNest = refl

stepNest : nestDᵗ slots₀ fS ≡ 1
stepNest = refl

srcNest : nestDᵉ slots₀ eS ≡ 1
srcNest = refl

-- the factor the clause already carries, and it is 1: one payload
countFactor : outWᵉ 0 slots₀ eS ≡ 1
countFactor = refl

bound : innerNest slots₀ progS ≡ 2
bound = refl

emitted : nestDᵉ slots₀ (applyFn fS (emptyᵉ , deep)) ≡ 3
emitted = refl

------------------------------------------------------------------
-- THE REFUTATION
------------------------------------------------------------------

row : burstND? slots₀ (innerNest slots₀ progS) (obs natᵗ)
        (proj₁ (subscribeE g20 progS root 0 0 schedS stS)) ≡ false
row = refl

emit-scan-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {s}
     (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
     (b : Closed Γ s) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     EmitCap g (scanᵉ f z b) κ bid now sched st) → ⊥
emit-scan-absurd h with h g20 fS zS eS root 0 0 schedS stS
... | ()
