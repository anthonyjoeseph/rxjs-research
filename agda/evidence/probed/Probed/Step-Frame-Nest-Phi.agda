-- ══════════════════════════════════════════════════════════════════
-- THE WALK'S POTENTIAL ACROSS ONE MAP FRAME, AT THE WITNESS THAT
-- KILLED THE READING IT REPLACED.
--
-- TARGET: stepFrame-nest-Φ @347d24
--
-- WHY THIS SHAPE AND NOT A SWEEP.  `Refuted.Apply-Fn-Nest` refuted the
-- ADDITIVE potential at a `mapᵉ` whose source list and whose step
-- function are the same outer variable, applied to a payload one
-- `switchAllᵉ` deep: one substitution installs the payload's nesting
-- twice while the path surrenders only the step function's own, which
-- is zero there.  The statement now scales by the path's FACTOR, so
-- the map frame is the only clause where the repair is actually bet,
-- and the refuting term is the only place the bet is adversarial.
--
-- WHAT IS LOAD-BEARING.  Both sides are computed: the left is the
-- evaluator's own `stepFrame` output, the right is the factor and the
-- depth read off the path, and the four figures are pinned separately
-- before either ordering is taken -- so a repair that moves the factor
-- or the charge fails here naming a number rather than turning the
-- crossing into an equality.  The ADDITIVE row is the control: it is
-- the same walk under the reading that died, and it reads false, so
-- the passing row above it cannot be passing for want of an attack.
--
-- NOT COVERED: any frame kind but `map-f`, and any path under the
-- frame but `root`.  A `scan-f` substitutes by the same rule and is
-- expected to behave identically; the three pass-through kinds spend
-- no factor at all, and a `thru-outer` spends depth rather than
-- factor, which is a different arm of the same statement.
-- ══════════════════════════════════════════════════════════════════
module Probed.Step-Frame-Nest-Phi where

open import Data.Bool using (true; false; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; nat̂; ofᵉ; strmᵗ; mapᵉ; switchAllᵉ;
         varᵗ; sizeᵗ)
open import Rx.Prim using (g0)
open import Rx.Evaluator
  using (sched-init; st-init; root; _↠_; Path; map-f; stepFrame)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; pathNestF)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

-- a program at the type the map frame lands in, so the frame's path
-- can be the empty one and the reading is the frame's alone
prog : Closed Γ₂ (obs (obs natᵗ))
prog = ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])) ∷ [])

-- the refuting payload: one `*All` layer deep
v : Val Γ₂ (obs natᵗ)
v = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- and the refuting step function: it names its payload on BOTH sides
-- of the `mapᵉ` sum
fn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fn = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

pathM : Path Γ₂ (obs natᵗ) (obs (obs natᵗ))
pathM = map-f fn ↠ root

out : List (Val Γ₂ (obs (obs natᵗ)))
out = proj₁ (stepFrame {e = prog} g0 0 0 (map-f fn) root (v ∷ []) false
                       (sched-init prog slots) (st-init prog))

U : ℕ
U = pathNestF pathM * (nestDᵛ (obs natᵗ) v + pathNestD pathM)

outNest : ℕ
outNest = foldr (λ w acc → nestDᵛ (obs (obs natᵗ)) w ⊔ acc) 0 out

packed : ℕ
packed = sizeᵗ fn + 100 * nestDᵗ fn + 10000 * pathNestF pathM
       + 1000000 * (nestDᵛ (obs natᵗ) v + pathNestD pathM)
       + 100000000 * outNest

figures≡ : packed ≡ 201640006
figures≡ = refl

-- the frame is handed the potential and hands it on
holds : valsΦ? U pathM (v ∷ []) ∧ valsΦ? U root out ≡ true
holds = refl

-- and the control: the same walk under the reading that died
Uadd : ℕ
Uadd = nestDᵛ (obs natᵗ) v + pathNestD pathM

addFails : all (λ w → nestDᵛ (obs (obs natᵗ)) w
                        + pathNestD (root {Γ = Γ₂} {t = obs (obs natᵗ)})
                        ≤ᵇ Uadd) out
             ≡ false
addFails = refl
