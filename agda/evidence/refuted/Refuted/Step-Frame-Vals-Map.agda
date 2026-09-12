-- ══════════════════════════════════════════════════════════════════
-- THE MAP ARM'S GRANT CANNOT SEE ITS STEP FUNCTION, so no grant bounds
-- what the arm emits.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A chain position is entered with a GRANT --
-- one number `S` that the position's potential, the payload in flight
-- and the store are all under -- and what a `map-f` frame emits stays
-- under it.  Three hypotheses fix `S`: the potential at the position,
-- the depth of the values handed in, and the store's own depth.
--
-- WHERE IT BREAKS.  The frame's STEP FUNCTION is quantified over and
-- appears in NONE of the three.  The map arm is `map (applyFn fn)`,
-- and a step function that IGNORES its payload still emits its own
-- body -- so the emitted depth is `nestDᵗ fn`, a free parameter of the
-- statement that no hypothesis moves with.  Pick it one deeper than
-- whatever grant the other three admit and the conclusion is `suc S ≤
-- S`.  The grant here is symbolic on purpose: `nestΦAt` is sealed, so
-- the witness never computes it, and the crossing therefore holds at
-- EVERY grant rather than at one arithmetic.
--
-- WHAT DIES AND WHAT DOES NOT.  The unconditional form dies at all
-- four of the split's arms, not only this one -- the quantifier is the
-- same in each, and the map arm is merely the one that needs no burst
-- count to say so.  What survives is that the frame a chain position
-- actually steps is not arbitrary: it is read off a PATH derived from
-- the program the grant is sighted at.  So the repair is a reading
-- indexed by that path -- `valsΦ?` is one, already proven to transport
-- across all five arms -- and not a larger grant, since no grant
-- stated before the frame is chosen can dominate a term chosen after.
--
-- WHAT IS HAND-BUILT.  Nothing: the schedule and the store are
-- `sched-init` and `st-init`, and the statement quantifies over every
-- `sched` and `st`.  The frame is the one the statement names.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Step-Frame-Vals-Map where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; z≤n)
open import Data.Nat.Properties
  using (⊔-identityʳ; m≤m⊔n; m≤n⊔m; 1+n≰n)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; subst)

open import Rx.Prim using (Gas; Id; Tick)
open import Rx.Exp
  using (Ctx; Closed; Exp; Val; Fn; natᵗ; obs;
         emptyᵉ; ofᵉ; mergeAllᵉ; nat̂; strmᵗ; applyFn)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; map-f; stepFrame; budgetAt;
         sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (storeSyncMax)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using (nestΦAt)
open import Refuted.Demand-Programs using (Γ₂; insT)

----------------------------------------------------------------------
-- THE STATEMENT, RESTATED HERE rather than imported, so that a repair
-- moving it leaves this file refuting what it was written against.
----------------------------------------------------------------------
StepFrameValsMap : Set
StepFrameValsMap = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (bid : Id) (now : Tick) (S : ℕ)
  (fn : Fn Γ [] [] [] s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sf ≡ budgetAt e sl bid →
  nestΦAt e sl id ≤ S →
  nestDᵛˢ vals ≤ S →
  storeSyncMax sched st ≤ S →
  nestDᵛˢ (proj₁ (stepFrame sf bid now (map-f fn) p vals fin sched st)) ≤ S

----------------------------------------------------------------------
-- THE WITNESS.  A step function that never names its payload, whose
-- body is `d` `mergeAllᵉ` layers deep.  `d` is the free parameter: the
-- statement's hypotheses do not mention `fn` at all.
----------------------------------------------------------------------

deepE : ℕ → Exp Γ₂ [] [] (natᵗ ∷ []) natᵗ
deepE 0       = ofᵉ (nat̂ 0 ∷ [])
deepE (suc d) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deepE d) ∷ []))

fnD : ℕ → Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
fnD d = strmᵗ (deepE d)

-- substitution cannot shrink a term that has no variable in it
apply-nest : ∀ (d : ℕ) (v : Val Γ₂ natᵗ) →
  nestDᵛ (obs natᵗ) (applyFn (fnD d) v) ≡ d
apply-nest 0       v = refl
apply-nest (suc d) v = cong suc (trans (⊔-identityʳ _) (apply-nest d v))

e₀ : Closed Γ₂ (obs natᵗ)
e₀ = emptyᵉ

slots₀ : Slots Γ₂
slots₀ = insT 0 0 0

sched₀ : Sched Γ₂
sched₀ = sched-init e₀ slots₀

st₀ : EvalSt e₀
st₀ = st-init e₀

-- a plain nat payload, so the value axis contributes nothing and the
-- crossing is the step function's alone
vals₀ : List (Val Γ₂ natᵗ)
vals₀ = 0 ∷ []

-- THE GRANT, taken as the join of the two quantities the witness
-- cannot compute -- `nestΦAt` is sealed -- so the three hypotheses
-- hold by ⊔-introduction at every program rather than at one numeral
S₀ : ℕ
S₀ = nestΦAt e₀ slots₀ 0 ⊔ storeSyncMax sched₀ st₀

-- what the arm emits, at step-function depth `d`
out : ℕ → ℕ
out d = nestDᵛˢ (proj₁ (stepFrame (budgetAt e₀ slots₀ 0) 0 0
                          (map-f (fnD d)) root vals₀ false sched₀ st₀))

out-nest : ∀ (d : ℕ) → out d ≡ d
out-nest d = trans (⊔-identityʳ _) (apply-nest d 0)

-- THE FIGURE, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality.
-- LOAD-BEARING: it is the arm actually stepping and emitting, and it
-- fails the moment `stepFrame`'s map clause stops forwarding the
-- substitution or `deepE` stops delivering its index
out₄≡4 : out 4 ≡ 4
out₄≡4 = refl

step-frame-vals-map-absurd : StepFrameValsMap → ⊥
step-frame-vals-map-absurd h =
  1+n≰n (subst (_≤ S₀) (out-nest (suc S₀))
    (h slots₀ 0 (budgetAt e₀ slots₀ 0) 0 0 S₀ (fnD (suc S₀)) root vals₀
       false sched₀ st₀ refl refl (m≤m⊔n _ _) z≤n (m≤n⊔m _ _)))
