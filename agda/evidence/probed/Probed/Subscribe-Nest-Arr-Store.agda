-- ══════════════════════════════════════════════════════════════════
-- ONE SUBSCRIPTION'S STORE HALVES, WHICH ARE THE REGION THE DOUBLING
-- PROBE LEFT OPEN AND SAID SO.
--
-- TARGET: subscribeInner-nest-arr
--
-- WHY THIS AXIS.  The bound this statement carries is read on three
-- things: the values the subscription hands back, the whole node
-- table's maximum, and the table at each id.  `Probed.Thru-Step-
-- Indexed` reaches the first, at the duplicating family the residue
-- was named for, and records that it reaches neither of the others --
-- the arms it probes have room, so they queue nothing and both store
-- readings are `0 ≤ _`.  This module arms them: the subscription is
-- taken under a `from-inner` frame from a table already holding a
-- merge node whose queue carries a value three deep, and the arrival
-- is a LIMITED merge whose first inner is deferred, so its limit is
-- still spent when the descent returns and the second inner is
-- genuinely parked.
--
-- WHAT IS LOAD-BEARING.  `D` is `2 ^ pred (syncSizeᵉ o)` over the
-- ambient unit and the arrival's own depth, and it mentions the
-- incoming table nowhere -- so a subscription installing under the
-- frame something deeper than both the incoming reading and `D`
-- breaks the second and third conjuncts, and a deep enough parked
-- inner is exactly the shape that would.
-- ══════════════════════════════════════════════════════════════════
module Probed.Subscribe-Nest-Arr-Store where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ;
         nat̂; strmᵗ; deferᵉ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeInner; root; sched-init; st-init; EvalSt;
         Path; _↠_; from-inner; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nestCapsOK?; nodeNestAt)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

st₀ : EvalSt prog
st₀ = installNode 7 (mergeAll-st {t = natᵗ} (just 1) 1 (deepV 3 ∷ []) false)
                 (st-init prog)

κF : Path Γ₂ natᵗ natᵗ
κF = from-inner mergeAllᵒ 7 1 ↠ root

tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

-- the arrival: a limited merge whose first inner is deferred, so the
-- second is parked rather than subscribed
parkedFlat : ℕ → Val Γ₂ (obs (obs natᵗ))
parkedFlat k =
  ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ []))) ∷ strmᵗ (deepV k) ∷ [])

oF : ℕ → Closed Γ₂ natᵗ
oF k = mergeAllᵉ (just 1) (parkedFlat k)

-- the premises the statement names, pinned rather than assumed
premF : ∀ (k : ℕ) → Set
premF k =
  (nestValOK? (tight {obs natᵗ} (oF k)) (obs natᵗ) (oF k) ≡ true)
  × (nestCapsOK? (tight {obs natᵗ} (oF k)) (sched-init prog slots) st₀ ≡ true)

premF-6 : premF 6
premF-6 = refl , refl

r : (o : Closed Γ₂ natᵗ) → _
r o = subscribeInner gasBig mergeAllᵒ 7 κF 0 0 o (sched-init prog slots) st₀

stOf : Closed Γ₂ natᵗ → EvalSt prog
stOf o = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (r o)))))

-- the bound, with `B` at the arrival's own depth exactly
D : Closed Γ₂ natᵗ → ℕ
D o = 2 ^ pred (syncSizeᵉ o) * (nestUnit prog slots + nestDᵉ o)

armed : ℕ
armed = nodeNestAt 7 st₀

figures : ℕ
figures = armed + 10 * nestDᵛˢ (proj₁ (proj₂ (r (oF 6))))
        + 100 * nodesMax (stOf (oF 6)) + 10000 * nodeNestAt 7 (stOf (oF 6))
        + 1000000 * D (oF 6)

figures≡ : figures ≡ 0
figures≡ = refl
