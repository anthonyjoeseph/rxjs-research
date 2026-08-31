-- ══════════════════════════════════════════════════════════════════
-- THE OUTER WRAP IS CHARGED ONE PER VALUE AND SUBSCRIBES EACH OF THEM,
-- so the per-value form at `thru-outer` is FALSE for the same reason
-- the inner arm is.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A `thru-outer` frame is the one frame
-- `pathNestD` charges, and it charges a UNIT: over a burst of `W` the
-- arm may deepen the store by `W`, one wrap per value taken.  The unit
-- is the `suc` a `*All` layer adds, which is exactly right for the
-- LAYER and says nothing about what the layer does.
--
-- WHERE IT BREAKS.  What a `thru-outer` takes is a list of
-- OBSERVABLES, and `thruWalk` SUBSCRIBES each one -- so the values it
-- hands on are the inner's emissions, not its own argument rewrapped.
-- The argument is priced by `nestDᵉ`, additive at `mapᵉ`, while the
-- substitution the subscription performs is not, so an emitted value
-- is deeper than the observable it came from by the number of times
-- the step function names its payload.  Eighty against forty-one at a
-- payload forty layers deep, and the depth is a free parameter, so no
-- per-value constant closes it.
--
-- THE TWO *ALL ARMS FAIL TOGETHER, WHICH IS THE FINDING.  This is the
-- same defect `Refuted.Inner-Drain-Nest` pins at the drain, arriving
-- at the other boundary: both frames re-enter the subscribe machinery
-- and both are charged as if they forwarded.  So the repair is one
-- repair -- the subscribe descent has to be charged in the currency
-- `depth-nest-compositional` already states it in -- and not two
-- separate widenings at two frames.
--
-- WHAT IS HAND-BUILT.  The state is `st-init` plus one `installNode`,
-- and the statement quantifies over every `st`; the node is the
-- ordinary one a `mergeAllᵉ` subscribe installs, with no lane taken.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Subscribe-Nest where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; emptyᵉ; ofᵉ; mapᵉ; switchAllᵉ;
         varᵗ; nat̂; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; mergeAll-st; thru-outer; mergeAllᵒ;
         root; stepFrame; sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Store using (frameNestF)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; frameNestD)
open import Refuted.Demand-Programs using (Γ₂; insT)

----------------------------------------------------------------------
-- THE WITNESS.  `Refuted.Step-Frame-Nest-Dup`'s pair -- a payload forty
-- `*All` layers deep and a step function naming it on both sides of a
-- `mapᵉ` sum -- handed to the wrap as the one observable it consumes.
----------------------------------------------------------------------

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the step function names its payload TWICE, once on each side of the
-- `mapᵉ` sum: as the list the source emits, and as the mapped result
dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dupFn = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

-- the observable the wrap takes: one emit, and that emit is the
-- substitution
o : Val Γ₂ (obs (obs (obs natᵗ)))
o = mapᵉ dupFn (ofᵉ (strmᵗ (deepV 40) ∷ []))

vals : List (Val Γ₂ (obs (obs (obs natᵗ))))
vals = o ∷ []

e : Closed Γ₂ (obs (obs natᵗ))
e = emptyᵉ

slots : Slots Γ₂
slots = insT 0 0 0

sched₀ : Sched Γ₂
sched₀ = sched-init e slots

-- the node a `mergeAllᵉ` subscribe installs, with no lane taken
st₀ : EvalSt e
st₀ = installNode 0 (mergeAll-st {t = obs (obs natᵗ)} nothing 0 [] false)
                  (st-init e)

f : Frame Γ₂ (obs (obs (obs natᵗ))) (obs (obs natᵗ))
f = thru-outer mergeAllᵒ 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

-- the smallest width the statement admits, and the one its own
-- hypotheses pin: `1 ≤ W` and one value in the list
W : ℕ
W = 1

row : ℕ × ℕ
row = let r = stepFrame gas 0 0 f root vals false sched₀ st₀
      in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)
       , (nodesMax st₀ ⊔ nestDᵛˢ vals) + W

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
emitted≡80 : proj₁ row ≡ 80
emitted≡80 = refl

perValue≡41 : proj₂ row ≡ 41
perValue≡41 = refl

stepFrame-nodes-thru-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `80 ≤ᵇ 41` reduces to `false`, so `T` of it IS the empty type
stepFrame-nodes-thru-absurd h = ≤⇒≤ᵇ h

----------------------------------------------------------------------
-- AND THE ASSEMBLY FALLS TO THE SAME WITNESS: `frameNestF` reads a
-- `thru-outer` as one and `frameNestD` as one, so at this width the
-- parent's charge IS the leaf's bound.
----------------------------------------------------------------------

parentCharge : ℕ
parentCharge = frameNestF f ^ W * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W * frameNestD f)

parent≡41 : parentCharge ≡ 41
parent≡41 = refl

stepFrame-nodes-at-thru-absurd : proj₁ row ≤ parentCharge → ⊥
stepFrame-nodes-at-thru-absurd h = ≤⇒≤ᵇ h

c₀ : Caps
c₀ = caps 0 0 0

capsZeroThru : capsOK? c₀ sched₀ st₀ ≡ true
capsZeroThru = refl

capsCharge : ℕ
capsCharge = 2 ^ Caps.cSize c₀ * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W)

capsCharge≡41 : capsCharge ≡ 41
capsCharge≡41 = refl

stepFrame-nodes-thru-caps-absurd : proj₁ row ≤ capsCharge → ⊥
stepFrame-nodes-thru-caps-absurd h = ≤⇒≤ᵇ h

valCapsFails : valCaps? c₀ slots (obs (obs (obs natᵗ))) o ≡ false
valCapsFails = refl

----------------------------------------------------------------------
-- AND THE POTENTIAL FALLS AT THE SAME FRAME, in the currency the walk
-- carries now.  The walk's charge is a product -- the factor the path
-- can still apply, times the depth in flight plus the depth still to
-- climb -- and `frameNestF` reads a `thru-outer` as ONE, so all this
-- frame has to pay a doubling with is the single unit `pathNestD`
-- charges.  Eighty against forty-one again, and the arrival's depth is
-- a free parameter, so no constant closes it: the repair has to be a
-- FACTOR at this frame, in a currency that can see the term the
-- subscription evaluates.
----------------------------------------------------------------------

-- the two sides of the walk's per-frame law at the empty path, where
-- the factor is one and the depth still to climb is zero
walkBefore walkAfter : ℕ
walkBefore = frameNestF f * (nestDᵛˢ vals + frameNestD f)
walkAfter  = nestDᵛˢ (proj₁ (stepFrame gas 0 0 f root vals false sched₀ st₀))

walkBefore≡41 : walkBefore ≡ 41
walkBefore≡41 = refl

walkAfter≡80 : walkAfter ≡ 80
walkAfter≡80 = refl

thruΦ-grantless-absurd : walkAfter ≤ walkBefore → ⊥
-- `80 ≤ᵇ 41` reduces to `false`, so `T` of it IS the empty type
thruΦ-grantless-absurd h = ≤⇒≤ᵇ h
