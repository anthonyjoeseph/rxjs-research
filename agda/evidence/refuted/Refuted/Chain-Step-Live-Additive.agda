-- ══════════════════════════════════════════════════════════════════
-- A DEPTH-ADDITIVE CHARGE CANNOT PAY FOR A MINT AT A DEFERRED BODY.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  The live arm of a chain's store transport
-- wants a charge the round's own cap can absorb, and the cap is
-- DEPTH-denominated -- a `suc` of the program's nesting depth and the
-- slot vocabulary's.  So the candidate charged the path ADDITIVELY,
-- `pathNestD path + sizeᵛ` of the arrival, against the multiplicative
-- form whose path PRODUCT the cap has no room for.
--
-- WHY IT LOOKED RIGHT.  It holds everywhere the corpus already looks.
-- Both merge families clear it with room, the two-frame family clears
-- it, the parked-drain attack clears it, and the transforming frame
-- meets it EXACTLY at four against four -- a tightness that reads as
-- the bound being the right one rather than as the last row before it
-- crosses.
--
-- WHERE IT BREAKS.  Both depth measures read ZERO into a `deferᵉ`
-- body; only `sizeᵛ`/`sizeᵗ` descend.  So a `map-f` whose function is
-- a deferred constant of depth k hands the frame something k deep
-- while `nestDᵗ` of that function -- and hence the whole additive
-- charge -- does not move at all.  The grown fold tracks k and the
-- charge is CONSTANT: six against four at depth six, on the same
-- family that was tight at depth four.
--
-- WHAT THIS DOES NOT SHOW.  It does not refute the arm.  What dies is
-- the currency: any charge built from the nesting-DEPTH measures is
-- blind to a deferred body, so the live arm needs a SIZE-based factor
-- somewhere, and the question the leg now owes is whether the round's
-- cap has room for one.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Live-Additive where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; foldr)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Val; Exp; natᵗ; obs; nat̂; ofᵉ; strmᵗ; deferᵉ; switchAllᵉ;
         sizeᵛ)
open import Rx.Prim using (Gas; g0; gs)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root;
         chainStep; Arrival; Path; _↠_; thru-outer; mergeAllᵒ;
         map-f; installNode; mergeAll-st)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; pathNestD)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE gas prog root 0 0 (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

-- the node the chain delivers into: an empty limited merge
emptyNode : EvalSt prog
emptyNode = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (proj₂ sub)

-- the transforming frame, whose function is a DEFERRED constant of
-- depth k -- the one place a value enters that the arrival never
-- carried, and the one the depth measures cannot see into
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE zero    = ofᵉ (nat̂ 0 ∷ [])
deepE (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepE k) ∷ []))

shallowV : Val Γ₂ (obs natᵗ)
shallowV = ofᵉ (nat̂ 0 ∷ [])

shallow : Arrival Γ₂
shallow = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = obs natᵗ
                 ; payload = shallowV ; isLast = false }

path : ℕ → Path Γ₂ (obs natᵗ) natᵗ
path k = map-f (strmᵗ (deferᵉ (deepE k))) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

grown : ℕ → ℕ
grown k = liveMax (proj₁ (proj₂ (chainStep 1 shallow (path k) (proj₁ sub) emptyNode)))

chargeD : ℕ → ℕ
chargeD k = liveMax (proj₁ sub) ⊔ slotsNestSum (Sched.slots (proj₁ sub))
              ⊔ (pathNestD (path k) + sizeᵛ (obs natᵗ) shallowV)

-- THE FIGURES, PINNED.  The tight row is the one that makes this a
-- refutation and not a margin: at four the two sides MEET, so the
-- candidate is not merely loose here -- it is exactly spent, and the
-- next step of the same family crosses it while the charge stands
-- still
tight : ℕ × ℕ
tight = grown 4 , chargeD 4

tight≡ : tight ≡ (4 , 4)
tight≡ = refl

cross : ℕ × ℕ
cross = grown 6 , chargeD 6

cross≡ : cross ≡ (6 , 4)
cross≡ = refl

chain-step-live-additive-absurd : proj₁ cross ≤ proj₂ cross → ⊥
-- `6 ≤ᵇ 4` reduces to `false`, so `T` of it IS the empty type
chain-step-live-additive-absurd h = ≤⇒≤ᵇ h
