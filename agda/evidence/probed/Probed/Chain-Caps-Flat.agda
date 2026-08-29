-- HOW MUCH SLACK A FLAT CAP HAS TO HAVE, ACROSS A CASCADE THAT WALKS.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: chainStep-caps @38f180
--
-- WHAT IS BEING TESTED.  The target asserts `chainsCapsOK` at ONE cap --
-- the one read at the instant the cascade starts -- and that predicate
-- restates `capsOK?` at EVERY state its fold passes through.  The
-- hypothesis speaks only about the state the fold BEGINS at, so the
-- whole content is that a walk which starts inside the cap stays inside
-- it, and the risk is that the cap is read one instant too early: the
-- frame-wise receipt this would be assembled from concludes at a GROWN
-- cap, and composing a walk's growth is what the caps recurrence
-- identifies with the cap at the NEXT instant.
--
-- AND THE ANSWER IS THAT ONLY THE SIZE MOVES, WHICH IS THE FINDING.
-- Over three families the width and the registry components do not grow
-- across a cascade at all -- both come back at or below where they
-- started, because a delivery CONSUMES a queued value and RETIRES the
-- registration it walked.  The size grows in every one of them, by
-- under a factor of three at the widest and by a bit over a third at
-- the narrowest, so the flat reading is a slack claim about a SINGLE
-- component and the other two are preservation outright.
--
-- WHAT THESE ROWS DO NOT REACH, and it is why they are evidence for
-- the STEP leaf and not for the walk one beside it.  A fit read before
-- and after a cascade says the caps survive the fold; it says nothing
-- about what the fold's own walk asserts at the states in between --
-- the parked drain's two size bounds, the sink arm's
-- registry-versus-unit conjunct -- and those are the walk leaf's
-- content.  The three figures below are the caps components alone.
module Probed.Chain-Caps-Flat where

open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainsOf)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)
open import Verify-Budget-Sufficient.Caps using (caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)

entry : ∀ {t} (e : Closed Γ₂ t) → Slots Γ₂ → ℕ → Sched Γ₂ × EvalSt e
entry e sl g =
  let r = subscribeE (gasPad g g0) e root 0 0 (sched-init e sl) (st-init e)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

step1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → Sched Γ₂ × EvalSt e
step1 sched st with sched-next sched
... | inj₁ _        = sched , st
... | inj₂ (a , sd) =
  let r = cascade a 1 sd st
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

sl₁ : Slots Γ₂
sl₁ = insF 1 2 2

-- THE READING, AND WHY IT IS NUMBERS RATHER THAN A VERDICT AT THE
-- TARGET'S OWN CAP.  `capsAt` does not reduce -- it spends `sizeCount`
-- and `capsH`, both sealed -- so `capsOK? (capsAt e sl id)` is a
-- NEUTRAL term and the target cannot be instantiated at its own cap.
-- That is a coverage boundary, not a dead probe: what the statement
-- risks is that a walk which starts inside a FLAT cap leaves it, and
-- that question is decidable at any concrete cap.  So each row reports
-- the SMALLEST cap the state fits, before the cascade and after it, one
-- component at a time -- and the flat claim is safe exactly when the
-- after-figures do not exceed the before-figures.

minFit : (ℕ → Bool) → ℕ → ℕ
minFit p = go 0
  where
  go : ℕ → ℕ → ℕ
  go k zero    = k
  go k (suc f) = if p k then k else go (suc k) f

fuel : ℕ
fuel = 400

-- the three components, each read with the other two given room, so a
-- figure is that component's own minimum and not a joint one
fits : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → ℕ × ℕ × ℕ
fits sched st =
    minFit (λ S → capsOK? (caps S 4000 4000) sched st) fuel
  , minFit (λ W → capsOK? (caps 4000 W 4000) sched st) fuel
  , minFit (λ R → capsOK? (caps 4000 4000 R) sched st) fuel

read1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e →
        ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
read1 sched st with sched-next sched
... | inj₁ _        = 0 , (0 , 0 , 0) , (0 , 0 , 0)
... | inj₂ (a , sd) =
  let r = cascade a 1 sd st
  in length (chainsOf a st)
   , fits sd (cascadeLatch a st)
   , fits (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

pU : Closed Γ₂ natᵗ
pU = progU 2 2

rowU : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
rowU = let e₀ = entry pU sl₁ (sucGU 1 2 2 2 2)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

pC : Closed Γ₂ natᵗ
pC = progC 1 2 2

rowC : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
rowC = let e₀ = entry pC sl₁ (sucGC 1 2 2 1 2 2)
       in read1 (proj₁ e₀) (proj₂ e₀)

pF : Closed Γ₂ natᵗ
pF = progF 1 1

rowF : ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
rowF = let e₀ = entry pF sl₁ (sucGF 1 2 2 1 1)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

U-row : rowU ≡ (1 , (26 , 4 , 1) , (69 , 1 , 0))
U-row = refl

C-row : rowC ≡ (3 , (17 , 1 , 3) , (24 , 1 , 0))
C-row = refl

F-row : rowF ≡ (2 , (38 , 1 , 2) , (52 , 1 , 0))
F-row = refl
