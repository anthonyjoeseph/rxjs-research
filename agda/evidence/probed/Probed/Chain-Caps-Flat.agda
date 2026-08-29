-- HOW MUCH SLACK A FLAT CAP HAS TO HAVE, ACROSS A CASCADE THAT WALKS.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: chainStep-caps @0f7196
--
-- WHAT IS BEING TESTED.  The target hands one chain's step a state
-- inside `frameStep Lv` of the instant's cap and asks for an INCREMENT
-- carrying the post-state, under the instant's own count.  So there are
-- two questions and the rows answer both at the family that refuted the
-- flat form: does an increment exist at all, and is it small.
--
-- AND THE ANSWER IS ONE LEVEL, WHICH IS THE FINDING.  At a cap the
-- pre-state fits, the post-state of ONE chain's step does not -- and it
-- fits that cap's FIRST step outright.  The increment is therefore one,
-- which is the EXISTENCE half of the target and the half a row can
-- settle.  The three cascade rows beneath say where the growth is: over
-- three families the width and registry components come back at or
-- below where they started -- a delivery CONSUMES a queued value and
-- RETIRES the registration it walked -- and only the size moves.
--
-- WHAT THESE ROWS DO NOT REACH, and it is why they are evidence for
-- the STEP leaf and not for the walk one beside it.  A fit read either
-- side of a step says the caps are recoverable at a level; it says
-- nothing about what the walk asserts at the states in between -- the
-- parked drain's two size bounds, the sink arm's registry-versus-unit
-- conjunct -- and those are the walk leaf's content.  Nor is the
-- CEILING reached, and it is now unreachable in principle rather than
-- by a seal: the target asks the increment to fit the walk's own
-- ceiling, an `iterL` over the path's length followed by one charge
-- per delivery, and one storey of that ladder at a cap this small is
-- already past anything that normalises.  So the rows say an increment
-- of one EXISTS and say nothing about what bounds it.
module Probed.Chain-Caps-Flat where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (length; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainsOf; chainStep)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
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

-- AND ONE LEVEL OF THE RECURRENCE COVERS THE STEP, which is the row the
-- statement now asks for.  Read either side of ONE chain's step rather
-- than a whole cascade: the post-state does NOT fit the cap the
-- pre-state was read at, and it DOES fit that cap's first step.  So the
-- claim the statement makes -- an increment exists, under the instant's
-- own count -- is satisfied here at an increment of one, and the gap
-- between the two is four orders of magnitude rather than a margin.
capU : Caps
capU = caps 26 4 4

eU : Sched Γ₂ × EvalSt pU
eU = let e₀ = entry pU sl₁ (sucGU 1 2 2 2 2)
     in step1 (proj₁ e₀) (proj₂ e₀)

stepRow : Bool × Bool × Bool
stepRow with sched-next (proj₁ eU)
... | inj₁ _ = false , false , false
... | inj₂ (a , sd) with chainsOf a (proj₂ eU)
...   | []            = false , false , false
...   | (rid , p) ∷ _ =
  let st₀ = cascadeLatch a (proj₂ eU)
      st₁ = record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }
      r   = chainStep 1 a p sd st₁
      sd′ = proj₁ (proj₂ r)
      st′ = proj₂ (proj₂ r)
  in capsOK? capU sd st₁
   , capsOK? capU sd′ st′
   , capsOK? (frameStep 1 capU) sd′ st′

step-pre : proj₁ stepRow ≡ true
step-pre = refl

step-flat : proj₁ (proj₂ stepRow) ≡ false
step-flat = refl

step-lvl1 : proj₂ (proj₂ stepRow) ≡ true
step-lvl1 = refl
