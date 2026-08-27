-- WHICH COMPONENT OF THE STORE A CASCADE ACTUALLY GROWS.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: cascadeGo-nest-regs @4149d3
--
-- WHY THE COMPONENTS ARE READ SEPARATELY.  The store measure is a
-- four-way `⊔` and the walk is charged one increment for the whole of
-- it, so a row reading only the total cannot say which summand the
-- increment is FOR -- and the sibling row for the pending sources turned
-- out to need no increment at all.  These rows put each summand beside
-- the total the walk started from, so a component that never outruns it
-- is visible as one.
--
-- EVERY ROW IS LOAD-BEARING IN THE ONE WAY THAT MATTERS HERE: it is the
-- AFTER figures that carry the finding, and they are read at the state a
-- full cascade left rather than at one written down by hand.  The chain
-- count is pinned beside them because a cascade over an empty selection
-- walks nothing and would report preservation for free.
--
-- NOT COVERED, and it is the whole reason this cannot settle the target:
-- the bound the target states is `storeNestMax + nestIncAt`, and
-- `nestIncAt` spends the anchor, which no instantiation reaches.  These
-- rows say whether the increment is NEEDED, never whether it suffices.
module Probed.Cascade-Store-Components where

open import Data.List using (length)
open import Data.Nat using (ℕ)
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
open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; regsNestMax)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax)

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

-- chains walked, the whole store the walk started from, then the two
-- summands the walk can move: the registry's paths and the node table
read1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → ℕ × ℕ × ℕ × ℕ
read1 sched st with sched-next sched
... | inj₁ _        = 0 , 0 , 0 , 0
... | inj₂ (a , sd) =
  let r = cascade a 1 sd st
  in length (chainsOf a st)
   , storeNestMax sd (cascadeLatch a st)
   , regsNestMax (EvalSt.registry (proj₂ (proj₂ r)))
   , nodesMax (proj₂ (proj₂ r))

pU : Closed Γ₂ natᵗ
pU = progU 2 2

rowU : ℕ × ℕ × ℕ × ℕ
rowU = let e₀ = entry pU sl₁ (sucGU 1 2 2 2 2)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

pC : Closed Γ₂ natᵗ
pC = progC 1 2 2

rowC : ℕ × ℕ × ℕ × ℕ
rowC = let e₀ = entry pC sl₁ (sucGC 1 2 2 1 2 2)
       in read1 (proj₁ e₀) (proj₂ e₀)

pF : Closed Γ₂ natᵗ
pF = progF 1 1

rowF : ℕ × ℕ × ℕ × ℕ
rowF = let e₀ = entry pF sl₁ (sucGF 1 2 2 1 1)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

U-parts : rowU ≡ (1 , 3 , 0 , 12)
U-parts = refl

C-parts : rowC ≡ (3 , 2 , 0 , 3)
C-parts = refl

F-parts : rowF ≡ (2 , 5 , 0 , 7)
F-parts = refl
