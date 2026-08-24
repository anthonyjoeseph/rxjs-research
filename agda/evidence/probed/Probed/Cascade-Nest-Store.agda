-- THE DESCENT AGAINST THE STORE THE WALK LEAVES BEHIND.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
-- TARGET: cascade-nest-store
--
-- WHY IT IS TESTABLE AT ALL, and it is the whole reason this statement was
-- worth stating: both sides COMPUTE.  The target is premise-free -- it reads
-- the descent against its base terms plus the store measure taken at the
-- walk's own result -- so there is no hypothesis to discharge and no sealed
-- family in the way, and an instantiation is a verdict rather than a
-- half-verdict.  The narrow readings this replaces were refuted, so a row
-- that could only distinguish THEM is not the point: the rows here are
-- chosen to reach the two regions those refutations turned on.
--
-- EVERY ROW IS LABELLED, and none of them is vacuous by the usual route.
-- `depthCascade a id [] sched st` is `0` outright, so a program with no
-- chains selected proves nothing -- each block therefore pins the CHAIN
-- COUNT and the DESCENT alongside the verdict, in the same file, by refl.
-- A descent pinned above zero is a run that actually walked something.
module Probed.Cascade-Nest-Store where

open import Data.Bool using (Bool; true; false)
open import Data.List using (length)
open import Data.Nat using (ℕ; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; cascadeGo; chainsOf; arrTy; arrVal)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)
open import Verify-Budget-Sufficient.Caps-Depth using (depthCascade)
open import Verify-Budget-Sufficient.Nest-Store using (storeNestMax; chainsNestD)

----------------------------------------------------------------------
-- The reading: chain count, descent, and the verdict, at one arrival.
-- `n` selects the cascade -- 0 is the arrival the subscribe leaves, and
-- each step past that RUNS a full cascade first, so a later row is read
-- at a state the evaluator actually reached rather than one written down.
----------------------------------------------------------------------

read1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
read1 sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      ch  = chainsOf a st
      g   = cascadeGo a 1 ch sd stL
      aft = storeNestMax (proj₁ (proj₂ g)) (proj₂ (proj₂ g))
      dep = depthCascade a 1 ch sd stL
  in length ch , dep
   , (dep ≤ᵇ nestDᵛ (arrTy a) (arrVal a) + chainsNestD ch + aft)

-- one whole cascade, so the next reading is taken at a state the
-- evaluator REACHED rather than one written down by hand
step1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → Sched Γ₂ × EvalSt e
step1 sched st with sched-next sched
... | inj₁ _        = sched , st
... | inj₂ (a , sd) =
  let r = cascade a 1 sd st
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

entry : ∀ {t} (e : Closed Γ₂ t) → Slots Γ₂ → ℕ → Sched Γ₂ × EvalSt e
entry e sl g =
  let r = subscribeE (gasPad g g0) e root 0 0 (sched-init e sl) (st-init e)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

sl₁ : Slots Γ₂
sl₁ = insF 1 2 2

----------------------------------------------------------------------
-- ROW 1 — THE BOUNDED DRAIN, at the exact witness that refuted both
-- narrow readings.  `progU` is the limit-1 mergeAll family, so its
-- inners park and the drain fires; the reading is taken at the SECOND
-- cascade, which is where something is parked to release.  This is the
-- only region in which the descent is known to outrun every syntactic
-- term, so a row that clears it here is the load-bearing one.
----------------------------------------------------------------------

pU : Closed Γ₂ natᵗ
pU = progU 2 2

rowU : ℕ × ℕ × Bool
rowU = let e₀ = entry pU sl₁ (sucGU 1 2 2 2 2)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

U-chains : proj₁ rowU ≡ 1
U-chains = refl

U-descent : proj₁ (proj₂ rowU) ≡ 13
U-descent = refl

U-holds : proj₂ (proj₂ rowU) ≡ true
U-holds = refl

----------------------------------------------------------------------
-- ROW 2 — THE SKIP BRANCH.  `progC`'s arrival selects more chains than
-- it delivers on, so `depthCascade`'s cons clause takes its PHANTOM
-- tail -- the arm read at a state `cascadeGo` never visits.  That arm
-- is what killed the per-chain reading, and it is charged here.
----------------------------------------------------------------------

pC : Closed Γ₂ natᵗ
pC = progC 1 2 2

rowC : ℕ × ℕ × Bool
rowC = let e₀ = entry pC sl₁ (sucGC 1 2 2 1 2 2)
       in read1 (proj₁ e₀) (proj₂ e₀)

C-chains : proj₁ rowC ≡ 3
C-chains = refl

C-descent : proj₁ (proj₂ rowC) ≡ 4
C-descent = refl

C-holds : proj₂ (proj₂ rowC) ≡ true
C-holds = refl

----------------------------------------------------------------------
-- ROW 3 — A SECOND FAMILY, and at the second cascade rather than the
-- first.  `progF` delivers on every chain it selects, so it exercises
-- the arm `progC` skips, and reading it one instant in puts the store
-- somewhere other than where the subscribe left it.
----------------------------------------------------------------------

pF : Closed Γ₂ natᵗ
pF = progF 1 1

rowF : ℕ × ℕ × Bool
rowF = let e₀ = entry pF sl₁ (sucGF 1 2 2 1 1)
           e₁ = step1 (proj₁ e₀) (proj₂ e₀)
       in read1 (proj₁ e₁) (proj₂ e₁)

F-chains : proj₁ rowF ≡ 2
F-chains = refl

F-descent : proj₁ (proj₂ rowF) ≡ 8
F-descent = refl

F-holds : proj₂ (proj₂ rowF) ≡ true
F-holds = refl
