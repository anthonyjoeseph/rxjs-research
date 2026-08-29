-- THE DESCENT AGAINST A CEILING THAT COMPUTES.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: cascade-nest-flat @6a79ec
--
-- WHY THIS ONE IS TESTABLE AND ITS CONSUMER IS NOT.  The statement the
-- proof spends bounds the descent by a SEALED factor times the store
-- plus a SEALED increment, and neither of those two can be
-- instantiated -- the factor is a power of two whose exponent is a
-- delivery square, so no row evaluates it.  The target here replaces
-- both by quantities that compute: a numeral for the factor, and the
-- arrival's own size for the increment.  Every term is then a numeral
-- at a concrete program, so a row is a verdict rather than a
-- half-verdict, and the two proven inequalities that carry this form
-- back to the sealed one are what make the verdict transfer.
--
-- EVERY ROW IS LABELLED, and none is vacuous by the usual route.
-- `depthCascade a id [] sched st` is `0` outright, so a program that
-- selects no chains proves nothing -- each block pins the CHAIN COUNT
-- and the DESCENT beside the verdict, so a descent above zero says a
-- run actually walked something.
--
-- NOT COVERED: EVERY PREMISE, and none of them for the same reason as
-- the conclusion.  All three compare against a SEALED cap -- the caps
-- record's fields and the nesting cap alike -- so none of them reduces
-- at any program, and a row cannot discharge one.  These rows are
-- evidence that the CONCLUSION holds where the evaluator reaches, and
-- say nothing about whether a state a premise rejects would still
-- satisfy it.  The compiled harness does read the nesting premise,
-- since the backend ignores the seal, and reports it holding on these
-- families -- measured, not rechecked, and recorded here only to say
-- the rows are not being taken at states the premise excludes.
module Probed.Cascade-Nest-Flat where

open import Data.Bool using (Bool; true)
open import Data.List using (length)
open import Data.Nat using (ℕ; _+_; _*_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; sizeᵛ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next; cascade; cascadeLatch;
  chainsOf; arrTy; arrVal)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)
open import Verify-Budget-Sufficient.Caps-Depth using (depthCascade)
open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; chainsNestD)

----------------------------------------------------------------------
-- The reading: chain count, descent, and the verdict at one arrival --
-- the target's own inequality at a factor of sixteen, conjoined with
-- the nesting premise it takes.
----------------------------------------------------------------------

read1 : ∀ {t} {e : Closed Γ₂ t} → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
read1 sched st with sched-next sched
... | inj₁ _        = 0 , 0 , true
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      ch  = chainsOf a st
      dep = depthCascade a 1 ch sd stL
  in length ch , dep
   , (dep ≤ᵇ nestDᵛ (arrTy a) (arrVal a) + chainsNestD ch
            + 16 * (storeNestMax sd stL + sizeᵛ (arrTy a) (arrVal a)))

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
-- ROW 1 — THE BOUNDED DRAIN.  `progU` is the limit-1 mergeAll family,
-- so its inners park and the drain fires; the reading is taken at the
-- SECOND cascade, which is where something is parked to release.  This
-- is the region in which the descent is known to outrun the syntactic
-- terms beside it, so it is where a factor has to pay.
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
-- tail -- the arm read at a state `cascadeGo` never visits.
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
-- ROW 3 — A SECOND FAMILY, one instant in.  `progF` delivers on every
-- chain it selects, so it exercises the arm `progC` skips, and reading
-- it past the first cascade puts the store somewhere other than where
-- the subscribe left it.
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
