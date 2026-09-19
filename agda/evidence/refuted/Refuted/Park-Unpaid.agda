------------------------------------------------------------------
-- THE PARK IS NOT PAID FOR BY ANYTHING THE STEP RELATION CARRIES.
------------------------------------------------------------------

-- WHAT THIS KILLS.  The builder's budget is a pair -- an unconnected
-- COUNT and a PARKED TOTAL -- and it is preserved across a step by a
-- disjunction: either the parked total does not grow, or the count
-- strictly drops.  That reading was to be established by induction
-- over the delivery cycle, arm by arm, against the same cycle the
-- count's own bound was already proven over.
--
-- IT CANNOT BE, AND THE OBSTRUCTION IS ONE ARM.  A saturated
-- `mergeAll` PARKS an arriving inner: the observable goes on the
-- node's queue, so the parked total rises by exactly one.  That arm
-- is a LEAF of the relation -- two equations, a lookup and a
-- room test, and no sub-derivation -- and it touches neither the
-- slot telescope nor the connected list, so the count is unmoved.
-- Neither disjunct is available, and a derivation ending in it
-- inhabits the hypothesis of the statement at full generality.
--
-- SO THE REPAIR IS A RESTATEMENT AND NOT A PROOF.  What was supposed
-- to pay for the park is a connect somewhere ABOVE it in the run --
-- the fan-out that fires a chain the walk is not standing on -- and
-- the step relation quantifies over every path and every store, so
-- nothing in its hypotheses says a connect happened.  A statement
-- carrying that fact is a different statement.
module Refuted.Park-Unpaid where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties using (n≮n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (natᵗ; obs; Ctx; Closed; Val; emptyᵉ; []ᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; thru-outer;
  mergeAllᵒ; mergeAll-st; mergeAllPark; st-init; sched-init)
open import Rx.Evaluator.Domain using (emit⇓; emit-thru-outer; consume-merge-park)
open import Rx.Evaluator.Reducible using (Out; queued; unconnected)

-- THE SMALLEST RUN THAT PARKS: an empty program, one `mergeAll` node
-- whose limit is zero, and an inner arriving at it down a path with
-- nothing above the outer.
Γ₀ : Ctx 0
Γ₀ = []

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

o₀ : Val Γ₀ (obs natᵗ)
o₀ = [] , emptyᵉ , []ᵉ

st₀ : EvalSt e₀
st₀ = record (st-init e₀)
        { nodes = (0 , mergeAll-st {Γ = Γ₀} {t = natᵗ} (just 0) 0 [] false) ∷ [] }

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ (λ ())

κ₀ : Path Γ₀ 0 (obs natᵗ) natᵗ
κ₀ = thru-outer mergeAllᵒ 0 ↠ root

park : emit⇓ {e = e₀} κ₀ 0 o₀ sched₀ st₀ ([] , sched₀ , mergeAllPark 0 o₀ st₀)
park = emit-thru-outer (consume-merge-park refl refl)

-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED, because what is
-- refuted is the SHAPE and not a name: any statement of this reading
-- over the bare step relation is this type.
StepPreservesPair : Set
StepPreservesPair =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {κ : Path Γ lo u t} {now} {v : Val Γ u}
    {sched : Sched Γ} {st : EvalSt e} {r : Out e}
  → emit⇓ {e = e} κ now v sched st r
  → queued (proj₂ (proj₂ r)) ≤ queued st
    ⊎ unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) < unconnected sched st

step-preserves-pair-false : StepPreservesPair → ⊥
step-preserves-pair-false f with f park
... | inj₁ ()
... | inj₂ lt = n≮n _ lt
