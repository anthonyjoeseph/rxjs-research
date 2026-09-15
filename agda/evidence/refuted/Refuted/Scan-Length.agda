-- THE FOLD'S LEAF ASKS FOR A COUNT ITS HYPOTHESES DO NOT CARRY, AND
-- AN ORDINARY FIVE-ELEMENT BURST IS ENOUGH TO SAY SO.
--
-- The leaf is handed a template, a seed, a burst, a bound on the
-- template's reading and a bound on the burst's VALUES; it is asked
-- back a figure leaving one rate per element under the entry rank.
-- Nothing in the premises relates the LENGTH of the burst to that
-- rank.  So fix a template reading nought, enter at the smallest rank
-- a run ever produces, and hand it five data values: every hypothesis
-- holds, the values impose nothing at all because the payload type is
-- data, and the conclusion demands a figure five below one.
--
-- THE WITNESS IS THE TYPICAL CASE RATHER THAN A CORNER, WHICH IS THE
-- WHOLE OF ITS FORCE.  The rank the machine seeds a top-level frame
-- with is one above the deepest value in hand, so a burst of plain
-- numbers enters at exactly the rank used here, and the rxjs line is
-- `of(1,2,3,4,5).pipe(scan((a, v) => a, 0))`.  A witness reachable
-- only at an adversarial configuration leaves the escape of
-- restricting the claim; this one leaves none, because the shape it
-- kills is the first program anybody would write.  Any burst longer
-- than the rank does it, so the margin is not an offset a wider bound
-- absorbs — the two quantities are independent.
--
-- WHAT SURVIVES, AND IT IS THE STATEMENT'S OWN CURRENCY.  The rate is
-- proven and is not what fails here; a repair has to put the count
-- somewhere a premise can see it, which means the entry rank stops
-- being a reading of the program alone.  That is a restatement of the
-- leaf's interface rather than a harder proof of its conclusion, and
-- it is why this witness is worth more than the reservation its target
-- already carried in prose.
--
-- REFUTED: `Refuted.Scan-Deepens` — the rate, over every burst length,
--   which is what put a length factor in the target's conclusion at all
-- REFUTED: `Refuted.Scan-Reachable` — the same currency from the other
--   side, where a bound in the reading PLUS the length HELD; this
--   witness says the target's way of paying for that length does not
module Refuted.Scan-Length where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; _≤_; _<_; _+_; _*_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤n+m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Fn; natᵗ; _×ᵗ_; reify; varᵗ; fstᵗ)
open import Rx.Obs-Depth using (depᵗ)
open import Rx.Evaluator.Doorless using (HandedOK)
open import Rx.Evaluator.Scan-Climb using (Rate)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ηᶻ : Fin 0 → ℕ
ηᶻ ()

-- behaviourally the identity on the accumulator, and as shallow as a
-- template can be: it writes no stream, so its reading is nought and
-- its rate is the one wrap `reify` charges
tmpl : Fn Γ₀ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
tmpl = fstᵗ (varᵗ (here refl))

-- five ordinary numbers.  At a data payload `ValOK` is `⊤`, so the
-- burst hypothesis is satisfied at EVERY rank and constrains nothing
burst₅ : List (Val Γ₀ natᵗ)
burst₅ = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

-- THE STATEMENT, as the leaf reads.
ScanFits : Set
ScanFits = ∀ {n} {Γ : Ctx n} {s u} {U r sz} (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s))
  → depᵗ η fn ≤ r → HandedOK η vs (U , r , sz)
  → Σ ℕ (λ a → (depᵗ η (reify ac) ≤ a)
             × All (λ v → depᵗ η (reify v) ≤ a) vs
             × (a + length vs * Rate η fn < r))

-- the template's own reading, which does not move with the burst
tmpl-is : depᵗ ηᶻ tmpl ≡ 0
tmpl-is = refl

-- one delivery's worth of climb: the wrap, and nothing else
rate-is : Rate ηᶻ tmpl ≡ 1
rate-is = refl

-- the burst hypothesis, discharged outright rather than out of any
-- statement this tower still owes
handed₅ : HandedOK {Γ = Γ₀} {u = natᵗ} ηᶻ burst₅ (0 , 1 , 0)
handed₅ = tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ

-- and the demand that cannot be met: five rates under a rank of one,
-- from a figure that also has to dominate the seed
scan-fits-false : ScanFits → ⊥
scan-fits-false claim
  with claim {Γ = Γ₀} {s = natᵗ} {u = natᵗ} {U = 0} {r = 1} {sz = 0}
         ηᶻ tmpl 0 burst₅ z≤n handed₅
... | a , _ , _ , s≤s le with ≤-trans (m≤n+m 5 a) le
... | ()
