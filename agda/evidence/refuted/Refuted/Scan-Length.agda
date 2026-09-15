-- THE FOLD'S LEAF ASKS FOR A COUNT ITS HYPOTHESES DO NOT CARRY, AND
-- AN ORDINARY FIVE-ELEMENT BURST IS ENOUGH TO SAY SO.
--
-- The leaf is handed a template, a seed, a burst, a bound on the
-- template's reading at the rank the burst ARRIVED at and a bound on
-- the burst's VALUES; it is asked back a figure leaving one rate per
-- element under the rank the fold DELIVERS at.  Nothing in the
-- premises relates the LENGTH of the burst to that rank.  So fix a
-- template that wraps its accumulator once, deliver at the smallest
-- rank such a template admits, and hand it five data values: every
-- hypothesis holds, the values impose nothing at all because the
-- payload type is data, and the conclusion demands a figure five
-- below one.
--
-- THE WITNESS IS THE TYPICAL CASE RATHER THAN A CORNER, WHICH IS THE
-- WHOLE OF ITS FORCE.  A template that wraps is the only kind whose
-- rate is positive at all, and one wrap is the least it can write, so
-- the configuration here is the cheapest member of the only family
-- the claim has anything to say about; the rxjs line is
-- `of(1,2,3,4,5).pipe(scan((a, v) => of(a), EMPTY))`.  A witness
-- reachable only at an adversarial configuration leaves the escape of
-- restricting the claim; this one leaves none, because the burst is
-- five ordinary numbers.  Any burst longer than the rank does it, so
-- the margin is not an offset a wider bound absorbs — the two
-- quantities are independent.
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
open import Data.Nat using (ℕ; _≤_; _<_; _+_; _*_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n+m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (nothing)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Fn; natᵗ; obs; _×ᵗ_; reify; varᵗ;
  fstᵗ; strmᵗ; ofᵉ; emptyᵉ; mergeAllᵉ)
open import Rx.Obs-Depth using (depᵗ)
open import Rx.Evaluator.Doorless using (HandedOK)
open import Rx.Evaluator.Scan-Climb using (Rate)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ηᶻ : Fin 0 → ℕ
ηᶻ ()

-- behaviourally the identity on the accumulator, and as shallow as a
-- WRAPPING template can be: one `strmᵗ` over the binder, which is the
-- least a positive rate can cost
tmpl : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
tmpl = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

-- five ordinary numbers.  At a data payload `ValOK` is `⊤`, so the
-- burst hypothesis is satisfied at EVERY rank and constrains nothing
burst₅ : List (Val Γ₀ natᵗ)
burst₅ = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

-- THE STATEMENT, as the leaf reads.
ScanFits : Set
ScanFits = ∀ {n} {Γ : Ctx n} {s u} {U q sz r} (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s))
  → depᵗ η q fn ≤ r → HandedOK η vs (U , q , sz)
  → Σ ℕ (λ a → (depᵗ η 0 (reify ac) ≤ a)
             × All (λ v → depᵗ η 0 (reify v) ≤ a) vs
             × (a + length vs * Rate η fn < r))

-- one delivery's worth of climb: the wrap, and nothing else.  This is
-- also the reading the premise is discharged at, since the burst
-- arrives at the closed rank and `Rate` is the reading taken there
rate-is : Rate ηᶻ tmpl ≡ 1
rate-is = refl

-- the burst hypothesis, discharged outright rather than out of any
-- statement this tower still owes
handed₅ : HandedOK {Γ = Γ₀} {u = natᵗ} ηᶻ burst₅ (0 , 0 , 0)
handed₅ = tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ

-- and the demand that cannot be met: five rates under a rank of one,
-- from a figure that also has to dominate the seed
scan-fits-false : ScanFits → ⊥
scan-fits-false claim
  with claim {Γ = Γ₀} {s = natᵗ} {u = obs natᵗ} {U = 0} {q = 0} {sz = 0}
         {r = 1}
         ηᶻ tmpl emptyᵉ burst₅ ≤-refl handed₅
... | a , _ , _ , s≤s le with ≤-trans (m≤n+m 5 a) le
... | ()
