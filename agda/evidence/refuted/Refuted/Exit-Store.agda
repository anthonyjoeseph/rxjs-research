-- NOR IS A FRAME'S OUTPUTS BOUNDED BY THE STORE THE STEP LEAVES.  A fold
-- emits every intermediate accumulator and keeps only the LAST, so a
-- template that DISCARDS its accumulator on a later delivery hands back
-- a shallow store having already emitted a deep value.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT IT KILLS, AND IT IS THE CHOICE OF STORE RATHER THAN THE JOIN.
-- The depth here is never manufactured: it walks in on the accumulator
-- the frame was ENTERED with, survives one delivery, and is dropped on
-- the next.  So the surviving shape must read the store the step was
-- entered AT, and no reading of the value it leaves can stand in — the
-- exit store is a function of the last delivery alone, and the burst's
-- own history is what the conclusion quantifies over.

-- WHY IT IS CLAIMED BESIDE THE CLIMB AND NOT FOLDED INTO IT.  The two
-- die to different repairs, which is the only reason to state a second
-- witness at all.  The climb needs a figure growing with the burst;
-- this one is answered by reading the other end of the step, and no
-- quantity growing in the burst's length repairs it, because the burst
-- here is TWO and the template deepens nothing at all.

-- AND IT IS WHY THE MEASURE CANNOT SEE THE DIFFERENCE.  Under a `strmᵗ`
-- a variable is reified WHOLE and no projection is reduced, so a
-- template that deepens pays for the accumulator and the payload
-- together and the store can only climb.  The drop needs a head the
-- evaluator reduces at the VALUE level — a conditional over a data
-- payload, choosing between the accumulator and a constant — which is
-- the one shape that discards without reading anything.

-- AND THE REPAIR THAT READS BOTH ENDS DIES HERE TOO, WHICH IS WHY THE
-- SECOND STATEMENT IS IN THIS FILE RATHER THAN ITS OWN.  Joining the
-- entry store, the exit store and the incoming bound, and ADDING the
-- template's own reading on top, is the strongest shape that still
-- reads a fixed number of stored values — and a template that climbs
-- while its payload says so and discards when it stops leaves the
-- burst's peak strictly inside, visible at neither end.  What survives
-- must therefore carry a factor in the burst's LENGTH, which is the
-- climb's repair reaching the store readings as well.

-- THE BOUNDARY.  As with the climb, the rows are over `scanVals` and
-- reach the frame step through `step-scan` and no other constructor.
-- What is NOT shown is that a store this deep is reachable at a frame's
-- entry; the crossing is between the statement's own quantities, so
-- reachability is not what it turns on.
module Refuted.Exit-Store where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _+_; _⊔_; z≤n)
open import Data.Nat.Properties using (n≮n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ty; Ctx; Val; Fn; natᵗ; boolᵗ; obs; _×ᵗ_; ofᵉ; emptyᵉ;
  mergeAllᵉ; varᵗ; fstᵗ; sndᵗ; ifᵗ; strmᵗ; applyFn)
open import Rx.Obs-Depth using (obsDepthᵗ; obsDepthᵛ)
open import Rx.Evaluator using (scanVals)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

-- The measure's context implicit is not inferable from a value: at a
-- data type `Val Γ t` mentions no Γ at all, so every application below
-- pins it once through this alias rather than six times inline.
depth : (t : Ty) → Val Γ₀ t → ℕ
depth t v = obsDepthᵛ {Γ = Γ₀} t v

----------------------------------------------------------------------
-- THE STATEMENT.  The shape that survived the climb: the outgoing bound
-- joins what came in with a reading of the store the step LEAVES.  It
-- is stated at its strongest — the reader may have the whole exit value
-- and not merely a figure computed from it.
----------------------------------------------------------------------

ExitBounded : Set
ExitBounded =
  ∀ {u s} (fn : Fn Γ₀ [] [] [] (u ×ᵗ s) u) (ac : Val Γ₀ u) (m : ℕ)
    (vals : List (Val Γ₀ s)) →
    All (λ v → depth s v ≤ m) vals →
    All (λ v → depth u v ≤ m ⊔ depth u (proj₂ (scanVals fn ac vals)))
        (proj₁ (scanVals fn ac vals))

----------------------------------------------------------------------
-- THE TEMPLATE THAT DISCARDS.  Its two arms are the accumulator
-- untouched and a constant, so it deepens nothing and manufactures
-- nothing — the witness cannot be read as the climb in another
-- spelling.
----------------------------------------------------------------------

keep : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ boolᵗ) (obs natᵗ)
keep = ifᵗ (sndᵗ (varᵗ (here refl)))
           (fstᵗ (varᵗ (here refl)))
           (strmᵗ emptyᵉ)

-- one layer, and it walks in at the frame's entry rather than being
-- built by anything the step does
deep : Val Γ₀ (obs natᵗ)
deep = mergeAllᵉ nothing (ofᵉ (strmᵗ emptyᵉ ∷ []))

-- KEEP then DISCARD, which is what leaves the peak behind the store:
-- reversing it satisfies the statement, so the order is the finding
burst : List (Val Γ₀ boolᵗ)
burst = true ∷ false ∷ []

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl`.  Three figures rather than one,
-- because a repair moving any single end would leave a witness
-- reporting numbers that no longer meet: the entry store carries the
-- depth, the first output still has it, and the exit store does not.
----------------------------------------------------------------------

entry-is : depth (obs natᵗ) deep ≡ 1
entry-is = refl

kept-is : depth (obs natᵗ) (applyFn keep (deep , true)) ≡ 1
kept-is = refl

store-is : depth (obs natᵗ) (proj₂ (scanVals keep deep burst)) ≡ 0
store-is = refl

-- DEGENERATE by design, and that is the point: every payload is data,
-- so the incoming bound is NOUGHT and the deep output cannot be read as
-- depth the caller supplied
under : All (λ v → depth boolᵗ v ≤ 0) burst
under = z≤n ∷ z≤n ∷ []

-- LOAD-BEARING: the surviving value is one the statement quantifies
-- over.  Without this row the crossing would be about a value the
-- conclusion never mentions
kept-among : applyFn keep (deep , true) ∈ proj₁ (scanVals keep deep burst)
kept-among = here refl

exit-bounded-false : ExitBounded → ⊥
exit-bounded-false h = n≮n 0 (lookup (h keep deep 0 burst under) kept-among)

----------------------------------------------------------------------
-- THE SECOND STATEMENT.  Both ends of the step, the incoming bound,
-- and the template's own reading ADDED rather than joined — the
-- strongest shape that still reads a fixed number of stored values.
----------------------------------------------------------------------

BothEndsBounded : Set
BothEndsBounded =
  ∀ {u s} (fn : Fn Γ₀ [] [] [] (u ×ᵗ s) u) (ac : Val Γ₀ u) (m : ℕ)
    (vals : List (Val Γ₀ s)) →
    All (λ v → depth s v ≤ m) vals →
    All (λ v → depth u v
                 ≤ obsDepthᵗ fn
                     + (depth u ac ⊔ depth u (proj₂ (scanVals fn ac vals)) ⊔ m))
        (proj₁ (scanVals fn ac vals))

-- CLIMB while the payload says so, DISCARD when it stops.  One arm is
-- the climb's template and the other the discard's, so the peak it
-- leaves is interior by construction rather than by arithmetic
rise : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ boolᵗ) (obs natᵗ)
rise = ifᵗ (sndᵗ (varᵗ (here refl)))
           (strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))
           (strmᵗ emptyᵉ)

base : Val Γ₀ (obs natᵗ)
base = emptyᵉ

long : List (Val Γ₀ boolᵗ)
long = true ∷ true ∷ false ∷ []

interior : Val Γ₀ (obs natᵗ)
interior = applyFn rise (applyFn rise (base , true) , true)

----------------------------------------------------------------------
-- THE SECOND CROSSING.  Four figures, because this statement offers
-- four quantities and the finding is that the peak clears ALL of them:
-- both ends read nought, the template reads one, and the interior
-- output reads two.
----------------------------------------------------------------------

rise-tmpl-is : obsDepthᵗ rise ≡ 1
rise-tmpl-is = refl

rise-entry-is : depth (obs natᵗ) base ≡ 0
rise-entry-is = refl

rise-store-is : depth (obs natᵗ) (proj₂ (scanVals rise base long)) ≡ 0
rise-store-is = refl

interior-is : depth (obs natᵗ) interior ≡ 2
interior-is = refl

-- DEGENERATE by design, as above: the payloads are the discard's own
-- switch and carry no depth for the peak to be attributed to
long-under : All (λ v → depth boolᵗ v ≤ 0) long
long-under = z≤n ∷ z≤n ∷ z≤n ∷ []

-- LOAD-BEARING: the peak is the SECOND output, so it is neither end of
-- the burst.  A witness whose peak sat first or last would be refuting
-- a reading of one store rather than of both
interior-among : interior ∈ proj₁ (scanVals rise base long)
interior-among = there (here refl)

both-ends-false : BothEndsBounded → ⊥
both-ends-false h = n≮n 1 (lookup (h rise base 0 long long-under) interior-among)
