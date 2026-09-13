-- WHAT THE WALK'S TWO EVALUATING ARMS OWE, INSTANTIATED — and the
-- family that refuted the earlier form, agreeing with the report the
-- walk now carries.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THESE TWO STATEMENTS ARE PROBEABLE AT ALL, which most of this
-- tree's targets are not: both are hypothesis-free and both sides of
-- each compute.  A term the machine evaluates is read by the reading's
-- own term clause first, so the row is an arithmetic comparison at a
-- concrete program and the decision procedure is the honest witness.
-- The points are chosen so neither side is zero: a literal list of
-- OBSERVABLES and a fold seeded with one, since a data payload reads
-- zero on the left by construction and a row taken there could not
-- have failed.  The source arm now compares a PAIR, and its literals
-- deliver two and three times, so the count half is a comparison rather
-- than one against one.
--
-- AND THE WALK ROWS BELOW ARE ABOUT SOMETHING ELSE, deliberately: they
-- instantiate the CONCLUSION the two leaves serve, which is a real body
-- and so carries no receipt of its own.  Their subject is the doubling
-- fold at a late slot — the family that killed the previous form of
-- this comparison, where the carried depth climbed one per source
-- literal against a bound flat in source length.  Read against the
-- iterating clause the two sides now agree at every length reached, and
-- the margin is CONSTANT rather than closing, which is the shape a
-- crossing would have shown up in.
--
-- THE BOUNDARY, and it is what these rows do NOT buy.  Every row here
-- is a SUBSCRIBE at the root; no row reaches an arrival, a drain step
-- or a second cascade, so nothing here says anything about what the
-- loop preserves.  Lengths run to four literals and layers to two,
-- because a row costs a whole walk.
--
-- TARGET: ofᵉ-carried @975fea
-- TARGET: scan-seed-carried @44379b
module Probed.Carried-Leaf where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤ᵇ_; _+_; _*_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ;
  strmᵗ; nat̂; fstᵗ; varᵗ; input; evalTm)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; depthᵉ; rdᵗˢ; ε)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (subscribeE; rootWitness; root; sched-init;
  st-init)
open import Verify-Rank-Sufficient.Carried using (burstRd; valsRd)
open import Verify-Rank-Sufficient.Leaf-Carried using (ofᵉ-carried;
  scan-seed-carried)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE CLOSED CONTEXT, where the reading of an input cannot enter and
-- every figure is the term's own.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

ψ₀ : Fin 0 → Rd₃
ψ₀ = slotRd ins₀

----------------------------------------------------------------------
-- THE SOURCE ARM.  A one-shot whose literals are OBSERVABLES, so the
-- left side is a real join rather than the zero a data payload forces.
-- The second point nests one flattener inside a literal, which is where
-- the reading's own `suc` enters and where a clause charging the
-- literal list nothing would cross.
----------------------------------------------------------------------

litsFlat : List (Tm Γ₀ [] [] [] (obs natᵗ))
litsFlat = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ []))
         ∷ strmᵗ emptyᵉ
         ∷ []

litsNest : List (Tm Γ₀ [] [] [] (obs natᵗ))
litsNest = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])) ∷ [])))
         ∷ strmᵗ (ofᵉ (nat̂ 4 ∷ []))
         ∷ []

ofFlat : Confirms (ofᵉ-carried ψ₀ litsFlat)
ofFlat = Below , Below

ofNest : Confirms (ofᵉ-carried ψ₀ litsNest)
ofNest = Below , Below

-- BOTH COMPONENTS PINNED, since the statement now compares a PAIR and a
-- row green on the hop side alone would say nothing about the other.
-- Radix 1000, low first: delivered count and its bound at the flat
-- point, then at the nested one.  Both are TIGHT — two against two and
-- three against three — so a literal list the reading undercharged by a
-- single delivery would cross here.
ofPacked : ℕ
ofPacked = proj₁ (valsRd ψ₀ (obs natᵗ) (map (λ tm → evalTm tm) litsFlat))
         + 1000 * proj₁ (rdᵗˢ ψ₀ ε litsFlat)
         + 1000000 * proj₁ (valsRd ψ₀ (obs natᵗ)
             (map (λ tm → evalTm tm) litsNest))
         + 1000000000 * proj₁ (rdᵗˢ ψ₀ ε litsNest)

ofPacked-is : ofPacked ≡ 3003002002
ofPacked-is = refl

----------------------------------------------------------------------
-- THE SEED ARM, which is the one the store half rides on.  A seed that
-- reads zero could not refute anything, so both points seed the fold
-- with a live observable — the second with a flattened one, which is
-- the deepest thing a seed can be.
----------------------------------------------------------------------

stepG : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepG = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

srcG : Closed Γ₀ natᵗ
srcG = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

seedFlat : Tm Γ₀ [] [] [] (obs natᵗ)
seedFlat = strmᵗ (ofᵉ (nat̂ 7 ∷ nat̂ 8 ∷ []))

seedNest : Tm Γ₀ [] [] [] (obs natᵗ)
seedNest = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ nat̂ 8 ∷ [])) ∷ [])))

scanFlat : Confirms (scan-seed-carried ψ₀ stepG seedFlat srcG)
scanFlat = Below

scanNest : Confirms (scan-seed-carried ψ₀ stepG seedNest srcG)
scanNest = Below

----------------------------------------------------------------------
-- THE FAMILY THAT REFUTED THE EARLIER FORM.  One input, cold, a
-- synchronous part that lengthens row by row; the program flattens a
-- map of each arriving value into a six-literal burst and folds the
-- result under a step that re-wraps its accumulator.  A fold builds its
-- accumulator at RUN time, one fresh layer per refold, so this is where
-- a bound flat in source length was crossed.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insAt : List ℕ → Slots Γ₁
insAt xs zero = scripted (cold xs (after 0 , 9 ∷ []))

step : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

burst6 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst6 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

casc6 : Closed Γ₁ (obs natᵗ)
casc6 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

-- a step that wraps TWO layers per refold, against a reading whose fold
-- clause iterates the same step
step2 : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
          (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

casc2L : Closed Γ₁ (obs natᵗ)
casc2L = scanᵉ step2 (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

carriedAt : Closed Γ₁ (obs natᵗ) → List ℕ → ℕ
carriedAt o xs =
  proj₂ (burstRd (slotRd (insAt xs)) (obs natᵗ)
    (proj₁ (subscribeE {lo = 1} (rootWitness o (insAt xs)) o
             root 0 0 (sched-init o (insAt xs)) (st-init o))))

termAt : Closed Γ₁ (obs natᵗ) → List ℕ → ℕ
termAt o xs = depthᵉ (slotRd (insAt xs)) o

holds : Closed Γ₁ (obs natᵗ) → List ℕ → Bool
holds o xs = carriedAt o xs ≤ᵇ termAt o xs

-- LOAD-BEARING at every row: the reading is what a clause charging the
-- fold nothing for what it folds over read as FLAT, against a carried
-- depth that climbs with the literal
rate : (holds casc6 (7 ∷ [])
      ∧ holds casc6 (7 ∷ 8 ∷ [])
      ∧ holds casc6 (7 ∷ 8 ∷ 9 ∷ [])
      ∧ holds casc6 (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])
      ∧ holds casc2L (7 ∷ [])
      ∧ holds casc2L (7 ∷ 8 ∷ [])
      ∧ holds casc2L (7 ∷ 8 ∷ 9 ∷ [])) ≡ true
rate = refl

-- BOTH SIDES PINNED, so the rows above are green with a margin someone
-- can read rather than merely green.  Radix 1000: carried and term at
-- one literal and at four, one layer then two.
packed : ℕ
packed = carriedAt casc6 (7 ∷ [])
       + 1000 * termAt casc6 (7 ∷ [])
       + 1000000 * carriedAt casc6 (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])
       + 1000000000 * termAt casc6 (7 ∷ 8 ∷ 9 ∷ 10 ∷ [])

packed-is : packed ≡ 31024013006
packed-is = refl

packed2L : ℕ
packed2L = carriedAt casc2L (7 ∷ [])
         + 1000 * termAt casc2L (7 ∷ [])
         + 1000000 * carriedAt casc2L (7 ∷ 8 ∷ 9 ∷ [])
         + 1000000000 * termAt casc2L (7 ∷ 8 ∷ 9 ∷ [])

packed2L-is : packed2L ≡ 49036025012
packed2L-is = refl

----------------------------------------------------------------------
-- AND THE AXIS THE LITERAL ROWS CANNOT REACH: a fold over a RECURSION
-- delivers as many times as the drain lets it, which is not a quantity
-- the term carries at all.
----------------------------------------------------------------------

recur : Closed Γ₀ natᵗ
recur = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

foldR : Closed Γ₀ (obs natᵗ)
foldR = scanᵉ stepG (strmᵗ emptyᵉ) recur

carried₀ : Closed Γ₀ (obs natᵗ) → ℕ
carried₀ o =
  proj₂ (burstRd ψ₀ (obs natᵗ)
    (proj₁ (subscribeE {lo = 0} (rootWitness o ins₀) o root 0 0
             (sched-init o ins₀) (st-init o))))

recurRow : (carried₀ foldR ≤ᵇ depthᵉ ψ₀ foldR) ≡ true
recurRow = refl
