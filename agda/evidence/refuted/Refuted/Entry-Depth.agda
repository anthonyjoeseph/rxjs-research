-- THE ENTRY'S DEPTH READING DOES NOT BOUND THE DEPTH OF WHAT A RUN
-- EMITS, and this is the composition of two witnesses already in this
-- tree rather than a new mechanism.  `Refuted.Scan-Deepens` proves a
-- fold whose template re-wraps its accumulator deepens it by exactly
-- one per delivery; `Refuted.Burst-Length` proves the number of
-- deliveries one instant carries is not bounded by any reading of the
-- program.  Feed the second into the first and the depth of an emitted
-- value climbs with a quantity the entry cannot see.
--
-- WHY THE COMPOSITION SAYS MORE THAN EITHER HALF.  Each half is about a
-- LEAF: one about a fold's outputs given a burst, the other about a
-- burst's length given a program.  Neither instantiates the rank the
-- descent is actually seeded at, so both were readable as statements
-- about a bound that was merely stated too weakly.  This one is the
-- entry's own reading, taken against a RUN, so there is no weaker
-- statement left to retreat to: the figure the caller fixes before the
-- run exists is compared with what the run produces.
--
-- AND THE CROSSING IS NOT A RACE BETWEEN TWO GROWING QUANTITIES.  The
-- depth reading is a ⊔ over the syntax, so lengthening the source's
-- literal list moves it not at all, while each added literal doubles
-- the cascade.  One side is CONSTANT across the family and the other
-- doubles, which is why four rows settle it and why no constant, no
-- multiple and no wider syntactic measure closes the gap.
module Refuted.Entry-Depth where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Nat using (ℕ; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≱; m<m+n)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit; InstEvent; value)
open import Rx.Exp using (Closed; Tm; Val; natᵗ; obs; emptyᵉ; scanᵉ; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Evaluator using (unconn)
open import Refuted.Apparatus using (obsDepthᵉ; obsDepthᵛ)
open import Refuted.Burst-Length using (Γ₀; ins₀; prog₁; prog₂; prog₃; prog₄)
open import Refuted.Scan-Deepens using (bump)

-- THE TWO HALVES, TAKEN AS THEY STAND.  `prog₁`..`prog₄` are
-- `Refuted.Burst-Length`'s own cascade, whose instant doubles per
-- literal added, and `bump` is `Refuted.Scan-Deepens`' own template,
-- which re-wraps its accumulator once per delivery.  Nothing is
-- restated here: the composition is the finding, so importing the
-- pieces is what makes it one.
emptySeed : Tm Γ₀ [] [] [] (obs natᵗ)
emptySeed = strmᵗ emptyᵉ

-- the fold that deepens once per delivery of the cascade, whose
-- emissions are the observables the rank has to price
deep₁ deep₂ deep₃ deep₄ : Closed Γ₀ (obs natᵗ)
deep₁ = scanᵉ bump emptySeed prog₁
deep₂ = scanᵉ bump emptySeed prog₂
deep₃ = scanᵉ bump emptySeed prog₃
deep₄ = scanᵉ bump emptySeed prog₄

-- the deepest payload one instant carries, past the bookkeeping events
vdepth : InstEvent (Val Γ₀ (obs natᵗ)) → ℕ
vdepth (value v) = obsDepthᵛ {Γ = Γ₀} (obs natᵗ) v
vdepth _         = 0

peak : ℕ → Closed Γ₀ (obs natᵗ) → Slots Γ₀ → ℕ
peak fuel e ins = foldr _⊔_ 0
  (map (λ em → foldr _⊔_ 0 (map vdepth (InstEmit.events em)))
       (evaluate↓ fuel e ins))

peaks : List ℕ
peaks = peak 400 deep₁ ins₀ ∷ peak 400 deep₂ ins₀
      ∷ peak 400 deep₃ ins₀ ∷ peak 400 deep₄ ins₀ ∷ []

reads : List ℕ
reads = obsDepthᵉ deep₁ ∷ obsDepthᵉ deep₂ ∷ obsDepthᵉ deep₃
      ∷ obsDepthᵉ deep₄ ∷ []

-- LOAD-BEARING, AND IT IS WHAT MAKES THE ENTRY READING A CEILING RATHER
-- THAN MERELY A STARTING POINT.  Of the order's three edges only the
-- connect one leaves the rank component free, and it fires on a drop in
-- the unconnected-share count -- so at a context with no slots at all
-- there is no such edge to take, every step either drops the rank or
-- holds it, and no frame of this run is reachable at a rank above the
-- entry's.  The row fails the moment a share is put on the table, which
-- is why the witness is written at the empty context.
no-connect-edge : unconn ins₀ [] ≡ 0
no-connect-edge = refl

-- THE STATEMENT.  No value a run emits reads deeper than the figure the
-- entry took off the program.  Quantified over the fuel, the program
-- and the slots, so no instance of it can be rescued by choosing any of
-- them.
EntryDepthBoundsRun : Set
EntryDepthBoundsRun = (fuel : ℕ) (e : Closed Γ₀ (obs natᵗ)) (ins : Slots Γ₀)
  → peak fuel e ins ≤ obsDepthᵉ e

-- LOAD-BEARING, AND BOTH LISTS ARE CLAIMED BECAUSE THE FINDING IS THEIR
-- CROSSING.  The first row HOLDS -- two under three -- which is why a
-- bound read off the syntax reads true from small programs, and why the
-- witness carries the row that fails beside the rows that do not.  A
-- repair moving either end alone would leave a witness reporting
-- figures that no longer meet.
run-peaks-are : peaks ≡ 2 ∷ 6 ∷ 14 ∷ 30 ∷ []
run-peaks-are = refl

-- and the entry's side, which does not move at all: the reading is a ⊔
-- over the syntax and a longer literal list adds no nesting
entry-reads-are : reads ≡ 3 ∷ 3 ∷ 3 ∷ 3 ∷ []
entry-reads-are = refl

-- thirty is not under three.
entry-depth-bounds-run-false : EntryDepthBoundsRun → ⊥
entry-depth-bounds-run-false claim =
  <⇒≱ (m<m+n 3 (s≤s z≤n)) (claim 400 deep₄ ins₀)
