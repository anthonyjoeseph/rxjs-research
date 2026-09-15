-- THE ENTRY TRIPLE'S THIRD COMPONENT DOES NOT BOUND HOW MANY VALUES ONE
-- INSTANT CARRIES, and the witness is a program with an rxjs source
-- line: `of(0,0,0,0).pipe(scan((acc, v) => merge(acc, acc), of(0)),
-- mergeAll())`.  The template hands back its own accumulator TWICE and
-- flattens, so each delivery emits double what the last one did, and
-- the outer flattener puts the whole cascade into a single instant.
--
-- WHY THIS COMPONENT AND NOT ANOTHER.  The fold's leaf asks for a
-- reservation in the burst's LENGTH, and the entry invariant offers
-- exactly one length-shaped channel from the entry to a frame's
-- premise: the component seeded off `syncSizeᵉ`.  The rank cannot
-- carry it, since a rank is fixed by the caller before the run that
-- produces the burst exists, and the share census counts connections
-- rather than values.  So this is not one candidate among many -- it
-- is the only one, and a length-carrying restatement of the leaf has
-- to spend it.
--
-- AND THE FIGURES ARE THE FINDING RATHER THAN THE VERDICT.  Four
-- programs differing by one literal each: the run's peak doubles while
-- the reading gains one, so the two cross ONCE and never meet again.
-- The first three rows HOLD, which is why the bound reads true from
-- small cases and why the witness has to carry the row that fails
-- beside the rows that do not.  Both lists are claimed because the
-- finding is their crossing: a repair moving either end alone would
-- leave a witness reporting numbers that no longer meet.
--
-- The rates are what generalise, not the numerals.  A measure additive
-- in the syntax gains a bounded amount per symbol, and a cascade that
-- re-subscribes its own accumulator doubles per delivery, so no
-- constant and no wider syntactic measure closes the gap -- only a
-- quantity read off the RUN can, and the entry has none.
--
-- REFUTED: `Refuted.Scan-Deepens` — the climb in the DEPTH, proven as a
--   rate over every burst length; this witness is its counterpart in
--   the COUNT, and the two together are why the leaf's arithmetic is
--   owed in a currency the entry does not carry
module Refuted.Burst-Length where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≱; m<m+n)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit; InstEvent; value)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
  ofᵉ; scanᵉ; mergeAllᵉ; varᵗ; nat̂; fstᵗ; strmᵗ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

zero̊ : Tm Γ₀ [] [] [] natᵗ
zero̊ = nat̂ 0

-- the accumulator taken TWICE and flattened: behaviourally a merge of
-- the last accumulator with itself, so one delivery emits double
dbl : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
dbl = strmᵗ (mergeAllᵉ nothing
        (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ (ofᵉ (zero̊ ∷ []))

prog₁ prog₂ prog₃ prog₄ : Closed Γ₀ natᵗ
prog₁ = mergeAllᵉ nothing (scanᵉ dbl seed (ofᵉ (zero̊ ∷ [])))
prog₂ = mergeAllᵉ nothing (scanᵉ dbl seed (ofᵉ (zero̊ ∷ zero̊ ∷ [])))
prog₃ = mergeAllᵉ nothing (scanᵉ dbl seed (ofᵉ (zero̊ ∷ zero̊ ∷ zero̊ ∷ [])))
prog₄ = mergeAllᵉ nothing
          (scanᵉ dbl seed (ofᵉ (zero̊ ∷ zero̊ ∷ zero̊ ∷ zero̊ ∷ [])))

-- the values one instant carries, past the bookkeeping events
nvals : List (InstEvent (Val Γ₀ natᵗ)) → ℕ
nvals []              = 0
nvals (value _ ∷ evs) = suc (nvals evs)
nvals (_ ∷ evs)       = nvals evs

peak : ℕ → Closed Γ₀ natᵗ → Slots Γ₀ → ℕ
peak fuel e ins = foldr _⊔_ 0
  (map (λ em → nvals (InstEmit.events em)) (evaluate↓ fuel e ins))

-- the run's own answer: one literal added to the source, and the
-- instant's width doubles
peaks : List ℕ
peaks = peak 100 prog₁ ins₀ ∷ peak 100 prog₂ ins₀
      ∷ peak 100 prog₃ ins₀ ∷ peak 100 prog₄ ins₀ ∷ []

peaks-are : peaks ≡ 2 ∷ 6 ∷ 14 ∷ 30 ∷ []
peaks-are = refl

-- and the reading the entry is seeded from, which gains one per literal
sizes : List ℕ
sizes = syncSizeᵉ prog₁ ∷ syncSizeᵉ prog₂ ∷ syncSizeᵉ prog₃
      ∷ syncSizeᵉ prog₄ ∷ []

sizes-are : sizes ≡ 17 ∷ 18 ∷ 19 ∷ 20 ∷ []
sizes-are = refl

-- THE STATEMENT.  No instant of a run carries more values than the
-- entry's own reading.  Quantified over the fuel, the program and the
-- slots, so no instance of it can be rescued by choosing any of them.
SyncSizeBoundsBurst : Set
SyncSizeBoundsBurst = (fuel : ℕ) (e : Closed Γ₀ natᵗ) (ins : Slots Γ₀)
  → peak fuel e ins ≤ syncSizeᵉ e

sync-bounds-burst-false : SyncSizeBoundsBurst → ⊥
sync-bounds-burst-false claim =
  <⇒≱ (m<m+n 20 (s≤s z≤n)) (claim 100 prog₄ ins₀)
