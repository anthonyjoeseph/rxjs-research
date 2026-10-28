{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, OVER THE EMISSION SET: `simultaneous.Statement`'s
-- three statements and its anchor, each read off the rows a reader of
-- the emission set meets (`denotation.EmissionSet.Read.Run`), where those read the
-- first n events of a stream.
module simultaneous.EmissionSet where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; concat)
import Data.List as L
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import denotation.MonotonicList.Events using (_≟ᵖ_; Pos; Timeline; root)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; enter; ⟦_⟧ᵀ)
open import denotation.EmissionSet.Read using (Run; Hush; cursor)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; Rooted; stamped; closed)
open import simultaneous.Statement using (batchedObs; SameInstant; named)

open Elaborate {C = Timeline} _≟ᵖ_ root using (IE; elaborate)

-- A program's emission set, its elaborated program's, and the batcher's on top,
-- each subscribed at the root.
eventsᵀ : ∀ {A} → SObs [] A → EmissionSet A
eventsᵀ o = enter (⟦ o ⟧ᵀ []) root

elaboratedᵀ : ∀ {A} → SObs [] A → EmissionSet (IE A)
elaboratedᵀ o = enter (⟦ elaborate o ⟧ᵀ []) root

batchedᵀ : ∀ {A} → SObs [] A → EmissionSet (IE (List A))
batchedᵀ o = enter (⟦ batchedObs o ⟧ᵀ []) root

------------------------------------------------------------------------
-- Readings of the rows met

-- The rows a reader at the root meets first.
Met : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Met t rs = Run t nothing rs

-- The values among them, each at its position.
outsᵀ : ∀ {A} → List (Pos × Ev A) → List (Pos × A)
outsᵀ []                 = []
outsᵀ ((q , out a) ∷ rs) = (q , a) ∷ outsᵀ rs
outsᵀ (_ ∷ rs)           = outsᵀ rs

valuesᵀ : ∀ {A} → List (Pos × Ev A) → List A
valuesᵀ rs = L.map proj₂ (outsᵀ rs)

batchesOutᵀ : ∀ {A} → List (Pos × Ev (IE (List A))) → List (Pos × List A)
batchesOutᵀ rs = stamped (valuesᵀ rs)

joinedᵀ : ∀ {A} → List (Pos × Ev (IE (List A))) → List A
joinedᵀ rs = concat (L.map proj₂ (batchesOutᵀ rs))

-- The spec's grouping of the values met, its last group kept only once
-- the run is over.
groupedᵀ : ∀ {A} → Bool → List (Pos × Ev (IE A)) → List (Pos × List A)
groupedᵀ ov rs = closed ov (batchSimultaneousᴰ (stamped (valuesᵀ rs)))

-- The rows met reach the run's end: its completion, or nothing after.
Over : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Over t rs = Any (λ r → proj₂ r ≡ end) rs ⊎ Hush t (cursor nothing rs)

-- A grouping may keep its last group only once the run is over.
Closes : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Bool → Set
Closes t rs false = ⊤
Closes t rs true  = Over t rs

-- Past the row at `q`, the run leaves `q`'s instant after finitely many
-- rows: a row of another instant, the completion, or nothing after.
Exits : ∀ {A} → EmissionSet A → Pos → Set
Exits t q = Σ _ λ rs → Run t (just q) rs
          × (Any (λ r → instantOf (proj₁ r) ≢ instantOf q ⊎ proj₂ r ≡ end) rs ⊎ Hush t (cursor (just q) rs))

-- Every instant a reader meets is over after finitely many rows.
FiniteInstantsᵀ : ∀ {A} → EmissionSet A → Set
FiniteInstantsᵀ t = ∀ {rs q e} → Met t (rs ++ (q , e) ∷ []) → Exits t q

------------------------------------------------------------------------
-- The three relations, between emission sets

Joinsᵀ : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet A → Set
Joinsᵀ b e =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Met e rs′ × Prefix _≡_ (joinedᵀ rs) (valuesᵀ rs′)) ×
  (FiniteInstantsᵀ e → ∀ {rs′} → Met e rs′ → Σ _ λ rs → Met b rs × Prefix _≡_ (valuesᵀ rs′) (joinedᵀ rs))

Batchesᵀ : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
Batchesᵀ b x =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Σ Bool λ ov → Met x rs′ × Closes x rs′ ov × Prefix _≡_ (batchesOutᵀ rs) (groupedᵀ ov rs′)) ×
  (∀ {rs′ ov} → Met x rs′ → Closes x rs′ ov → Σ _ λ rs → Met b rs × Prefix _≡_ (groupedᵀ ov rs′) (batchesOutᵀ rs))

InstantsAgreeᵀ : ∀ {A} → EmissionSet (IE A) → Set
InstantsAgreeᵀ x = ∀ {rs} → Met x rs → AllPairs SameInstant (L.map named (outsᵀ rs))

------------------------------------------------------------------------
-- The statements: each the root case

Left-To-Rightᵀ : Set₁
Left-To-Rightᵀ = ∀ {A} (o : SObs [] A) → Joinsᵀ (batchedᵀ o) (eventsᵀ o)

Coherentᵀ : Set₁
Coherentᵀ = ∀ {A} (o : SObs [] A) → InstantsAgreeᵀ (elaboratedᵀ o) × InstantsAgreeᵀ (batchedᵀ o)

Batchableᵀ : Set₁
Batchableᵀ = ∀ {A} (o : SObs [] A) → Batchesᵀ (batchedᵀ o) (elaboratedᵀ o)

Positionedᵀ : Set₁
Positionedᵀ = ∀ {A} (o : SObs [] A) {rs} → Met (eventsᵀ o) rs → All Rooted (L.map proj₁ rs)

postulate
  left-to-rightᵀ : Left-To-Rightᵀ
  coherentᵀ      : Coherentᵀ
  batchableᵀ     : Batchableᵀ
  positionedᵀ    : Positionedᵀ
