{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, over the emission set: elaborate the author's
-- program, put `batchSimultaneous` on top, and what comes out is what
-- plain rxjs delivers, grouped by instant, released the moment each
-- instant is over.  Three statements, each closing a cheat the others
-- leave open.
--
-- `left-to-right`: the batches, joined back up, are the plain run's
-- values, in order.  Elaborating every program to `empty` is trivially
-- batched, and fails it.
--
-- `coherent`: two emits share a provenance exactly when they sit in one
-- instant, valueless ones too, both the elaborated run's and the
-- batcher's.  Stamping every emit alike, or each apart, fails it on the
-- elaborated run; on the batcher's, it pins a batch to the moment its
-- instant is over, since a batch released late sits in an instant that
-- is not its own.
--
-- `batchable`: the batches, each with its provenance, are the spec's
-- grouping of the elaborated run's values.  A batch restamped to the
-- instant it was released in, to pass `coherent`, fails it.
--
-- EACH IS TWO DIRECTIONS OVER PREFIXES, since a run need not end: what
-- has come out is within what the spec allows, and everything the spec
-- allows comes out eventually.  A prefix is the rows a reader of the
-- emission set meets first (`denotation.Read.Run`).  Only
-- `left-to-right`'s second half needs the plain run's instants finite: an
-- instant that never ends is never released, so `ones` batched shows
-- nothing, as specified.
module simultaneous.Statement where

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
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import denotation.Events using (_≟ᵖ_; Pos; Timeline; root)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; enter; ⟦_⟧)
open import denotation.Read using (Run; Hush; cursor)
open import simultaneous.InstEmit using (InstEmit)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; Rooted; stamped; closed)

open Elaborate {C = Timeline} _≟ᵖ_ root using (E; IE; elaborate; batchSimultaneous)

-- The program the author's stands for: elaborated, batched on top.
batchedObs : ∀ {A} → SObs [] A → E [] (IE (List A))
batchedObs o = batchSimultaneous (elaborate o)

-- A program's emission set, its elaborated program's, and the batcher's on top,
-- each subscribed at the root.
events : ∀ {A} → SObs [] A → EmissionSet A
events o = enter (⟦ o ⟧ []) root

elaborated : ∀ {A} → SObs [] A → EmissionSet (IE A)
elaborated o = enter (⟦ elaborate o ⟧ []) root

batched : ∀ {A} → SObs [] A → EmissionSet (IE (List A))
batched o = enter (⟦ batchedObs o ⟧ []) root

------------------------------------------------------------------------
-- Readings of the rows met

-- The rows a reader at the root meets first.
Met : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Met t rs = Run t nothing rs

-- The values among them, each at its position.
outs : ∀ {A} → List (Pos × Ev A) → List (Pos × A)
outs []                 = []
outs ((q , out a) ∷ rs) = (q , a) ∷ outs rs
outs (_ ∷ rs)           = outs rs

values : ∀ {A} → List (Pos × Ev A) → List A
values rs = L.map proj₂ (outs rs)

batchesOut : ∀ {A} → List (Pos × Ev (IE (List A))) → List (Pos × List A)
batchesOut rs = stamped (values rs)

joined : ∀ {A} → List (Pos × Ev (IE (List A))) → List A
joined rs = concat (L.map proj₂ (batchesOut rs))

-- The spec's grouping of the values met, its last group kept only once
-- the run is over.
grouped : ∀ {A} → Bool → List (Pos × Ev (IE A)) → List (Pos × List A)
grouped ov rs = closed ov (batchSimultaneousᴰ (stamped (values rs)))

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
FiniteInstants : ∀ {A} → EmissionSet A → Set
FiniteInstants t = ∀ {rs q e} → Met t (rs ++ (q , e) ∷ []) → Exits t q

------------------------------------------------------------------------
-- The three relations, between emission sets

Joins : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet A → Set
Joins b e =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Met e rs′ × Prefix _≡_ (joined rs) (values rs′)) ×
  (FiniteInstants e → ∀ {rs′} → Met e rs′ → Σ _ λ rs → Met b rs × Prefix _≡_ (values rs′) (joined rs))

Batches : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
Batches b x =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Σ Bool λ ov → Met x rs′ × Closes x rs′ ov × Prefix _≡_ (batchesOut rs) (grouped ov rs′)) ×
  (∀ {rs′ ov} → Met x rs′ → Closes x rs′ ov → Σ _ λ rs → Met b rs × Prefix _≡_ (grouped ov rs′) (batchesOut rs))

-- coherent: provenances agree exactly when instants do.
SameInstant : Pos × Pos → Pos × Pos → Set
SameInstant (p , i) (q , j) = (i ≡ j) ⇔ (instantOf p ≡ instantOf q)

-- An emit at its position, read as its position and its name.
named : ∀ {A} → Pos × IE A → Pos × Pos
named (p , x) = p , InstEmit.instant x

InstantsAgree : ∀ {A} → EmissionSet (IE A) → Set
InstantsAgree x = ∀ {rs} → Met x rs → AllPairs SameInstant (L.map named (outs rs))

------------------------------------------------------------------------
-- The statements: each the root case

Left-To-Right : Set₁
Left-To-Right = ∀ {A} (o : SObs [] A) → Joins (batched o) (events o)

Coherent : Set₁
Coherent = ∀ {A} (o : SObs [] A) → InstantsAgree (elaborated o) × InstantsAgree (batched o)

Batchable : Set₁
Batchable = ∀ {A} (o : SObs [] A) → Batches (batched o) (elaborated o)

Positioned : Set₁
Positioned = ∀ {A} (o : SObs [] A) {rs} → Met (events o) rs → All Rooted (L.map proj₁ rs)

postulate
  left-to-right : Left-To-Right
  coherent      : Coherent
  batchable     : Batchable
  positioned    : Positioned
