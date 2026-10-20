{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, over the denotation: elaborate the author's
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
-- instant, valueless ones too, both the elaborated run's and the batcher's.  Stamping every
-- emit alike, or each apart, fails it on the elaborated run; on the
-- batcher's, it pins a batch to the moment its instant is over, since a
-- batch released late sits in an instant that is not its own.
--
-- `batchable`: the batches, each with its provenance, are the spec's
-- grouping of the elaborated run's values.  A batch restamped to the
-- instant it was released in, to pass `coherent`, fails it.
--
-- EACH IS TWO DIRECTIONS OVER PREFIXES, since a run need not end: what
-- has come out is within what the spec allows, and everything the spec
-- allows comes out eventually.  Only `left-to-right`'s second half needs
-- the plain run's instants finite: an instant that never ends is never
-- released, so `ones` batched shows nothing, as specified.
module simultaneous.Statement where

open import Data.List using (List; []; concat; map)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ; _,_; proj₂)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList.Events using (Events; Pos)
open import denotation.Observe using (events)
open import simultaneous.InstEmit using (InstEmit; Provenance)
open import simultaneous.SObs using (SObs; elaborate; batchSimultaneous)
open import simultaneous.Spec using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; outs; values; positions; over; FiniteInstants; Rooted; stamped; closed)

-- The program the author's stands for: elaborated, batched on top.
batchedObs : ∀ {A} → SObs [] A → SObs [] (InstEmit (List A))
batchedObs o = batchSimultaneous (elaborate o)

-- The elaborated program's run, and the batcher's on top of it.
elaborated : ∀ {A} → SObs [] A → Events (InstEmit A)
elaborated o = events (elaborate o)

batched : ∀ {A} → SObs [] A → Events (InstEmit (List A))
batched o = events (batchedObs o)

-- The batches among the batcher's first n events, each with its provenance.
batchesOut : ∀ {A} → ℕ → SObs [] A → List (Provenance × List A)
batchesOut n o = stamped (values n (batched o))

-- The spec's grouping of the elaborated run's first m events, but for an
-- instant that may still be running.
grouped : ∀ {A} → ℕ → SObs [] A → List (Provenance × List A)
grouped m o = closed (over m (elaborated o)) (batchSimultaneousᴰ (stamped (values m (elaborated o))))

------------------------------------------------------------------------
-- left-to-right

joined : ∀ {A} → ℕ → SObs [] A → List A
joined n o = concat (map proj₂ (batchesOut n o))

plain : ∀ {A} → ℕ → SObs [] A → List A
plain m o = values m (events o)

Left-To-Right : Set₁
Left-To-Right = ∀ {A} (o : SObs [] A) →
  (∀ n → Σ ℕ λ m → Prefix _≡_ (joined n o) (plain m o)) ×
  (FiniteInstants (events o) → ∀ m → Σ ℕ λ n → Prefix _≡_ (plain m o) (joined n o))

------------------------------------------------------------------------
-- coherent

SameInstant : Pos × Provenance → Pos × Provenance → Set
SameInstant (p , i) (q , j) = (i ≡ j) ⇔ (instantOf p ≡ instantOf q)

InstantsAgree : ∀ {A} → Events (InstEmit A) → Set
InstantsAgree e = ∀ n → AllPairs SameInstant (map (λ (p , x) → p , InstEmit.instant x) (outs n e))

Coherent : Set₁
Coherent = ∀ {A} (o : SObs [] A) → InstantsAgree (elaborated o) × InstantsAgree (batched o)

------------------------------------------------------------------------
-- batchable

Batchable : Set₁
Batchable = ∀ {A} (o : SObs [] A) →
  (∀ n → Σ ℕ λ m → Prefix _≡_ (batchesOut n o) (grouped m o)) ×
  (∀ m → Σ ℕ λ n → Prefix _≡_ (grouped m o) (batchesOut n o))

-- The anchor for `instantOf`: every position a program's run shows
-- lies under the subscribe frame or under one timer cascade.
Positioned : Set₁
Positioned = ∀ {A} (o : SObs [] A) n → All Rooted (positions n (events o))

postulate
  positioned    : Positioned
  left-to-right : Left-To-Right
  coherent      : Coherent
  batchable     : Batchable
