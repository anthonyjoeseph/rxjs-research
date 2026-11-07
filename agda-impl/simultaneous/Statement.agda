{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, over the emission set: elaborate the author's
-- program, put `batchSimultaneous` on top, and what comes out is what
-- plain rxjs delivers, grouped by instant, released the moment each
-- instant is over.  Three statements, each closing a cheat the others
-- leave open.
--
-- `left-to-right`: the batches, joined back up, are the plain run's
-- values, in order, and the batched run completes exactly when the plain
-- one does, all its values out.  Elaborating every program to `empty` is
-- trivially batched, and fails it.
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
-- AN INSTANT'S END IS A FACT OF THE ROWS, NOT OF WHAT IS SHOWN: work no
-- subscriber sees (a skip, a pin) still runs in some instant, so an
-- instant is left by every row past it.  Those are read off the
-- emission set directly, over its reached rows (`Seen`), never through a
-- reader.
--
-- AN INSTANT OVER IS ENOUGH, THE RUN NEED NOT BE: a batch is released
-- the moment its instant is, though work no subscriber sees runs on.
--
-- EACH IS TWO DIRECTIONS OVER PREFIXES, since a run need not end: what
-- has come out is within what the spec allows, and everything the spec
-- allows comes out eventually.  A prefix is what a subscriber is shown
-- first (`denotation.Read.Meets`), the reader adequacy reads by.  Only
-- `left-to-right`'s second half needs the plain run's instants finite: an
-- instant that never ends is never released, so `ones` batched shows
-- nothing, as specified.
module simultaneous.Statement where

open import Data.Bool using (true)
open import Data.List using (List; [])
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym; trans to ≡-trans)

open import denotation.Events using (_≟ᵖ_; Pos; Timeline; root; fresh)
open import denotation.EmissionSet using (Ev; Seen)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Flatten as F
open import simultaneous.Readings using (Rooted; stamped)
open import simultaneous.Relations using (events; elaborated; batched; Met; values; batchesOut; joined; vals; grouped; Ends; FiniteInstants;
  Joins; Batches; InstantsAgree; Erases; Settles)
open import simultaneous.Batcher using (batcher-ends)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE)

postulate
  erases       : ∀ {A} (o : SObs [] A) → Erases (elaborated o) (events o)
  settles      : ∀ {A} (o : SObs [] A) → Settles (elaborated o) (events o)

------------------------------------------------------------------------
-- The statements: each the root case

Left-To-Right : Set₁
Left-To-Right = ∀ {A} (o : SObs [] A) → Joins (batched o) (events o)

Coherent : Set₁
Coherent = ∀ {A} (o : SObs [] A) → InstantsAgree (elaborated o) × InstantsAgree (batched o)

Batchable : Set₁
Batchable = ∀ {A} (o : SObs [] A) → Batches (batched o) (elaborated o)

Positioned : Set₁
Positioned = ∀ {A} (o : SObs [] A) {k e} → Seen (events o) k e → Rooted k

postulate
  coherent      : Coherent
  batchable     : Batchable
  positioned    : Positioned

-- The batches, joined, are within the elaborated run's values, and those
-- are the plain run's; the batches closed, they reach as far.
left-to-right : Left-To-Right
left-to-right o = early , late , ends-out , ends-in
  where
    open F _≟ᵖ_ using (prefix-trans; prefix-≡; prefix-map; prefix-concat; joined-closed; joined-batches)

    -- what a prefix of the grouping joins to
    joined-within : ∀ {A} (rs : List (Pos × Ev (IE (List A)))) {ov} rx →
                    Prefix _≡_ (batchesOut rs) (grouped ov rx) → Prefix _≡_ (joined rs) (vals rx)
    joined-within rs {ov} rx p = prefix-trans (prefix-concat (prefix-map proj₂ p)) (joined-closed ov (stamped (values rx)))

    early : ∀ {rs} → Met (batched o) rs → Σ _ λ rs′ → Met (events o) rs′ × Prefix _≡_ (joined rs) (values rs′)
    early {rs} m with proj₁ (batchable o) m
    ... | rx , ov , mx , _ , p with proj₁ (erases o) mx
    ...   | rs′ , me , q = rs′ , me , prefix-trans (joined-within rs rx p) q

    late : FiniteInstants (events o) → ∀ {rs′} → Met (events o) rs′ → Σ _ λ rs → Met (batched o) rs × Prefix _≡_ (values rs′) (joined rs)
    late fin m with proj₁ (proj₂ (erases o)) m
    ... | rx , mx , p with settles o fin mx
    ...   | rx′ , mx′ , cl , q with proj₂ (batchable o) {ov = true} mx′ cl
    ...     | rs , mb , r = rs , mb , prefix-trans p (prefix-trans q
                (prefix-trans (prefix-≡ (≡-sym (joined-batches (stamped (values rx′))))) (prefix-concat (prefix-map proj₂ r))))

    ends-out : ∀ {rs} → Met (batched o) rs → Ends rs → Σ _ λ rs′ → Met (events o) rs′ × Ends rs′ × joined rs ≡ values rs′
    ends-out m en with proj₁ (batcher-ends o) m en
    ... | rx , mx , ex , eq with proj₁ (proj₂ (proj₂ (erases o))) mx ex
    ...   | rs′ , me , es , eq′ = rs′ , me , es , ≡-trans eq eq′

    ends-in : ∀ {rs′} → Met (events o) rs′ → Ends rs′ → Σ _ λ rs → Met (batched o) rs × Ends rs × values rs′ ≡ joined rs
    ends-in m en with proj₂ (proj₂ (proj₂ (erases o))) m en
    ... | rx , mx , ex , eq with proj₂ (batcher-ends o) mx ex
    ...   | rs , mb , eb , eq′ = rs , mb , eb , ≡-trans eq eq′
