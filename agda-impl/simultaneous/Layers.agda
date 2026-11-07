{-# OPTIONS --guardedness #-}

-- A PROGRAM READ THROUGH THE OPERATOR ON TOP: what a subscriber to a
-- `scan`, or to an `each` (a merge of `of`s), meets, read back as what a
-- subscriber to its source meets.  Generic in the source: nothing here
-- knows the batcher.
module simultaneous.Layers where

open import Data.List using (List; []; _∷_; concatMap)
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; scan)
open import denotation.Events using (Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; enter; ⟦_⟧)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values; Ends)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (each)

-- A closed program's emission set, subscribed at the root.
at : ∀ {A} → Obs Timeline [] A → EmissionSet A
at s = enter (⟦ s ⟧ []) root

-- The states a fold passes through, one per value.
scans : ∀ {A B : Set} → (B → A → B) → B → List A → List B
scans f z []       = []
scans f z (a ∷ as) = f z a ∷ scans f (f z a) as

-- A SCAN ENDS WHEN ITS SOURCE DOES, its values the fold's states.
postulate
  scan-ends-out : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {sc} → Met (at (scan f z s)) sc → Ends sc
                → Σ _ λ rx → Met (at s) rx × Ends rx × values sc ≡ scans f z (values rx)
  scan-ends-in  : ∀ {A B} (f : B → A → B) z (s : Obs Timeline [] A) {rx} → Met (at s) rx → Ends rx
                → Σ _ λ sc → Met (at (scan f z s)) sc × Ends sc × values sc ≡ scans f z (values rx)

-- AN EACH ENDS WHEN ITS SOURCE DOES, every lane's values out in turn.
postulate
  each-ends-out : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {rs} → Met (at (each f s)) rs → Ends rs
                → Σ _ λ sc → Met (at s) sc × Ends sc × values rs ≡ concatMap f (values sc)
  each-ends-in  : ∀ {X Y} (f : X → List Y) (s : Obs Timeline [] X) {sc} → Met (at s) sc → Ends sc
                → Σ _ λ rs → Met (at (each f s)) rs × Ends rs × values rs ≡ concatMap f (values sc)
