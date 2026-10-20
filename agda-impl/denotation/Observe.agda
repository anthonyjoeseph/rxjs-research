{-# OPTIONS --guardedness #-}

module denotation.Observe where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Timeline; root)
open import denotation.MonotonicList using (observe)
open import denotation.Denote using (⟦_⟧)

-- What a subscriber at the root is shown.
events : ∀ {A} → Obs Timeline [] A → Events A
events o = observe (⟦ o ⟧ []) root
