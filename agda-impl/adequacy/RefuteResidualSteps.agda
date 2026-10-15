{-# OPTIONS --guardedness #-}

-- `residual-steps` refuted as stated of every node.  A joiner already
-- told its end, under a connect whose source still runs: the stepper
-- feeds it the source's value, which it then shows; the meaning reads a
-- told joiner as its end alone, so the value is in no residual of it.
module adequacy.RefuteResidualSteps where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix)
import denotation.Unfold as U
open import adequacy.Content using (module Honesty)
open Honesty ⊤ using (Has; Steps; atOut; pastOut; pastSkip)

told-under-live : U.Node [] ⊤
told-under-live = U.connectᶜ (U.joinᶜ (here refl) (ix 0 ∷ []) [] (just (ix 2 ∷ []))) (U.live (U.ofᶜ (ix 1 ∷ []) 0 (tt ∷ [])))

refuted : (∀ g → Steps (Honesty.residual ⊤ g) (U.step g)) → ⊥
refuted rs with proj₂ (rs told-under-live) atOut
... | pastSkip ()
