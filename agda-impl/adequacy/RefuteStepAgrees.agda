{-# OPTIONS --guardedness #-}

-- `step-agrees` refuted, the stepper's joiner shown every source step as
-- `M.rejoin` shows it.  A lane a flatMap has yet to subscribe reads its
-- connect's source from where the ghost's source stands, so the meaning
-- shows it a skip under its own position for each source step before its
-- join; a step of the source leaves one fewer.
module adequacy.RefuteStepAgrees where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (ix; Timeline; skip⁼)
open import Tree using (Obs; Later; of; connect; connected; defer; flatMap; mergeᶠ)
import denotation.Unfold as U
open import adequacy.Strong using (module Strongly)
open import adequacy.Content using (module Honesty)
open Strongly ⊤ using (sane-subscribe)
open Honesty ⊤ using (step-agrees)

twice : Later Timeline [] ⊤
Later.force twice = of (tt ∷ tt ∷ [])

-- A lane per value of the joined source, each joining it again.
program : Obs Timeline [] ⊤
program = connect (defer twice) (flatMap (mergeᶠ nothing) (λ _ → connected (here refl)) (connected (here refl)))

lanes : U.Node [] ⊤
lanes = U.subscribe program (ix 0 ∷ [])

refuted : ⊥
refuted with step-agrees lanes (sane-subscribe {ν = []ᴬ} program (ix 0 ∷ []) (λ ())) 6
... | skip⁼ (skip⁼ (skip⁼ (skip⁼ (skip⁼ ()))))
