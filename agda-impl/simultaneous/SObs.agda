-- THE AUTHOR'S PROGRAM AND ITS ELABORATION.  An `SObs` is what a user
-- writes against srxjs: the same primitives as plain rxjs, so the same
-- tree, and its plain reading is the tree itself.  `batchSimultaneous`
-- stands only on top, applied to the elaboration, so it is not a former.
--
-- `elaborate` is srxjs written in rxjs: each primitive rebuilt over
-- InstEmits, so that every emit carries its instant and the counting
-- protocol.  `batchSimultaneous` is a program too, built from the
-- primitives, so it runs on every runtime the tree does.
module simultaneous.SObs where

open import Data.List using (List; map)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import simultaneous.InstEmit using (InstEmit)

SObs : List Set → Set → Set₁
SObs = Obs Timeline

postulate
  -- A shared source is elaborated too, so the context is of InstEmits.
  elaborate : ∀ {Γ A} → SObs Γ A → Obs Timeline (map InstEmit Γ) (InstEmit A)

  batchSimultaneous : ∀ {C Γ A} → Obs C Γ (InstEmit A) → Obs C Γ (InstEmit (List A))
