------------------------------------------------------------------
-- THE README'S SEMANTICS, AS PROOFS OVER THE SPEC.  The README is the
-- reference for how `batchSimultaneous` behaves (Anthony); what it
-- says in prose, this module says in Agda, and nothing here reads an
-- implementation.
--
-- TWO FACTS CARRY EVERY CLAIM IT MAKES.  Batching never reorders --
-- the batches, joined back up, are the values in arrival order.  And
-- over a well-formed run there is one batch per arrival that carried a
-- value, holding exactly that arrival's values
-- (`Verify-Batch-Simultaneous.Well-Formed.wf-batches` and
-- `wf-arrival-batch`, which live beside the record they read).
------------------------------------------------------------------
module Readme-Semantics where

open import Data.List    using (List; []; _∷_; _++_; _∷ʳ_; concat; map)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)
import Spec

module _ {Instant : Set} (_≟_ : DecidableEquality Instant) where
  open Spec Instant _≟_ using (spec-batchSimultaneous; batchFrom)

  private
    batchFrom-order : ∀ {A : Set} (i : Instant) (vs : List A) (xs : List (Instant × A))
                    → concat (batchFrom i vs xs) ≡ vs ++ map proj₂ xs
    batchFrom-order i vs []             = refl
    batchFrom-order i vs ((j , v) ∷ xs) with i ≟ j
    ... | yes _ = trans (batchFrom-order i (vs ∷ʳ v) xs) (++-assoc vs (v ∷ []) (map proj₂ xs))
    ... | no  _ = cong (vs ++_) (batchFrom-order j (v ∷ []) xs)

  -- BATCHING NEVER REORDERS: for `1 5 3 7 0`, `[1,5] [3] [7,0]` joins
  -- back to `1 5 3 7 0`, and so does every batching the spec gives;
  -- `[1,5,3,0,7]` joins to something else, so the spec never gives it.
  spec-preserves-order : ∀ {A : Set} (xs : List (Instant × A))
                       → concat (spec-batchSimultaneous xs) ≡ map proj₂ xs
  spec-preserves-order []             = refl
  spec-preserves-order ((i , v) ∷ xs) = batchFrom-order i (v ∷ []) xs
