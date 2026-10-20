-- THE SPEC: `batchSimultaneous` cuts a stream into maximal runs of one
-- instant, and never reorders.  Values leave in exactly the order they
-- arrived, and later in the list means later in time: `[1,5] [3] [7,0]`
-- is a batching of `1 5 3 7 0`, and `[1,5,3,0,7]` is not one of
-- anything.  Each batch keeps its instant, so a batched stream is again
-- an InstEmit stream.
--
-- The spec asks one question of an instant, whether it is the last one
-- again, so it is generic in the names and reads their equality alone.
open import Relation.Binary.Definitions using (DecidableEquality)

module simultaneous.Spec {N : Set} (_≟_ : DecidableEquality N) where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

-- the batch open at instant `i`, holding `vs` so far
batchFrom : ∀ {A : Set} → N → List A → List (N × A) → List (N × List A)
batchFrom i vs []             = (i , vs) ∷ []
batchFrom i vs ((j , v) ∷ xs) with i ≟ j
... | yes _ = batchFrom i (vs ∷ʳ v) xs
... | no  _ = (i , vs) ∷ batchFrom j (v ∷ []) xs

batchSimultaneousᴰ : ∀ {A : Set} → List (N × A) → List (N × List A)
batchSimultaneousᴰ []             = []
batchSimultaneousᴰ ((i , v) ∷ xs) = batchFrom i (v ∷ []) xs
