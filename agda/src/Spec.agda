------------------------------------------------------------------
-- THE SPEC: `batchSimultaneous` cuts a stream into maximal runs of one
-- instant, and never reorders.
--
-- The input is what a subscriber sees, each value tagged with the
-- instant that caused it; the output is the batches.  Values leave in
-- exactly the order they arrived, and later in the array means later
-- in time -- `[1,5] [3] [7,0]` is a batching of `1 5 3 7 0`, and
-- `[1,5,3,0,7]` is not one of anything (`Readme-Semantics`).
--
-- AN INSTANT IS OPAQUE, AND THAT IS WHY THE MODULE IS PARAMETERISED.
-- The spec asks one question of an instant -- is it the same one as the
-- last? -- so it is given equality and nothing else.  No order, no
-- successor, no arithmetic: whatever an implementation uses to name
-- its instants, the spec cannot tell and does not care.
------------------------------------------------------------------
open import Relation.Binary.Definitions using (DecidableEquality)

module Spec (Instant : Set) (_≟_ : DecidableEquality Instant) where

open import Data.List    using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

-- the batch open at instant `i`, holding `vs` so far
batchFrom : ∀ {A : Set} → Instant → List A → List (Instant × A) → List (List A)
batchFrom i vs []             = vs ∷ []
batchFrom i vs ((j , v) ∷ xs) with i ≟ j
... | yes _ = batchFrom i (vs ∷ʳ v) xs
... | no  _ = vs ∷ batchFrom j (v ∷ []) xs

spec-batchSimultaneous : ∀ {A : Set} → List (Instant × A) → List (List A)
spec-batchSimultaneous []             = []
spec-batchSimultaneous ((i , v) ∷ xs) = batchFrom i (v ∷ []) xs
