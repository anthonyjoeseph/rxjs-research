------------------------------------------------------------------
-- DRYNESS IS A PROPERTY OF EVENTS, and this module says so at the
-- shapes the subscription machine actually builds.
--
-- `hasDry` is a disjunctive fold over emits and then over their
-- events, so every fact here is one induction and none of them knows
-- anything about the descent.  They are separated from the descent
-- proof for that reason: a clause that assembles a burst out of
-- `init`, `value` and `close … exhausted` is dry-free for a reason
-- that has nothing to do with which triple it was standing at, and
-- mixing the two would put arithmetic beside a list induction.
--
-- RECOVERY: git show 234074e:agda/src/Verify-Rank-Sufficient/Dry-Emits.agda
--   restores the SHELF this module was cut back to one lemma from: the
--   branch, the one-emit burst, the payload run, the cold tail, the
--   one-shot source, the plumbing retag and the connect emit.  Each is
--   a five-line induction over the shape a clause BUILDS, and each is
--   owed again the moment `subscribeE⇓-nodry` is a body rather than a
--   leaf — one arm per shape, which is what they were written for.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Dry-Emits where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (InstEmit)
open import Rx.Evaluator using (hasDry; dryEvent)

-- dryness of a concatenation is dryness of either half
hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry xs ≡ false → hasDry ys ≡ false → hasDry (xs ++ ys) ≡ false
hasDry-++ []         ys hx hy = hy
hasDry-++ (em ∷ ems) ys hx hy with any dryEvent (InstEmit.events em)
... | true  = hx
... | false = hasDry-++ ems ys hx hy
