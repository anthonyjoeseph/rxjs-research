module Verify-Batch-Simultaneous.Batch-Theorems where

open import Data.List    using (List; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Rx.Prim        using (InstEmit)
open import Implementation using (impl-batchSimultaneous)

postulate
  -- online-ness (extrinsic no-lookahead): once a group is closed it is
  -- never reopened — output on a prefix is a prefix of output
  batch-online :
    ∀ {A} (xs ys : List (InstEmit A)) →
    Prefix _≡_ (impl-batchSimultaneous xs)              -- modulo the open tail,
              (impl-batchSimultaneous (xs ++ ys))       -- i.e. compare pre-flush
    -- nb: state precisely as "fold xs's emitted groups prefix fold (xs++ys)'s"
