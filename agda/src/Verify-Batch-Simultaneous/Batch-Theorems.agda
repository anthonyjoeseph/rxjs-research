-- ONLINE-NESS: the batcher never reopens a group it has closed.
--
-- HISTORY, because the shape here is the whole content.  This
-- claim used to read
--
--   Prefix _≡_ (impl-batchSimultaneous xs) (impl-batchSimultaneous (xs ++ ys))
--
-- and it is FALSE.  `impl-batchSimultaneous = foldBatch batch-init`, and
-- `foldBatch st [] = flushBatch st` — so on `xs` alone the batcher FLUSHES a
-- batch that is still open, and on `xs ++ ys` that same batch keeps growing.
-- Machine refutation in ``git show 94a5a3c^:agda/probe/Battery-Batch-Online.agda``
-- (`batch-online-refuted`, a proven `¬`): two emits flush to `value [1]`, while
-- three close the same batch as `value [1,2]`, so the first elements differ and
-- no prefix relation can hold.  The old statement's own trailing comments —
-- "modulo the open tail, i.e. compare pre-flush" and the `nb:` asking for "fold
-- xs's emitted groups prefix fold (xs++ys)'s" — had said this all along, in
-- prose, where neither the typechecker nor `grep` could act on it.  The lesson
-- is the repo's own: a qualification that lives in a comment is not part of the
-- claim.  State it.
--
-- So the honest statement compares only what the fold has actually EMITTED,
-- which is what `foldBatch-no-flush` is for.  Every group it returns was closed
-- mid-stream by `paidOff`, and a closed group is final — that is exactly the
-- no-lookahead property, and it is now what the type says.
--
-- AUTHORITY.  Anthony delegated the SHAPE to this session,
-- conditional on the main proof not depending on this claim.  That condition was
-- then verified, not assumed: `Batch-Theorems` is imported ONLY by Main,
-- `The-Proof.agda` does not import it at all, and `batch-online` has no in-repo
-- consumer.  So `formal-verification-batchSimultaneous` cannot be affected by
-- anything written here — this is a leaf claim Main asserts BESIDE the theorem,
-- which makes its shape a reporting question rather than a soundness one.  If a
-- future change ever routes the main proof through this module, that delegation
-- has lapsed and the shape needs asking about again.
module Verify-Batch-Simultaneous.Batch-Theorems where

open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Rx.Prim        using (InstEmit)
open import Implementation using (impl-batchSimultaneous; BatchSt; batch-init;
                                 step-batch)

-- The fold's EMITTED groups: `foldBatch` (.Implementation) with its terminal
-- `flushBatch` removed.  It differs from `foldBatch` in exactly one clause, and
-- that one clause is the entire point — the flush is what forces a
-- still-growing batch out early and makes the unqualified prefix claim false.
-- This lives here rather than in `Implementation` on purpose: `Implementation`
-- mirrors the real rxjs pipeline operator-for-operator (see CLAUDE.md), and a
-- fold that deliberately drops its own terminal flush is a proof-side
-- projection, not something an rxjs pipeline does.
foldBatch-no-flush : ∀ {A : Set} → BatchSt A → List (InstEmit A)
                   → List (InstEmit (List A))
foldBatch-no-flush st []       = []
foldBatch-no-flush st (x ∷ xs) =
  let (out , st′) = step-batch x st
  in out ++ foldBatch-no-flush st′ xs

postulate
  -- online-ness (extrinsic no-lookahead): once a group is CLOSED it is never
  -- reopened, so the groups emitted while reading `xs` are a prefix of the
  -- full output on any extension `xs ++ ys`.  The open tail is deliberately
  -- excluded on the left — it is not yet a group.
  batch-online :
    ∀ {A} (xs ys : List (InstEmit A)) →
    Prefix _≡_ (foldBatch-no-flush batch-init xs)
               (impl-batchSimultaneous (xs ++ ys))
