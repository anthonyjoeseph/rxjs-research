-- ONLINE-NESS: the batcher never reopens a group it has closed.
--
-- HISTORY, because the shape here is the whole content.  This
-- claim used to read
--
--   Prefix _≡_ (foldBatch batch-init xs) (foldBatch batch-init (xs ++ ys))
--
-- and it is FALSE.  The batcher is `foldBatch batch-init`, and
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
-- the constructors are renamed because `[]` and `_∷_` would otherwise
-- resolve to `Data.List`'s at every use site below
open import Data.List.Relation.Binary.Prefix.Heterogeneous
  using (Prefix) renaming ([] to nilᴾ; _∷_ to _∷ᴾ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Rx.Prim        using (InstEmit)
open import Implementation using (foldBatch; BatchSt; batch-init;
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

------------------------------------------------------------------
-- The one lemma, and it is about `Prefix` rather than about batching.
------------------------------------------------------------------

-- PREPENDING A COMMON RUN PRESERVES A PREFIX.  This is the whole of
-- the step case below: the two folds agree on everything `step-batch`
-- emits for the head and differ only in the tail, so the induction
-- hands back a prefix of the tails and this carries it past the shared
-- part.
prefix-++ᵖ : ∀ {A : Set} (zs : List A) {xs ys : List A}
           → Prefix _≡_ xs ys → Prefix _≡_ (zs ++ xs) (zs ++ ys)
prefix-++ᵖ []       p = p
prefix-++ᵖ (z ∷ zs) p = refl ∷ᴾ prefix-++ᵖ zs p

------------------------------------------------------------------
-- Online-ness.
------------------------------------------------------------------

-- THE STATEMENT IS GENERALISED OFF `batch-init` BEFORE IT IS PROVEN,
-- which is the only real step in this file.  The induction is on `xs`,
-- and after one emit the fold stands at `proj₂ (step-batch x st)`
-- rather than at the initial state -- so a claim pinned to
-- `batch-init` has no induction hypothesis to appeal to.  Quantifying
-- over the state costs nothing, since nothing below looks inside one.
--
-- AND THAT IS WHY THIS IS SHORT: no property of `step-batch` is needed
-- at all.  Online-ness is not a fact about batching, it is a fact
-- about the SHAPE of the fold -- each step's output is committed
-- before the next step runs, so the only difference `ys` can make is
-- further out. `foldBatch-no-flush` is what makes that sayable, by
-- dropping the terminal flush that would otherwise force a
-- still-growing batch out on the left and contradict it.
online-from : ∀ {A : Set} (st : BatchSt A) (xs ys : List (InstEmit A))
            → Prefix _≡_ (foldBatch-no-flush st xs) (foldBatch st (xs ++ ys))
online-from st []       ys = nilᴾ
online-from st (x ∷ xs) ys =
  prefix-++ᵖ (proj₁ (step-batch x st))
             (online-from (proj₂ (step-batch x st)) xs ys)

-- online-ness (extrinsic no-lookahead): once a group is CLOSED it is never
-- reopened, so the groups emitted while reading `xs` are a prefix of the
-- full output on any extension `xs ++ ys`.  The open tail is deliberately
-- excluded on the left — it is not yet a group.
batch-online :
  ∀ {A} (xs ys : List (InstEmit A)) →
  Prefix _≡_ (foldBatch-no-flush batch-init xs)
             (foldBatch batch-init (xs ++ ys))
batch-online = online-from batch-init
