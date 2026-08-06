-- BATTERY: batch-online (Verify-Batch-Simultaneous.Batch-Theorems:12)
-- Task 0b: probe the postulate AS WRITTEN, build the counterexample,
-- and formulate the corrected pre-flush form.
--
-- IMPORT STRATEGY: only Implementation and Rx.Prim.  Neither touches
-- the modified Verify-Budget-Sufficient chain, so all .agdai files
-- are fresh.
--
-- FINDINGS (see below):
--   REFUTED-AS-WRITTEN: YES.  Two refl checks show the first batch
--   emitted by [em1,em2] has values [1] while [em1,em2,em3] emits
--   a batch with values [1,2].  A Prefix would require them equal,
--   but 1 ≠ 2 (see batch-online-refuted below).
--
--   CORRECTED FORM: replace `impl-batchSimultaneous xs` (which flushes
--   the open tail) with `foldBatch-no-flush batch-init xs` (same fold,
--   no terminal flushBatch).  All batches emitted by foldBatch-no-flush
--   were closed by paidOff mid-stream and are final; they form a genuine
--   prefix of any extension.  Concrete check: foldBatch-no-flush [em1,em2]
--   = [] (nothing paid off yet) and foldBatch-no-flush [em1,em2,em3]
--   = [(value [1,2] ∷ []) at 1 from 0 as delivery] (paid off by em3).
module Battery-Batch-Online where

open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; length)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Bool    using (Bool; true; false)
open import Data.Empty   using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Data.List.Relation.Binary.Prefix.Heterogeneous as Pref

open import Rx.Prim using (Id; Source; InstEmit; InstEvent; _at_from_as_;
                           init; value; close; handoff; complete;
                           EmitKind; subscribe; delivery; plumbing;
                           CloseReason; exhausted)
open import Implementation using (impl-batchSimultaneous;
                                   foldBatch; flushBatch; step-batch;
                                   batch-init; BatchSt; OpenBatch)

----------------------------------------------------------------------
-- § 1  THE COUNTEREXAMPLE
----------------------------------------------------------------------
-- em1: subscribe frame that registers source 0 TWICE.
--      live becomes [0, 0].
-- em2: first delivery from source 0 at instant 1.
--      settleBatch delivery 0 [0,0] [] seeds owed [(0,2)];
--      payOwed 0 [(0,2)] = just [(0,1)];
--      applyBatch [value 1] [0,0] [(0,1)] [] = [0,0], [(0,1)], [1]
--      paidOff [(0,1)] = false  →  batch STAYS OPEN.
-- em3: second delivery from source 0 at instant 1 (same instant).
--      hasOwed 0 [(0,1)] = true; payOwed 0 [(0,1)] = just [(0,0)];
--      applyBatch [value 2] [0,0] [(0,0)] [1] = [0,0], [(0,0)], [1,2]
--      paidOff [(0,0)] = true   →  batch PAID OFF, closeBatch fires.

em1 : InstEmit ℕ
em1 = (init 0 ∷ init 0 ∷ []) at 0 from 0 as subscribe

em2 : InstEmit ℕ
em2 = (value 1 ∷ []) at 1 from 0 as delivery

em3 : InstEmit ℕ
em3 = (value 2 ∷ []) at 1 from 0 as delivery

----------------------------------------------------------------------
-- § 2  REFUTATION: batch-online AS WRITTEN is FALSE
----------------------------------------------------------------------

-- LHS: impl-batchSimultaneous [em1, em2]
-- The final flushBatch flushes the still-open batch, producing a
-- singleton-value batch with only [1].
lhs-check : impl-batchSimultaneous {A = ℕ} (em1 ∷ em2 ∷ [])
          ≡ ((value (1 ∷ []) ∷ []) at 1 from 0 as delivery) ∷ []
lhs-check = refl

-- RHS: impl-batchSimultaneous [em1, em2, em3]
-- em3 pays off the owed; closeBatch fires mid-stream with [1, 2].
rhs-check : impl-batchSimultaneous {A = ℕ} (em1 ∷ em2 ∷ em3 ∷ [])
          ≡ ((value (1 ∷ 2 ∷ []) ∷ []) at 1 from 0 as delivery) ∷ []
rhs-check = refl

-- Discriminator: length of the values list in the first batch emit.
first-batch-val-len : List (InstEmit (List ℕ)) → ℕ
first-batch-val-len (((value vs ∷ _) at _ from _ as _) ∷ _) = length vs
first-batch-val-len _                                         = 0

-- lhs has length 1, rhs has length 2 — by computation:
lhs-len : first-batch-val-len (impl-batchSimultaneous {ℕ} (em1 ∷ em2 ∷ [])) ≡ 1
lhs-len = refl

rhs-len : first-batch-val-len (impl-batchSimultaneous {ℕ} (em1 ∷ em2 ∷ em3 ∷ [])) ≡ 2
rhs-len = refl

-- FORMAL REFUTATION.
-- If batch-online held, the first elements of lhs and rhs would be _≡_,
-- so first-batch-val-len of them would be equal — but 1 ≢ 2.
batch-online-refuted :
  ¬ (∀ {A : Set} (xs ys : List (InstEmit A)) →
     Pref.Prefix _≡_ (impl-batchSimultaneous xs)
                     (impl-batchSimultaneous (xs ++ ys)))
batch-online-refuted hyp
  with hyp {ℕ} (em1 ∷ em2 ∷ []) (em3 ∷ [])
... | Pref._∷_ h _ with cong (λ em → first-batch-val-len (em ∷ [])) h
... | ()

----------------------------------------------------------------------
-- § 3  CORRECTED STATEMENT: foldBatch-no-flush prefix
----------------------------------------------------------------------
-- Replace impl-batchSimultaneous (which flushes the open tail) with
-- foldBatch-no-flush (same fold but no terminal flushBatch).
-- Batches emitted by foldBatch-no-flush are closed by paidOff mid-
-- stream and are final; they can never be modified by further input.

foldBatch-no-flush : ∀ {A : Set} → BatchSt A → List (InstEmit A)
                   → List (InstEmit (List A))
foldBatch-no-flush st []       = []                    -- no flush at end
foldBatch-no-flush st (x ∷ xs) =
  let (out , st′) = step-batch x st
  in out ++ foldBatch-no-flush st′ xs

-- Check: [em1, em2] emits nothing from foldBatch-no-flush
-- (em2 does not pay off the owed, so no closeBatch fires)
no-flush-empty : foldBatch-no-flush {A = ℕ} batch-init (em1 ∷ em2 ∷ []) ≡ []
no-flush-empty = refl

-- Check: [em1, em2, em3] emits one finalized batch
-- (em3 pays off the owed, closeBatch fires inside step-batch)
no-flush-paid : foldBatch-no-flush {A = ℕ} batch-init (em1 ∷ em2 ∷ em3 ∷ [])
             ≡ ((value (1 ∷ 2 ∷ []) ∷ []) at 1 from 0 as delivery) ∷ []
no-flush-paid = refl

-- The corrected statement prefix check (LHS side):
-- foldBatch-no-flush [em1, em2] = [] is trivially a Prefix of anything.
pref-empty : Pref.Prefix _≡_ (foldBatch-no-flush {A = ℕ} batch-init (em1 ∷ em2 ∷ []))
                              (impl-batchSimultaneous (em1 ∷ em2 ∷ em3 ∷ []))
pref-empty = Pref.[]

-- The corrected statement prefix check (full [em1,em2,em3] vs same ++ []):
-- foldBatch-no-flush [em1,em2,em3] = [b] = impl-batchSimultaneous [em1,em2,em3]
-- So Prefix [b] [b] = refl-head ∷ Prefix [] [].
pref-full : Pref.Prefix _≡_ (foldBatch-no-flush {A = ℕ} batch-init (em1 ∷ em2 ∷ em3 ∷ []))
                             (impl-batchSimultaneous (em1 ∷ em2 ∷ em3 ∷ []))
pref-full = Pref._∷_ refl Pref.[]

----------------------------------------------------------------------
-- § 4  THE CORRECTED STATEMENT (Agda text for src/)
----------------------------------------------------------------------
-- Do NOT land in src/. Reported to the design session.
--
--   foldBatch-no-flush : ∀ {A : Set} → BatchSt A → List (InstEmit A)
--                      → List (InstEmit (List A))
--   foldBatch-no-flush st []       = []
--   foldBatch-no-flush st (x ∷ xs) =
--     let (out , st′) = step-batch x st in out ++ foldBatch-no-flush st′ xs
--
--   batch-online-corrected :
--     ∀ {A : Set} (xs ys : List (InstEmit A)) →
--     Pref.Prefix _≡_ (foldBatch-no-flush batch-init xs)
--                     (impl-batchSimultaneous (xs ++ ys))
--
-- STATUS: not yet postulated; this module typechecks the statement's
-- shape and its behavior on the counterexample shapes.
