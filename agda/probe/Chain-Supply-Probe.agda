------------------------------------------------------------------
-- WHAT THE OPERATOR COUNT HAS TO BE GIVEN, and whether the clique
-- already holds it.
--
-- Chain-Index-Probe settled that a chain member reports at
-- `opIterD S W dep bud m j` with m the operators it has LEFT.  Reading
-- the gate's operator step off .Caps-Chain, its CONCLUSION is at
-- `suc m`:
--
--     op-step : … → j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m) j
--
-- so an operator clause can only report if its own index IS a
-- successor.  Step C cannot assume that — a caller could pass 0 — so the
-- index arrives with a HYPOTHESIS.  Which one, and whether the clique can
-- supply it, was NOT part of the settled design; it is what the
-- already-proven gate forces, and it is settled here before any clause
-- is rewritten.
------------------------------------------------------------------
module Chain-Supply-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤n+m)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Evaluator using (sizeAt; widAt; opIterD; fIterD)
open import Verify-Budget-Sufficient.Caps using (Caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Chain using (op-step)

------------------------------------------------------------------
-- § 1.  THE HYPOTHESIS IS `suc (sizeᵉ b) ≤ m`, AND IT IS FREE AT ENTRY.
------------------------------------------------------------------

-- the frame's size cap IS the size transformer at that level, so a
-- hypothesis stated against `frameStep` is already one about `sizeAt`
-- and no conversion sits between them.  This is what makes the entry
-- supply cost nothing: every clique head already carries
-- `sizeᵉ b ≤ Caps.cSize (frameStep j c)`
frameStep-size : ∀ (c : Caps) (j : ℕ) →
  Caps.cSize (frameStep j c) ≡ sizeAt (Caps.cSize c) j
frameStep-size c j = refl

-- so a FRESH entry instantiates `m` at `suc (sizeAt S j)` — the same
-- index `entry-to-index` converts the priced entry sweep into — and
-- supplies the hypothesis with one `s≤s` on a fact in hand
entry-supplies-index : ∀ (c : Caps) (j sz : ℕ) →
  sz ≤ Caps.cSize (frameStep j c) →
  suc sz ≤ suc (sizeAt (Caps.cSize c) j)
entry-supplies-index c j sz h = s≤s h

------------------------------------------------------------------
-- § 2.  AND ONE CHAIN EDGE LEAVES ROOM FOR THE SPLIT.
--
-- Every chain constructor's size is `suc (head + source)` — the shape
-- .Caps-Nest's `chain-step` abstracts the head out of — so a member
-- holding the hypothesis has a POSITIVE index (the split is licensed)
-- and its source's hypothesis holds at the predecessor (the split is
-- sound).  Two one-line facts, and the `m = 0` clause is absurd.
------------------------------------------------------------------

-- the split is licensed: an operator's index cannot be zero
chain-index-pos : ∀ (hd src m : ℕ) → suc (suc (hd + src)) ≤ m → 1 ≤ m
chain-index-pos hd src (suc m′) h = s≤s z≤n

-- and it is sound: at the predecessor the SOURCE's hypothesis holds,
-- which is what `op-step` hands the source
chain-index-desc : ∀ (hd src m′ : ℕ) →
  suc (suc (hd + src)) ≤ suc m′ → suc src ≤ m′
chain-index-desc hd src m′ (s≤s h) = ≤-trans (s≤s (m≤n+m src hd)) h

-- the zero case really is impossible, so the split costs one absurd
-- clause and no arithmetic
zero-index-absurd : ∀ (sz : ℕ) → suc sz ≤ zero → ⊥
zero-index-absurd sz ()

------------------------------------------------------------------
-- § 3.  AND THE GATE APPLIES AT THE SPLIT, UNCHANGED.  This is the
-- shape an operator clause closes in once its index is a successor: the
-- source reported at `m′`, pushBurst reported at the level the source
-- left, and `op-step` concludes at `suc m′` — the clause's own index.
-- Spent verbatim, so nothing new is owed here
------------------------------------------------------------------

op-clause-shape : ∀ (S W d k m′ j j₁ j₂ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterD S W d k m′ (suc j) →
  (suc j + j₁) + j₂ ≤ fIterD S W d k (suc (widAt S W (suc j + j₁))) (suc j + j₁) →
  j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m′) j
op-clause-shape = op-step

------------------------------------------------------------------
-- § 4.  WHICH TRANSFORMER EACH HEAD REPORTS IN, and it is FORCED rather
-- than chosen.  Step C was scoped as "one conjunct, one index", which
-- reads as though every head reports in the same shape.  They do not,
-- and the assignment is not a design decision: the family's own clause
-- equations (Rx.Evaluator) close into a CYCLE, and each head sits at
-- exactly one arc of it.
--
--     fLvlD S W (suc d) J ≡ sIterD S W d (suc (sizeAt S (suc J)))
--                                        (suc (widAt S W J)) (fLvl S W J)
--     sIterD S W d k (suc m) J ≡ sIterD S W d k m (sLvlD S W d k (suc J))
--     sLvlD S W d (suc k) J    ≡ opIterD S W d k (suc (sizeAt S J)) J
--     opIterD S W d k (suc m) J ≡ fIterD S W d k (suc (widAt S W X)) X
--     fIterD S W d k (suc m) J ≡ fIterD S W d k m (fLvlD S W d J)
--
--   A FRAME's payload walk runs at the REFRESHED budget
--   `suc (sizeAt S (suc J))` — which is `frameBud c j` on the nose, and
--   the one arc that spends a unit of DEPTH FUEL.  A WALK subscribes each
--   payload at `suc J`.  A FRESH SUBSCRIBE on budget `suc k` opens an
--   operator sweep at k, indexed by the size cap.  An OPERATOR pushes
--   frames.  And a frame pushes one `fLvlD` per emit, closing the ring.
--
--   So, per head:
--
--     subscribeE-caps        opIterD S W dep bud m j      m = operators LEFT
--     subscribeAll-caps      opIterD S W dep bud m j      (it IS an operator)
--     subscribeInner-caps    sLvlD  S W dep bud (suc j)   a payload's own entry
--     thruWalk-caps          sIterD S W dep bud (length vals) j
--     concatDrain-caps       sIterD S W dep bud (length q) j
--     stepFrame-caps         fLvlD  S W dep j             one frame, no index
--     pushBurst-caps         fIterD S W dep bud (length ems) j
--
--   The three frame-internal heads (thruConsume / innerFinish /
--   innerReact) report in their caller's shape, since they are the
--   inside of one `stepFrame`; the three share heads (sharedSlot /
--   sharedConnect / subscribeE-input) report as FRESH ENTRIES, because a
--   stored def is unrelated to the caller's term; and retagEvents-caps
--   subscribes nothing, so it gains no conjunct at all.
--
--   ONLY the two `opIterD` rows need an index PARAMETER.  Every other
--   index is a function of arguments the head already has — a payload
--   list's length, a queue's length, an emit list's length — so the
--   conjunct reads it off directly and no plumbing is added.  That is
--   why § 1's hypothesis is needed at two heads rather than fourteen.
------------------------------------------------------------------
