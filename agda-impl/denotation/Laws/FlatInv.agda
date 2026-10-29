{-# OPTIONS --guardedness #-}

-- EACH JOINER KEEPS THE INVARIANT: merge, switch and exhaust by the
-- joiner view (`Laws.JoinInv`), a bounded merge by its own.
module denotation.Laws.FlatInv where

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (Den; module Op)
open import denotation.Laws.Worlds using (InvD)
open import denotation.Laws.JoinInv using (module MergeI; module SwitchI; module ExhaustI)

postulate
  -- A BOUNDED MERGE KEEPS THE INVARIANT.  A queued lane is subscribed under
  -- the end of the lane it follows, in that lane's world, so its world is
  -- nested in the earlier lane's rather than apart from it.
  bounded-inv : ∀ {A B H} (n : ℕ) {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (Op.flatMap (mergeᶠ (just n)) f s)

flatMap-inv : ∀ {A B H} (op : FlatOp) {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (Op.flatMap op f s)
flatMap-inv (mergeᶠ nothing)  {f} is fi p ok = MergeI.inv ok f fi (is p ok)
flatMap-inv (mergeᶠ (just n)) {f} {s} is fi = bounded-inv n {f} {s} is fi
flatMap-inv switchᶠ           {f} is fi p ok = SwitchI.inv ok f fi (is p ok)
flatMap-inv exhaustᶠ          {f} is fi p ok = ExhaustI.inv ok f fi (is p ok)
