{-# OPTIONS --guardedness #-}

-- EACH JOINER KEEPS THE INVARIANT: merge, switch and exhaust by the
-- joiner view (`Laws.JoinInv`), a bounded merge by its own
-- (`Laws.BoundedInv`).
module denotation.Laws.FlatInv where

open import Data.Maybe using (just; nothing)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (Den; module Op)
open import denotation.Laws.Worlds using (InvD)
open import denotation.Laws.JoinInv using (module MergeI; module SwitchI; module ExhaustI)
open import denotation.Laws.BoundedInv using (module BoundedI)

flatMap-inv : ∀ {A B H} (op : FlatOp) {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (Op.flatMap op f s)
flatMap-inv (mergeᶠ nothing)  {f} is fi p ok = MergeI.inv ok f fi (is p ok)
flatMap-inv (mergeᶠ (just n)) {f} is fi p ok = BoundedI.inv ok n f fi (is p ok)
flatMap-inv switchᶠ           {f} is fi p ok = SwitchI.inv ok f fi (is p ok)
flatMap-inv exhaustᶠ          {f} is fi p ok = ExhaustI.inv ok f fi (is p ok)
