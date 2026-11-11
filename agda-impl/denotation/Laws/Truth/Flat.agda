{-# OPTIONS --guardedness #-}

-- EACH JOINER KEEPS THE TRUTH, over an outer and lanes each read against
-- the next.  A joiner's rows are truncated: a row shows only past
-- finitely many it waits on.  A cover of the rows shown before a clean
-- row covers every row before it only where hangs show (`Shows`): there
-- a row with infinitely many before it is past one the cover sees.  So
-- each joiner reads its outer and lanes as showing their hangs, as every
-- approximant does (`sk-approx`).
module denotation.Laws.Truth.Flat where

open import Data.Maybe using (just; nothing)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (Den; enter; module Op)
open import denotation.Laws.Worlds using (Ok; InvD)
open import denotation.Laws.Shows using (ShowsK)
open import denotation.Laws.Truth using (Rel)
open import denotation.Laws.Truth.Join using (merge-truth; switch-truth; exhaust-truth)

postulate
  bounded-truth : ∀ {A B H} n {f f′ : A → Den B} {s s′ : Den A}
                → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
                → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
                → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap (mergeᶠ (just n)) f s) (Op.flatMap (mergeᶠ (just n)) f′ s′)

flat-truth : ∀ {A B H} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
           → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
           → (∀ m q → Ok H q → ShowsK m (enter s q)) → (∀ m a q → Ok H q → ShowsK m (enter (f a) q))
           → Rel H s s′ → (∀ a → Rel H (f a) (f′ a)) → Rel H (Op.flatMap op f s) (Op.flatMap op f′ s′)
flat-truth {A} {B} {H} (mergeᶠ nothing)  {f} {f′} {s} {s′} = merge-truth   {A} {B} {H} {f} {f′} {s} {s′}
flat-truth {A} {B} {H} (mergeᶠ (just n)) {f} {f′} {s} {s′} = bounded-truth {A} {B} {H} n {f} {f′} {s} {s′}
flat-truth {A} {B} {H} switchᶠ           {f} {f′} {s} {s′} = switch-truth  {A} {B} {H} {f} {f′} {s} {s′}
flat-truth {A} {B} {H} exhaustᶠ          {f} {f′} {s} {s′} = exhaust-truth {A} {B} {H} {f} {f′} {s} {s′}
