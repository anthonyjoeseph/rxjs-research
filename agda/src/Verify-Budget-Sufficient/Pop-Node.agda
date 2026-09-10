------------------------------------------------------------------
-- WHAT A POP LEAVES ALONE, stated where it costs nothing to state.
--
-- The node counter is not touched by taking an arrival off the
-- queue: nothing subscribes while a pop is in progress, so the
-- counter the registry's order conjunct is keyed on is the same
-- counter on both sides.  It is a separate statement from the
-- source floor's because the two are separate fields with separate
-- consumers -- this one's is the registry's own ordering fold,
-- which reads the counter as a WATERMARK rather than as a bound,
-- so a transport is what it needs and not a weakening.
--
-- IT LIVES HERE AND NOT BESIDE ITS SIBLINGS, and that placement is
-- the point rather than an accident.  The obvious home is next to
-- the other pop transports, which sit in a module 72 of this
-- tree's 132 modules import: a four-line lemma there invalidates
-- 55% of the tree, and one of the modules it invalidates has
-- itself outgrown the dev loop, so the bill is a CI gate for a
-- statement whose proof is one `refl`.  Nothing about the lemma
-- wants that depth -- it needs the evaluator and nothing else --
-- so it takes a module of its own, where it checks in seconds and
-- invalidates only the face that spends it.  `make cone-check`
-- enforces the general rule.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Pop-Node where

open import Data.Product using (_,_)
open import Data.Sum     using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp       using (Ctx)
open import Rx.Evaluator using (Sched; Arrival; sched-next; schedGo)

pop-nextNode : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  Sched.nextNode sched′ ≡ Sched.nextNode sched
pop-nextNode sched eq with schedGo (Sched.live sched) | eq
... | inj₂ (a″ , ls) | refl = refl
