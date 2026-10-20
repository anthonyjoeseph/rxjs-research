-- A flatMap whose outer has ended but not yet closed leaves less than its
-- leftover reads: the outer's rest, a source's burst still under way past
-- a body's `take(1)`, is in the leftover and not yet in the pool, so the
-- part's rest hushes where the leftover's skips.
module refute.MidClimb where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
import Tree as T
import denotation.Unfold as U
open import adequacy.Strong.Against using (module StrongAgainst)
open StrongAgainst ⊤ using (Leaves)

-- The flatMap's part: no outer, one lane idling, the pool idle.
part : U.Node [] ⊤
part = U.flatMapᶜ {A = ⊤} T.switchᶠ (λ _ _ → U.idleᶜ) nothing (U.idleᶜ ∷ []) [] U.idleᶜ

-- Its leftover: the ended outer's burst still to run, beside the lane's.
left : U.Node [] ⊤
left = U.unionᶜ (U.burstingᶜ [] (U.ofᶜ [] 0 (tt ∷ []))) (U.unionᶜ U.idleᶜ U.idleᶜ)

refuted : ¬ Leaves part left
refuted l with Leaves.pin l
... | ()
