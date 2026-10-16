{-# OPTIONS --guardedness #-}

-- Witness: a takeWhile over a run merely in order, steady and trailing,
-- a pin left running at the failing value's own position.
module adequacy.Refute-Take where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList using (Events; Events∞; Pos; ix; out; hush; Tail; Tail∞; pin; idle)
import denotation.MonotonicList as M
open import adequacy.Placed using (Ordered; Steady; Trail; trail; trailᶠ; everyᵀ; sortedᵀ; flatᵀ; everyT-idle; flatT-idle)

open Events∞
open Tail∞

h : Pos
h = ix 0 ∷ []

-- The value at `h`, then silence; `h` itself left running beside it.
run : Events ℕ
run = out h 0 λ where
  .force → hush
  .cut   → idle

left : Tail
left = pin h λ where .later → idle

run-ordered : Ordered run
run-ordered = record { ordered = tt , record { ordered = tt } }

run-steady : Steady run
run-steady = record { steady = tt , record { steady = tt } }

run-trail : Trail run left
run-trail = record
  { trail  = record { sortedᵀ = tt , record { sortedᵀ = tt } }
           , record { everyᵀ = refl , everyT-idle }
           , record { trail = record { sortedᵀ = tt } , everyT-idle , tt ; trailᶠ = flatT-idle }
  ; trailᶠ = record { flatᵀ = everyT-idle , flatT-idle } }

-- The value fails: its completion under `last`, past the pin it left at `h`.
take-refuted : (∀ {A} i (q : A → Bool) (x : Events A) c → Ordered x → Steady x → Trail x c → Trail (M.takeWhileᴱ i q x) c) → ⊥
take-refuted t with proj₁ (everyᵀ (proj₁ (proj₂ (trail (t false (λ _ → false) run left run-ordered run-steady run-trail)))))
... | () , _
