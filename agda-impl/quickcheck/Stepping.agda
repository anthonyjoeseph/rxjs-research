{-# OPTIONS --guardedness #-}

-- THE STEPPER, EXACT, TESTED: `denotation.Unfold`'s stepper shows what
-- its configuration means, event for event, skips and positions included,
-- so the relation between them is equality and not a bisimulation up to
-- silent steps.
module quickcheck.Stepping where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; _<ᵖ_; root)
open import denotation.Unfold using (subscribe; unfold; meaning)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  exactᵇ : ℕ → Events ℕ → Events ℕ → Bool
  exactᵇ zero    _           _            = true
  exactᵇ (suc k) (out p a r) (out q b r′) = samePos p q ∧ (a ≡ᵇ b) ∧ exactᵇ k (Events∞.force r) (Events∞.force r′)
  exactᵇ (suc k) (skip p r)  (skip q r′)  = samePos p q ∧ exactᵇ k (Events∞.force r) (Events∞.force r′)
  exactᵇ (suc k) (end p)     (end q)      = samePos p q
  exactᵇ (suc k) hush        hush         = true
  exactᵇ (suc k) _           _            = false

-- The stepper's run against the meaning of the configuration it starts from.
stepping : Prog natᵗ → Bool
stepping p = exactᵇ 4000 (unfold n) (meaning n []ᴬ)
  where n = subscribe (toObs timeline 3 p []ᴬ []ᴬ []ᴬ) root

-- The seeds from f on which they part.
steppingFails : ℕ → ℕ → List ℕ
steppingFails f c = filterᵇ (λ s → not (stepping (program s))) (mapL (f +_) (upTo c))
