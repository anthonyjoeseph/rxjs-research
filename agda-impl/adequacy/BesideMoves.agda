{-# OPTIONS --guardedness #-}

-- `M.beside` does not respect `≃` in its source: a matched skip may move,
-- so a source spinning below the body's value is alike one that passes it.
module adequacy.BesideMoves where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

open import denotation.MonotonicList using (Events; Events∞; out; skip; hush; ix)
import denotation.MonotonicList as M
open import adequacy.Content using (_≃_; _≃∞_; skip≃; module Honesty)
open Honesty ⊤ using (Has; has-skips; atOut; pastOut; pastSkip)

open Events∞
open _≃∞_

zeno : ℕ → Events ⊤
zeno n = skip (ix 1 ∷ ix n ∷ []) λ where .force → zeno (suc n)

up : ℕ → Events ⊤
up n = skip (ix n ∷ []) λ where .force → up (suc n)

alike : ∀ m n → zeno m ≃ up n
alike m n = skip≃ λ where .≃force → alike (suc m) (suc n)

body : Events ⊤
body = out (ix 5 ∷ []) tt λ where .force → hush

passes : Has (M.beside body (up 0)) (ix 5 ∷ []) (just tt)
passes = pastSkip (pastSkip (pastSkip (pastSkip (pastSkip atOut))))

spins : ∀ n {k b} → Has (M.beside body (zeno n)) k b → ⊥
spins n (pastSkip h) = spins (suc n) h

refuted : ((x y : Events ⊤) → x ≃ y → M.beside body x ≃ M.beside body y) → ⊥
refuted cong = spins 0 (has-skips (Content-sym (cong _ _ (alike 0 0))) passes)
  where open import adequacy.Content using () renaming (≃-sym to Content-sym)
