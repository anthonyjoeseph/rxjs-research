{-# OPTIONS --guardedness #-}

-- `M.beside` does not respect `≃` in its body, even with every matched
-- skip in place: an unmatched skip above the value after it holds a
-- source spinning between the two in front of that value.
module adequacy.BesideAbove where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)

open import denotation.MonotonicList using (Events; Events∞; out; skip; hush; ix)
import denotation.MonotonicList as M
open import adequacy.Content using (_≃_; _≃∞_; out≃; hush≃; skipˡ; ≃-sym; module Honesty)
open Honesty ⊤ using (Has; has-skips; atOut; pastOut; pastSkip)

open Events∞
open _≃∞_

zeno : ℕ → Events ⊤
zeno n = skip (ix 3 ∷ ix n ∷ []) λ where .force → zeno (suc n)

value : Events ⊤
value = out (ix 2 ∷ []) tt λ where .force → hush

above : Events ⊤
above = skip (ix 9 ∷ []) λ where .force → value

alike : above ≃ value
alike = skipˡ (out≃ λ where .≃force → hush≃)

shows : Has (M.beside value (zeno 0)) (ix 2 ∷ []) (just tt)
shows = atOut

spins : ∀ n {k b} → Has (M.beside above (zeno n)) k b → ⊥
spins n (pastSkip h) = spins (suc n) h

refuted : ((x y : Events ⊤) → x ≃ y → M.beside x (zeno 0) ≃ M.beside y (zeno 0)) → ⊥
refuted cong = spins 0 (has-skips (≃-sym (cong _ _ alike)) shows)
