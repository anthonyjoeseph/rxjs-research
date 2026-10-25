{-# OPTIONS --guardedness #-}

-- An outer run out of order, `skip [5]` before `skip [1]`, erased of its
-- `skip [5]`: a lane heading at `[3]` is shown before the outer's
-- `skip [1]` on the left, after it on the right.
module adequacy.Refute-Erase where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Tree using (FlatOp; mergeᶠ)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; ix; skip; hush; idle)
open import denotation.Unfold using (Node; NEnv; ofᶜ)
open import adequacy.Engine.Meaning using (outerFrame)
open import adequacy.Engine.Drop using (_⊒_; Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; stopᵉ; idleᵉ; skipᵉ; erased; hushᵉ; skipᴸ)
open Events∞
open Eraseˢ

sk : Pos → Events∞ ℕ → Events∞ ℕ
sk p r .force = skip p r
sk p r .cut   = idle

hushed : Events∞ ℕ
hushed .force = hush
hushed .cut   = idle

h h′ : Events∞ ℕ
h  = sk (ix 0 ∷ []) (sk (ix 5 ∷ []) (sk (ix 1 ∷ []) hushed))
h′ = sk (ix 0 ∷ []) (sk (ix 1 ∷ []) hushed)

idle-erase : ∀ n → Eraseᵀ n idle idle
idle-erase zero    = stopᵉ
idle-erase (suc n) = idleᵉ

hush-erase : ∀ n → Erase n hush idle (hush {A = ℕ})
hush-erase zero    = stopᵉ
hush-erase (suc n) = hushᵉ

rest : ∀ n → Erase n (skip (ix 1 ∷ []) hushed) idle (skip (ix 1 ∷ []) hushed)
rest zero    = stopᵉ
rest (suc n) = skipᵉ (idle-erase n) (hush-erase n)

erase : ∀ n → Eraseˢ n h h′
erase zero          = stopᵉ ,ᵉ stopᵉ
erase (suc zero)    = idleᵉ ,ᵉ skipᵉ stopᵉ stopᵉ
erase (suc (suc n)) = idleᵉ ,ᵉ skipᵉ idleᵉ (erased (idle-erase n) (rest n))

erasure : h ⊒ h′
erasure = skipᴸ , (λ ()) , erase

g : ℕ → Pos → Node [] ℕ
g _ _ = ofᶜ [] 0 []

lane3 : List (Node [] ℕ)
lane3 = ofᶜ [] 3 (0 ∷ []) ∷ []

outer-refuted : (∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
                 → h ⊒ h′ → outerFrame op g false q ls ds ρ h ⊒ outerFrame op g false q ls ds ρ h′) → ⊥
outer-refuted f with nowᵉ (proj₂ (proj₂ (f (mergeᶠ nothing) g [] lane3 [] []ᴬ erasure)) 2)
... | skipᵉ _ ()
... | erased _ ()
