{-# OPTIONS --guardedness #-}

-- A tail out of order, `[5, 1]`, erased of its `5`, beside a pool pinned
-- at `[3]`: the merge's tail is `[3, 5, 1]` on the left and `[1, 3]` on
-- the right, which no erasure relates.
module adequacy.Refute-Unpin where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Bool using (false)
open import Tree using (mergeᶠ)
open import denotation.MonotonicList.Events using (Events∞; Tail; Tail∞; Pos; ix; skip; hush; idle; pin)
open import denotation.Unfold using (Node; NEnv; ofᶜ; burstingᶜ)
open import adequacy.Engine.Meaning using (outerFrame)
open import adequacy.Engine.Drop using (_⊒_; Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; stopᵉ; idleᵉ; pinᵉ; unpin; skipᵉ; hushᵉ; skipᴸ)
open Events∞
open Tail∞
open Eraseˢ

one : Tail
one = pin (ix 1 ∷ []) λ where .later → idle

five-one : Tail
five-one = pin (ix 5 ∷ []) λ where .later → one

hushed : Events∞ ℕ
hushed .force = hush
hushed .cut   = idle

run : Tail → Events∞ ℕ
run t .force = skip (ix 0 ∷ []) hushed
run t .cut   = t

idle-erase : ∀ n → Eraseᵀ n idle idle
idle-erase zero    = stopᵉ
idle-erase (suc n) = idleᵉ

hush-erase : ∀ n → Erase n hush idle (hush {A = ℕ})
hush-erase zero    = stopᵉ
hush-erase (suc n) = hushᵉ

erase : ∀ n → Eraseˢ n (run five-one) (run one)
erase zero          = stopᵉ ,ᵉ stopᵉ
erase (suc zero)    = unpin stopᵉ ,ᵉ skipᵉ stopᵉ stopᵉ
erase (suc (suc n)) = unpin (pinᵉ (idle-erase n)) ,ᵉ skipᵉ idleᵉ (hush-erase (suc n))

erasure : run five-one ⊒ run one
erasure = skipᴸ , (λ ()) , erase

g : ℕ → Pos → Node [] ℕ
g _ _ = ofᶜ [] 0 []

pool : List (Node [] ℕ)
pool = burstingᶜ [] (ofᶜ [] 3 (0 ∷ [])) ∷ []

outer-refuted : (∀ {Γ A B} op (g : A → Pos → Node Γ B) q ls ds (ρ : NEnv Γ) {h h′ : Events∞ A}
                 → h ⊒ h′ → outerFrame op g false q ls ds ρ h ⊒ outerFrame op g false q ls ds ρ h′) → ⊥
outer-refuted f with cutᵉ (proj₂ (proj₂ (f (mergeᶠ nothing) g [] [] pool []ᴬ erasure)) 4)
... | unpin (unpin (pinᵉ ()))
... | unpin (unpin (unpin ()))
