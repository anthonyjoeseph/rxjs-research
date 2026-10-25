{-# OPTIONS --guardedness #-}

-- A source `skip [1], skip [2], end [9]` whose tail at its end is pinned
-- at `[0]`, erased of its `skip [2]`, beside a hushed body: the
-- connect's tail is `[1, 2, 0]` on the left and `[1, 0]` on the right,
-- which no erasure relates.
module adequacy.Refute-Body where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import denotation.MonotonicList.Events using (Events∞; Tail; Tail∞; Pos; ix; skip; end; hush; idle; pin)
open import denotation.MonotonicList using (agreeᵀ-refl)
open import adequacy.Engine.Meaning using (bodyConn)
open import adequacy.Engine.Erase using (_⊒_; Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; stopᵉ; idleᵉ; pinᵉ; unpin; skipᵉ; erased; endᵉ; skipᴸ; eraseᵀ-agree)
open Events∞
open Tail∞
open Eraseˢ

zero-pin : Tail
zero-pin = pin (ix 0 ∷ []) λ where .later → idle

ended : Events∞ ℕ
ended .force = end (ix 9 ∷ [])
ended .cut   = zero-pin

two : Events∞ ℕ
two .force = skip (ix 2 ∷ []) ended
two .cut   = zero-pin

left : Events∞ ℕ
left .force = skip (ix 1 ∷ []) two
left .cut   = idle

right : Events∞ ℕ
right .force = skip (ix 1 ∷ []) ended
right .cut   = idle

hushed : Events∞ ℕ
hushed .force = hush
hushed .cut   = idle

same : ∀ n → Eraseᵀ n zero-pin zero-pin
same n = eraseᵀ-agree (agreeᵀ-refl n zero-pin)

idle-erase : ∀ n → Eraseᵀ n idle idle
idle-erase zero    = stopᵉ
idle-erase (suc n) = idleᵉ

end-erase : ∀ n → Erase n (end (ix 9 ∷ [])) zero-pin (end {A = ℕ} (ix 9 ∷ []))
end-erase zero    = stopᵉ
end-erase (suc n) = endᵉ

erase : ∀ n → Eraseˢ n left right
erase zero          = stopᵉ ,ᵉ stopᵉ
erase (suc zero)    = idleᵉ ,ᵉ skipᵉ stopᵉ stopᵉ
erase (suc (suc n)) = idleᵉ ,ᵉ skipᵉ (same (suc n)) (erased refl (same n) (end-erase n))

erasure : left ⊒ right
erasure = skipᴸ , (λ ()) , erase

hush-refl : hushed ⊒ hushed
hush-refl = hushᴸ′ , (λ _ d → agreeᵀ-refl d idle) , λ n → idle-erase n ,ᵉ hush-erase n
  where
    open import adequacy.Engine.Erase using (hushᴸ; hushᵉ)
    hushᴸ′ = hushᴸ
    hush-erase : ∀ n → Erase n hush idle (hush {A = ℕ})
    hush-erase zero    = stopᵉ
    hush-erase (suc n) = hushᵉ

body-refuted : (∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′) → ⊥
body-refuted f with cutᵉ (proj₂ (proj₂ (f [] erasure hush-refl)) 3)
... | pinᵉ (unpin () _)
... | unpin _ (unpin () _)
