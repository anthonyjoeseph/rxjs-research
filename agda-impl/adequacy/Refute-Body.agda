{-# OPTIONS --guardedness #-}

-- Each premise of `body-⊒` is needed: a connect whose source erases a
-- skip runs with skips erased only if the source's next is no earlier
-- than where it subscribes, its run in order, and its tail trailing it.
module adequacy.Refute-Body where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import denotation.MonotonicList.Events using (Events∞; Tail; Tail∞; Pos; ix; skip; end; hush; idle; pin)
open import denotation.MonotonicList using (agreeᵀ-refl)
open import adequacy.Engine.Meaning using (bodyConn)
open import adequacy.Engine.Erase using (_⊒_; Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; stopᵉ; idleᵉ; pinᵉ; unpin; skipᵉ; erased; endᵉ; hushᵉ; skipᴸ; endᴸ; hushᴸ; eraseᵀ-agree)
open import adequacy.Placed.Order using (Atop; Ordered; ordered)
open import adequacy.Placed.Trail using (Trail; Trailing; trail-idle)
open Events∞
open Tail∞
open Eraseˢ

idle-erase : ∀ n → Eraseᵀ n idle idle
idle-erase zero    = stopᵉ
idle-erase (suc n) = idleᵉ

nine : Pos
nine = ix 9 ∷ []

end-erase : ∀ {t} n → Erase n (end nine) t (end {A = ℕ} nine)
end-erase zero    = stopᵉ
end-erase (suc n) = endᵉ

hushed : Events∞ ℕ
hushed .force = hush
hushed .cut   = idle

hush-refl : hushed ⊒ hushed
hush-refl = hushᴸ , (λ _ d → agreeᵀ-refl d idle) , λ n → idle-erase n ,ᵉ hush-erase n
  where
    hush-erase : ∀ n → Erase n hush idle (hush {A = ℕ})
    hush-erase zero    = stopᵉ
    hush-erase (suc n) = hushᵉ

fin : Events∞ ℕ
fin .force = end nine
fin .cut   = idle

fin-trail : Trailing fin
fin-trail = trail-idle _ tt

------------------------------------------------------------------------
-- No trail: a source `skip [1], skip [2], end [9]` whose tail is pinned
-- at `[0]`, erased of its `skip [2]`, beside a hushed body: the
-- connect's tail is `[1, 2, 0]` on the left and `[1, 0]` on the right.

zero-pin : Tail
zero-pin = pin (ix 0 ∷ []) λ where .later → idle

ended : Events∞ ℕ
ended .force = end nine
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

same : ∀ n → Eraseᵀ n zero-pin zero-pin
same n = eraseᵀ-agree (agreeᵀ-refl n zero-pin)

erase : ∀ n → Eraseˢ n left right
erase zero          = stopᵉ ,ᵉ stopᵉ
erase (suc zero)    = idleᵉ ,ᵉ skipᵉ stopᵉ stopᵉ
erase (suc (suc n)) = idleᵉ ,ᵉ skipᵉ (same (suc n)) (erased refl (same n) (end-erase n))

ordered-left : Ordered (force left)
ordered (ordered-left) = refl , record { ordered = refl , record { ordered = tt } }

untrailed : (∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Atop r (force σ) → Ordered (force σ)
          → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′) → ⊥
untrailed f with cutᵉ (proj₂ (proj₂ (f [] refl ordered-left (skipᴸ , (λ ()) , erase) hush-refl)) 3)
... | pinᵉ (unpin () _)
... | unpin _ (unpin () _)

------------------------------------------------------------------------
-- No order: a source `skip [2,0], skip [1], skip [2,1], end [9]` at
-- `[2]`, erased of its `skip [1]`: the burst stops at `[1]` on the left
-- and runs to `[2,1]` on the right.

un-b : Events∞ ℕ
un-b .force = skip (ix 2 ∷ ix 1 ∷ []) fin
un-b .cut   = idle

un-a : Events∞ ℕ
un-a .force = skip (ix 1 ∷ []) un-b
un-a .cut   = idle

un-left : Events∞ ℕ
un-left .force = skip (ix 2 ∷ ix 0 ∷ []) un-a
un-left .cut   = idle

un-right : Events∞ ℕ
un-right .force = skip (ix 2 ∷ ix 0 ∷ []) un-b
un-right .cut   = idle

un-erase : ∀ n → Eraseˢ n un-left un-right
un-erase zero    = stopᵉ ,ᵉ stopᵉ
un-erase (suc n) = idleᵉ ,ᵉ skipᵉ (idle-erase n) (ea n)
  where
    eb : ∀ n → Erase n (force un-b) idle (force un-b)
    eb zero    = stopᵉ
    eb (suc n) = skipᵉ (idle-erase n) (end-erase n)
    ea : ∀ n → Erase n (force un-a) idle (force un-b)
    ea zero    = stopᵉ
    ea (suc n) = erased refl (idle-erase n) (eb n)

un-trail : Trailing un-left
un-trail = trail-idle _ (trail-idle _ (trail-idle _ fin-trail))

unordered : (∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Atop r (force σ) → Trailing σ
          → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′) → ⊥
unordered f with cutᵉ (proj₂ (proj₂ (f (ix 2 ∷ []) refl un-trail (skipᴸ , (λ ()) , un-erase) hush-refl)) 3)
... | pinᵉ ()
... | unpin _ ()

------------------------------------------------------------------------
-- Not atop: a source `skip [0], skip [1], skip [2,0], end [9]` at `[2]`,
-- erased of its `skip [1]`, beside a body `end [9]`: past the source's
-- `[0]`, the burst stops at `[1]` on the left and pins `[2,0]` on the
-- right.

lo-b : Events∞ ℕ
lo-b .force = skip (ix 2 ∷ ix 0 ∷ []) fin
lo-b .cut   = idle

lo-a : Events∞ ℕ
lo-a .force = skip (ix 1 ∷ []) lo-b
lo-a .cut   = idle

lo-left : Events∞ ℕ
lo-left .force = skip (ix 0 ∷ []) lo-a
lo-left .cut   = idle

lo-right : Events∞ ℕ
lo-right .force = skip (ix 0 ∷ []) lo-b
lo-right .cut   = idle

lo-erase : ∀ n → Eraseˢ n lo-left lo-right
lo-erase zero    = stopᵉ ,ᵉ stopᵉ
lo-erase (suc n) = idleᵉ ,ᵉ skipᵉ (idle-erase n) (ea n)
  where
    eb : ∀ n → Erase n (force lo-b) idle (force lo-b)
    eb zero    = stopᵉ
    eb (suc n) = skipᵉ (idle-erase n) (end-erase n)
    ea : ∀ n → Erase n (force lo-a) idle (force lo-b)
    ea zero    = stopᵉ
    ea (suc n) = erased refl (idle-erase n) (eb n)

lo-ordered : Ordered (force lo-left)
ordered lo-ordered = refl , record { ordered = refl , record { ordered = refl , record { ordered = tt } } }

lo-trail : Trailing lo-left
lo-trail = trail-idle _ (trail-idle _ (trail-idle _ fin-trail))

fin-refl : fin ⊒ fin
fin-refl = endᴸ , (λ ()) , λ n → idle-erase n ,ᵉ end-erase n

unplaced : (∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Ordered (force σ) → Trailing σ
         → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′) → ⊥
unplaced f with nowᵉ (proj₂ (proj₂ (f (ix 2 ∷ []) lo-ordered lo-trail (skipᴸ , (λ ()) , lo-erase) fin-refl)) 3)
... | skipᵉ () _
... | erased _ _ (erased () _ _)
