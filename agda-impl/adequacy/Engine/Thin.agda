{-# OPTIONS --guardedness #-}

-- A RUN THINNED: some of its skips erased, and of what it leaves running
-- at each step, some pins unpinned in order.  A source fed the rest past
-- its leading skips is its run so thinned.
module adequacy.Engine.Thin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₂)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; out; skip; end; hush)
open import denotation.MonotonicList using (Agree; Agreeᵀ; stop; out⁼; skip⁼; end⁼; hush⁼; stopᵀ; pin⁼; idle⁼; agreeᵀ-refl;
  agree-refl; agree-trans)
open import denotation.Unfold using (NEnv)
open import adequacy.Engine.Erase using (Eraseᵀ; stopᵉ; pinᵉ; unpin; idleᵉ; Erase; outᵉ; skipᵉ; erased; endᵉ; hushᵉ; eraseᵀ-agree; nowᵉ)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ)
open Events∞

-- To `n` events: each kept alike, its tail unpinned of some pins, or a
-- skip erased.
data Thinⁿ {A : Set} : ℕ → Events A → Events A → Set where
  stopᵗ : ∀ {x y} → Thinⁿ zero x y
  outᵗ  : ∀ {k p a l r} → Eraseᵀ k (cut l) (cut r) → Thinⁿ k (force l) (force r) → Thinⁿ (suc k) (out p a l) (out p a r)
  skipᵗ : ∀ {k p l r} → Eraseᵀ k (cut l) (cut r) → Thinⁿ k (force l) (force r) → Thinⁿ (suc k) (skip p l) (skip p r)
  dropᵗ : ∀ {k p l e} → Thinⁿ k (force l) e → Thinⁿ (suc k) (skip p l) e
  endᵗ  : ∀ {k p} → Thinⁿ (suc k) (end p) (end p)
  hushᵗ : ∀ {k} → Thinⁿ (suc k) hush hush

--
-- REFUTED: 974e8585 a run thinned of its skips alone, its tails unread, by
--   an `out` whose tail pins a position no tick heads: a sorted
--   environment thinned so is not sorted (`adequacy.Engine.Trails.sorted-thin`).
Thin : ∀ {A} → Events A → Events A → Set
Thin e e′ = ∀ n → Thinⁿ n e e′

-- Each source's run thinned.
Thinᴱ : ∀ {Γ} → NEnv Γ → NEnv Γ → Set
Thinᴱ []ᴬ       []ᴬ        = ⊤
Thinᴱ (e ∷ᴬ ρ) (e′ ∷ᴬ ρ′) = Thin e e′ × Thinᴱ ρ ρ′

thinⁿ-refl : ∀ {A} n (e : Events A) → Thinⁿ n e e
thinⁿ-refl zero    e           = stopᵗ
thinⁿ-refl (suc n) (out p a r) = outᵗ (eraseᵀ-agree (agreeᵀ-refl n (cut r))) (thinⁿ-refl n (force r))
thinⁿ-refl (suc n) (skip p r)  = skipᵗ (eraseᵀ-agree (agreeᵀ-refl n (cut r))) (thinⁿ-refl n (force r))
thinⁿ-refl (suc n) (end p)     = endᵗ
thinⁿ-refl (suc n) hush        = hushᵗ

thinᴱ-refl : ∀ {Γ} (ρ : NEnv Γ) → Thinᴱ ρ ρ
thinᴱ-refl []ᴬ      = tt
thinᴱ-refl (e ∷ᴬ ρ) = (λ n → thinⁿ-refl n e) , thinᴱ-refl ρ

-- Alike, then unpinned.
agreeᵀ-then : ∀ {k} {x y z : Tail} → Agreeᵀ k x y → Eraseᵀ k y z → Eraseᵀ k x z
agreeᵀ-then stopᵀ    stopᵉ       = stopᵉ
agreeᵀ-then (pin⁼ a) (pinᵉ e)    = pinᵉ (agreeᵀ-then a e)
agreeᵀ-then (pin⁼ a) (unpin t e) = unpin t (agreeᵀ-then a e)
agreeᵀ-then idle⁼    idleᵉ       = idleᵉ

-- Alike, then thinned.
agree-thin : ∀ {A k} {x y z : Events A} → Agree k x y → Thinⁿ k y z → Thinⁿ k x z
agree-thin stop          stopᵗ       = stopᵗ
agree-thin (out⁼ t a)    (outᵗ u e)  = outᵗ (agreeᵀ-then t u) (agree-thin a e)
agree-thin (skip⁼ t a)   (skipᵗ u e) = skipᵗ (agreeᵀ-then t u) (agree-thin a e)
agree-thin (skip⁼ t a)   (dropᵗ e)   = dropᵗ (agree-thin a e)
agree-thin end⁼          endᵗ        = endᵗ
agree-thin hush⁼         hushᵗ       = hushᵗ

-- Erased, thinned.
erase-thin : ∀ {A k} {x y : Events A} {t} → Erase k x t y → Thinⁿ k x y
erase-thin stopᵉ          = stopᵗ
erase-thin (outᵉ u e)     = outᵗ u (erase-thin e)
erase-thin (skipᵉ u e)    = skipᵗ u (erase-thin e)
erase-thin (erased _ _ e) = dropᵗ (erase-thin e)
erase-thin endᵉ           = endᵗ
erase-thin hushᵉ          = hushᵗ

-- Past leading skips, with its tail, is thinned.
drops-thin : ∀ {A P} {e : Events A} {h h′ : Events∞ A} → (∀ n → Agree n e (force h)) → Dropsˢ P h h′ → Thin e (force h′)
drops-thin y (dropˢ _ a r)  zero    = stopᵗ
drops-thin y (dropˢ _ a r)  (suc n) = agree-thin (agree-trans (y (suc n)) (a (suc n))) (dropᵗ (erase-thin (nowᵉ (proj₂ (proj₂ r) n))))
drops-thin y (dropsˢ _ a d) zero    = stopᵗ
drops-thin y (dropsˢ _ a d) (suc n) = agree-thin (agree-trans (y (suc n)) (a (suc n))) (dropᵗ (drops-thin (λ m → agree-refl m _) d n))
