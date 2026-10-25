{-# OPTIONS --guardedness #-}

-- WHAT A RUN SHOWS, IT SHOWS ERASED: every position a run with skips
-- erased shows, or leaves running, the run shows or leaves running too,
-- and what it leaves running after each step is as fresh.  Read a depth
-- at a time (`Upto`), each depth off one derivation of `Erase`, and in
-- the limit off them all, since `_⊒_` holds at each depth on its own.
-- Past dropped skips, alike (`every-drops`), and the last skip dropped
-- witnesses where what is left running is fresh (`drops-fresh`).
module adequacy.Engine.Erased where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import denotation.MonotonicList.Events using (Events; Events∞; Tail; Tail∞; Pos; out; skip; end; hush; pin; idle)
open import denotation.MonotonicList using (Agree)
open import adequacy.Engine.Erase using (Eraseᵀ; Erase; cutᵉ; nowᵉ; _⊒_; stopᵉ; pinᵉ; unpin; idleᵉ; outᵉ; skipᵉ; erased; endᵉ; hushᵉ; erase-agree)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ)
open import adequacy.Placed.Order using (Every; EveryT; Every∞; every; everyᵀ)
open import adequacy.Placed.Keys using (every-≈)
open import adequacy.Placed.Burst using (Fresh; FreshRun; freshᴿ)
open Events∞
open Tail∞

------------------------------------------------------------------------
-- A depth at a time

UptoT : ℕ → (Pos → Set) → Tail → Set
UptoT zero    P t         = ⊤
UptoT (suc n) P (pin k u) = P k × UptoT n P (later u)
UptoT (suc n) P idle      = ⊤

Upto : ∀ {A} → ℕ → (Pos → Set) → Events A → Set
Upto zero    P e           = ⊤
Upto (suc n) P (out h _ r) = P h × Upto n P (force r) × UptoT n P (cut r)
Upto (suc n) P (skip h r)  = P h × Upto n P (force r) × UptoT n P (cut r)
Upto (suc n) P (end h)     = P h
Upto (suc n) P hush        = ⊤

FreshUpto : ∀ {A} → ℕ → Pos → Events A → Set
FreshUpto zero    p e           = ⊤
FreshUpto (suc n) p (out m _ s) = UptoT n (Fresh p m) (cut s) × FreshUpto n p (force s)
FreshUpto (suc n) p (skip m s)  = UptoT n (Fresh p m) (cut s) × FreshUpto n p (force s)
FreshUpto (suc n) p (end _)     = ⊤
FreshUpto (suc n) p hush        = ⊤

------------------------------------------------------------------------
-- Every depth, every step

everyT-upto : ∀ {P : Pos → Set} (t : Tail) → (∀ n → UptoT n P t) → EveryT P t
everyᵀ (everyT-upto (pin k u) f) = proj₁ (f 1) , everyT-upto (later u) (λ n → proj₂ (f (suc n)))
everyᵀ (everyT-upto idle      f) = tt

every-upto : ∀ {A} {P : Pos → Set} (e : Events A) → (∀ n → Upto n P e) → Every P e
every (every-upto (out h _ r) f) =
  proj₁ (f 1) , every-upto (force r) (λ n → proj₁ (proj₂ (f (suc n)))) , everyT-upto (cut r) (λ n → proj₂ (proj₂ (f (suc n))))
every (every-upto (skip h r)  f) =
  proj₁ (f 1) , every-upto (force r) (λ n → proj₁ (proj₂ (f (suc n)))) , everyT-upto (cut r) (λ n → proj₂ (proj₂ (f (suc n))))
every (every-upto (end h)     f) = f 1
every (every-upto hush        f) = tt

fresh-upto : ∀ {A} p (e : Events A) → (∀ n → FreshUpto n p e) → FreshRun p e
freshᴿ (fresh-upto p (out m _ s) f) = everyT-upto (cut s) (λ n → proj₁ (f (suc n))) , fresh-upto p (force s) (λ n → proj₂ (f (suc n)))
freshᴿ (fresh-upto p (skip m s)  f) = everyT-upto (cut s) (λ n → proj₁ (f (suc n))) , fresh-upto p (force s) (λ n → proj₂ (f (suc n)))
freshᴿ (fresh-upto p (end _)     f) = tt
freshᴿ (fresh-upto p hush        f) = tt

------------------------------------------------------------------------
-- Read off one derivation

uptoT-erase : ∀ {P : Pos → Set} {k} {x y : Tail} → EveryT P x → Eraseᵀ k x y → UptoT k P y
uptoT-erase px stopᵉ       = tt
uptoT-erase px (pinᵉ e)    = proj₁ (everyᵀ px) , uptoT-erase (proj₂ (everyᵀ px)) e
uptoT-erase px (unpin o e) = uptoT-erase (proj₂ (everyᵀ px)) e
uptoT-erase px idleᵉ       = tt

upto-erase : ∀ {A} {P : Pos → Set} {k} {x y : Events A} {t} → Every P x → Erase k x t y → Upto k P y
upto-erase px stopᵉ          = tt
upto-erase px (outᵉ e x)     = proj₁ (every px) , upto-erase (proj₁ (proj₂ (every px))) x , uptoT-erase (proj₂ (proj₂ (every px))) e
upto-erase px (skipᵉ e x)    = proj₁ (every px) , upto-erase (proj₁ (proj₂ (every px))) x , uptoT-erase (proj₂ (proj₂ (every px))) e
upto-erase px (erased o e x) = upto-erase (proj₁ (proj₂ (every px))) x
upto-erase px endᵉ           = every px
upto-erase px hushᵉ          = tt

freshUpto-erase : ∀ {A} {p k} {x y : Events A} {t} → FreshRun p x → Erase k x t y → FreshUpto k p y
freshUpto-erase fx stopᵉ          = tt
freshUpto-erase fx (outᵉ e x)     = uptoT-erase (proj₁ (freshᴿ fx)) e , freshUpto-erase (proj₂ (freshᴿ fx)) x
freshUpto-erase fx (skipᵉ e x)    = uptoT-erase (proj₁ (freshᴿ fx)) e , freshUpto-erase (proj₂ (freshᴿ fx)) x
freshUpto-erase fx (erased o e x) = freshUpto-erase (proj₂ (freshᴿ fx)) x
freshUpto-erase fx endᵉ           = tt
freshUpto-erase fx hushᵉ          = tt

------------------------------------------------------------------------
-- Erased, and alike

everyT-⊒ : ∀ {A} {P : Pos → Set} {h h′ : Events∞ A} → EveryT P (cut h) → h ⊒ h′ → EveryT P (cut h′)
everyT-⊒ {h′ = h′} pt (_ , _ , e) = everyT-upto (cut h′) (λ n → uptoT-erase pt (cutᵉ (e n)))

every-⊒ : ∀ {A} {P : Pos → Set} {h h′ : Events∞ A} → Every∞ P h → h ⊒ h′ → Every∞ P h′
every-⊒ {h′ = h′} (pe , pt) d@(_ , _ , e) = every-upto (force h′) (λ n → upto-erase pe (nowᵉ (e n))) , everyT-⊒ pt d

fresh-⊒ : ∀ {A} {p} {h h′ : Events∞ A} → FreshRun p (force h) → h ⊒ h′ → FreshRun p (force h′)
fresh-⊒ {p = p} {h′ = h′} fr (_ , _ , e) = fresh-upto p (force h′) (λ n → freshUpto-erase fr (nowᵉ (e n)))

fresh-≈ : ∀ {A} {p} {x y : Events A} → (∀ n → Agree n x y) → FreshRun p x → FreshRun p y
fresh-≈ {p = p} {y = y} ag fx = fresh-upto p y (λ n → freshUpto-erase fx (erase-agree {t = idle} (ag n)))

------------------------------------------------------------------------
-- Past dropped skips

every-drops : ∀ {A} {P Q : Pos → Set} {h h′ : Events∞ A} → Every∞ P h → Dropsˢ Q h h′ → Every∞ P h′
every-drops (pe , _) (dropˢ q ag d)  = every-⊒ (proj₂ (every (every-≈ _ _ ag pe))) d
every-drops (pe , _) (dropsˢ q ag d) = every-drops (proj₂ (every (every-≈ _ _ ag pe))) d

fresh-drops : ∀ {A} {p} {Q : Pos → Set} {h h′ : Events∞ A} → FreshRun p (force h) → Dropsˢ Q h h′ → FreshRun p (force h′)
fresh-drops fr (dropˢ q ag d)  = fresh-⊒ (proj₂ (freshᴿ (fresh-≈ ag fr))) d
fresh-drops fr (dropsˢ q ag d) = fresh-drops (proj₂ (freshᴿ (fresh-≈ ag fr))) d

-- The last skip dropped: one `Q` holds of, as each `P` the run's
-- positions keep, and what is left running is fresh against it.
drops-fresh : ∀ {A} {p} {P Q : Pos → Set} {h h′ : Events∞ A} → Dropsˢ Q h h′ → Every∞ P h → FreshRun p (force h)
            → Σ Pos (λ k → Q k × P k × EveryT (Fresh p k) (cut h′))
drops-fresh (dropˢ {k = k} q ag d) (pe , _) fr =
  k , q , proj₁ (every (every-≈ _ _ ag pe)) , everyT-⊒ (proj₁ (freshᴿ (fresh-≈ ag fr))) d
drops-fresh (dropsˢ q ag d) (pe , _) fr =
  drops-fresh d (proj₂ (every (every-≈ _ _ ag pe))) (proj₂ (freshᴿ (fresh-≈ ag fr)))
