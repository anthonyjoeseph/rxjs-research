{-# OPTIONS --guardedness #-}

-- A LAWFUL HOT KEEPS THE INVARIANT among its own rows.  A subscription at
-- `p` sees the hot's rows past `p` named by `sub p`, or, the hot having
-- ended by `p`, a lone end below it; never both, since a lawful hot has
-- nothing past its end.  So no row follows an end, and the burst is empty.
module denotation.EmissionSet.Laws.HotInv where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (Equivalence)
open import Data.Bool.Properties using (T-≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.MonotonicList.Events using (Pos; sub; last; <ᵖ-split; <ᵖ-down)
open import denotation.EmissionSet using (Ev; end; EmissionSet; _≺_; _≼_; hot; Rejoin; shown; ended; late)
open import denotation.EmissionSet.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺-ext; ≼-trans; ≼-false)
open import denotation.EmissionSet.Laws.Worlds using (_⊕_; Lawful; W; W⁼; step; join; here; inW; Plain; plain-last; plain-sub; real-snoc; real-sub; Real; InvD;
  _⊑_; ⊑-snoc; ⊑-inside; ext≢; not-up; nest-in; named-view; named-e; anc-≼; world-anc⁼; world-after)

private
  module HI {A H p} {t : EmissionSet A} (L : Lawful t) where
    data Vw (y : Pos) (e : Ev A) : Set where
      jn : ∀ {q} → t q e → p ≺ q → y ≡ q ++ [ sub p ] → Vw y e
      lt : ∀ {c} → t c end → c ≼ p → e ≡ end → y ≡ p ++ [ last ] → Vw y e

    view : ∀ {y e} → Rejoin p t y e → Vw y e
    view (shown x _ pq) = jn x pq refl
    view (ended x pq)   = jn x pq refl
    view (late x cp)    = lt x cp refl refl

    -- Rows past `p` and an end by `p`: never both.
    no-mix : ∀ {q c e} → t q e → p ≺ q → t c end → c ≼ p → ⊥
    no-mix {q} {c} x pq xc cp = ≼-trans {q} {c} {p} (Lawful.proper L xc x) cp pq

    wo : ∀ {y e} → Vw y e → W (H ⊕ t) p y
    wo (jn x pq refl)    = join (inj₁ (inj₁ (_ , x))) here pq
    wo (lt _ _ _ refl)   = step here plain-last

    fu : ∀ {y e e′} → Vw y e → Vw y e′ → e ≡ e′
    fu (jn {q} x _ eq) (jn {q′} x′ _ eq′) with ∷ʳ-injectiveˡ q q′ (trans (sym eq) eq′)
    ... | refl = Lawful.func L x x′
    fu (jn x pq _)   (lt xc cp _ _)    = ⊥-elim (no-mix x pq xc cp)
    fu (lt xc cp _ _) (jn x pq _)      = ⊥-elim (no-mix x pq xc cp)
    fu (lt _ _ e _)  (lt _ _ e′ _)     = trans e (sym e′)

    fl : ∀ {y e y′ e′ l ys} → Vw y e → Vw y′ e′ → y′ ≡ y ++ l ∷ ys → ⊥
    fl {l = l} {ys} (jn {q} x _ refl) (jn {q′} x′ _ eq′) eq with ⊑-snoc {q ++ [ sub p ]} q′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₂ e = ext≢ (q ++ [ sub p ]) ys (trans (sym eq) (trans eq′ (sym e)))
    ... | inj₁ (zs , le) = Lawful.flat L x (subst (λ z → t z _) (trans le (++-assoc q [ sub p ] zs)) x′)
    fl (jn x pq _)    (lt xc cp _ _) _ = no-mix x pq xc cp
    fl (lt xc cp _ _) (jn x pq _)    _ = no-mix x pq xc cp
    fl {ys = ys} (lt _ _ _ refl) (lt _ _ _ eq′) eq = ext≢ (p ++ [ last ]) ys (trans (sym eq) eq′)

    bu : ∀ {c y e} → Vw c end → Vw y e → c ≺ y → ⊥
    bu (jn x pq _)      (lt xc cp _ _) _ = no-mix x pq xc cp
    bu (lt xc cp _ _)   (jn x pq _)    _ = no-mix x pq xc cp
    bu (lt _ _ _ refl)  (lt _ _ _ eq′) cy = ≺-irrefl {p ++ [ last ]} (subst ((p ++ [ last ]) ≺_) eq′ cy)
    bu (jn {q} xc _ refl) (jn {q′} x′ _ refl) cy with <ᵖ-split q′ q (≼-false {q′} {q} (Lawful.proper L xc x′))
    ... | inj₂ refl = ≺-irrefl {q ++ [ sub p ]} cy
    ... | inj₁ lt′  = ≺-absurd {q ++ [ sub p ]} {q′ ++ [ sub p ]} cy (Equivalence.from T-≡ (<ᵖ-down q′ q (sub p) (sub p) lt′ noext))
      where noext : ∀ l ls → q ≡ q′ ++ l ∷ ls → ⊥
            noext l ls eq = Lawful.flat L x′ (subst (λ z → t z end) eq xc)

lawful-hot : ∀ {A H} {t : EmissionSet A} → Lawful t → InvD (H ⊕ t) (hot t)
lawful-hot {H = H} {t} L p ok = record
  { world = λ x → wo (view (proj₁ x))
  ; real  = λ x → re (view (proj₁ x))
  ; func  = λ x x′ → fu (view (proj₁ x)) (view (proj₁ x′))
  ; flat  = λ x x′ → fl (view (proj₁ x)) (view (proj₁ x′)) refl
  ; burst = λ c y cy → ⊥-elim (bu (view (proj₁ c)) (view (proj₁ y)) cy)
  ; under = λ x y → un (view (proj₁ x)) (view (proj₁ y))
  ; quiet = λ c y cy → ⊥-elim (bu (view (proj₁ c)) (view (proj₁ y)) cy)
  }
  where
    open HI {H = H} {p} L
    re : ∀ {y e} → Vw y e → Real y
    re (jn {q} x pq refl) = real-sub q (Lawful.real L x) (proj₁ ok) (≺-trans {p} {q} {q ++ [ sub p ]} pq (≺-ext q []))
    re (lt _ _ _ refl)    = real-snoc p plain-last (proj₁ ok)

    -- Under a row's child lies neither the subscription nor a hot row.
    un : ∀ {q y w l e e′} → Vw q e → Vw y e′ → Plain l → W⁼ (H ⊕ t) (q ++ [ l ]) w → w ⊑ y → ⊥
    un (lt xc cp _ _) (jn x pq _) _ _ _ = no-mix x pq xc cp
    un (jn x pq _) (lt xc cp _ _) _ _ _ = no-mix x pq xc cp
    un (lt _ _ _ refl) (lt _ _ _ refl) pl v le = not-up (real-snoc p plain-last (proj₁ ok)) v le
    un {q} {l = l} vq@(jn _ _ _) (jn {q′} x′ _ refl) pl v le with ⊑-snoc q′ le
    ... | inj₁ le′ = proj₂ ok (inj₁ (_ , x′)) (nest-in (step (inW (wo vq)) pl) v) (⊑-inside le′)
    ... | inj₂ e   = anc-≼ (world-anc⁼ vp) (proj₁ ok) (world-after (step (inW (wo vq)) pl) (real-snoc q pl (re vq)))
      where vp : W⁼ (H ⊕ t) (q ++ [ l ]) p
            vp = named-e (named-view {h = q′} (subst (W⁼ (H ⊕ t) (q ++ [ l ])) e v)) λ eq → plain-sub pl (sym (∷ʳ-injectiveʳ q′ q eq))
