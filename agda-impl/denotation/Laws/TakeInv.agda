{-# OPTIONS --guardedness #-}

-- A TAKEWHILE KEEPS THE INVARIANT.  Its rows are the source's where they
-- lie, or one plain label below the first failing value.  A row below a
-- failing value and a row of the source at that value's position would
-- clash, and do not: the source has one event there, and the row kept at
-- it is either a passing value, a skip or end before every failure, or a
-- pin.
module denotation.Laws.TakeInv where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Events using (Pos; Label; ix; last; inside; inside-++; <ᵖ-part; <ᵖ-split; <ᵖ-apart)
open import denotation.EmissionSet using (Ev; out; end; skip; pin; Silent; hush; held; EmissionSet; _≺_; module TakeWhile; module Op)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd; ≺-ext; ≼-false; ≼-or-≻)
open import denotation.Laws.Worlds using (Plain; plain-ix; plain-last; W; W⁼; step; here; inW; real-snoc; Real; InvAt; InvD;
  ⊑-refl; ⊑-snoc⁺; ⊑-snoc; ⊑-inside; inside-⊑; conv; in-world; ext≢; same-lead; flat-under; _⊑_; w-up; nest⁼)

private
  T-not : ∀ {b} → T b → T (not b) → ⊥
  T-not {true}  _ ()
  T-not {false} ()

  module TI {A H p} (incl : Bool) (keep : A → Bool) {t : EmissionSet A} (I : InvAt H p t) where
    open TakeWhile incl keep t

    -- What a kept row of the source asserts of its event.
    Keeps : Ev A → Set
    Keeps (out a) = T (keep a)
    Keeps skip    = ⊤
    Keeps end     = ⊤
    Keeps (pin _) = ⊥

    -- A row where the source's lies: kept before every failure, or a pin.
    data Sm (y : Pos) : Ev A → Set where
      s-own  : ∀ {e} → Keeps e → ¬ Failed y → Sm y e
      s-left : ∀ {r} → ¬ Failed r → Sm y (pin r)

    -- A row below a failing value.
    data Sh (a : A) : Label → Ev A → Set where
      sh-fail : T incl → Sh a (ix 0) (out a)
      sh-stop : Sh a last end

    data Vw (y : Pos) (e : Ev A) : Set where
      sm : t y e → Sm y e → Vw y e
      sh : ∀ {q a l} → t q (out a) → T (not (keep a)) → ¬ Failed q → Sh a l e → y ≡ q ++ [ l ] → Vw y e

    view : ∀ {y e} → TakeT y e → Vw y e
    view (pass x k nf)    = sm x (s-own k nf)
    view (fail x nk nf i) = sh x nk nf (sh-fail i) refl
    view (stop x nk nf)   = sh x nk nf sh-stop refl
    view (step x nf)      = sm x (s-own tt nf)
    view (tend x nf)      = sm x (s-own tt nf)
    view (left x nf _)    = sm x (s-left nf)

    sh-plain : ∀ {a l e} → Sh a l e → Plain l
    sh-plain (sh-fail _) = plain-ix
    sh-plain sh-stop     = plain-last

    -- A row kept at a failing value's position is none.
    clash : ∀ {y e a} → t y e → Sm y e → t y (out a) → T (not (keep a)) → ¬ Failed y → ⊥
    clash x (s-own kp _) x′ nk _ = go (InvAt.func I x x′) kp nk
      where go : ∀ {e₀ a} → e₀ ≡ out a → Keeps e₀ → T (not (keep a)) → ⊥
            go refl kp′ nk′ = T-not kp′ nk′
    clash x (s-left _) x′ _ _ with InvAt.func I x x′
    ... | ()

    wo : ∀ {y e} → Vw y e → W H p y
    wo (sm x _)            = InvAt.world I x
    wo (sh x _ _ k refl)   = step (inW (InvAt.world I x)) (sh-plain k)

    re : ∀ {y e} → Vw y e → Real y
    re (sm x _)                  = InvAt.real I x
    re (sh {q = q} x _ _ k refl) = real-snoc q (sh-plain k) (InvAt.real I x)

    sh-func : ∀ {a a′ l e e′} → out a ≡ out a′ → Sh a l e → Sh a′ l e′ → e ≡ e′
    sh-func eq (sh-fail _) (sh-fail _) = eq
    sh-func eq sh-stop     sh-stop     = refl

    fu : ∀ {y e e′} → Vw y e → Vw y e′ → e ≡ e′
    fu (sm x _)             (sm x′ _)             = InvAt.func I x x′
    fu (sm x _)             (sh x′ _ _ _ refl)    = ⊥-elim (InvAt.flat I x′ x)
    fu (sh x _ _ _ refl)    (sm x′ _)             = ⊥-elim (InvAt.flat I x x′)
    fu (sh {q = q} x _ _ k eq) (sh {q = q′} x′ _ _ k′ eq′) with ∷ʳ-injectiveˡ q q′ (trans (sym eq) eq′) | ∷ʳ-injectiveʳ q q′ (trans (sym eq) eq′)
    ... | refl | refl = sh-func (InvAt.func I x x′) k k′

    fl : ∀ {y e y′ e′ l ys} → Vw y e → Vw y′ e′ → y′ ≡ y ++ l ∷ ys → ⊥
    fl (sm x _) (sm x′ _) refl = InvAt.flat I x x′
    fl {l = l} {ys} (sh x _ _ _ refl) (sm x′ _) eq = flat-under I x x′ (l ∷ ys , eq)
    fl {y} {l = l} {ys} (sm x k) (sh {q = q′} x′ nk nf _ eq′) eq with ⊑-snoc {y} q′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₂ e = ext≢ y ys (trans (sym eq) (trans eq′ (sym e)))
    ... | inj₁ le with same-lead I x x′ le
    ...   | refl = clash x k x′ nk nf
    fl {l = l} {ys} (sh {q = q} {l = l₀} x _ _ _ refl) (sh {q = q′} x′ _ _ _ eq′) eq with ⊑-snoc {q ++ [ l₀ ]} q′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₁ le = flat-under I x x′ le
    ... | inj₂ e  = ext≢ (q ++ [ l₀ ]) ys (trans (sym eq) (trans eq′ (sym e)))

    -- Nothing follows a stop at its own value.
    stop-last : ∀ r {a l e} → Sh a l e → (r ++ [ last ]) ≺ (r ++ [ l ]) → ⊥
    stop-last r (sh-fail _) lt = ≺-absurd {r ++ [ last ]} {r ++ [ ix 0 ]} lt (Equivalence.from T-≡ (<ᵖ-part r {ix 0} {last} [] [] refl))
    stop-last r sh-stop     lt = ≺-irrefl {r ++ [ last ]} lt

    -- Nothing below a failing value follows a stop.
    stop-sh : ∀ {r q′ a a′ l′ e} → t r (out a) → T (not (keep a)) → t q′ (out a′) → ¬ Failed q′ → Sh a′ l′ e → (r ++ [ last ]) ≺ (q′ ++ [ l′ ]) → ⊥
    stop-sh {r} {q′} {l′ = l′} xr nk xy nf′ k′ cy with ≼-or-≻ q′ r
    ... | inj₂ rq = nf′ (r , _ , xr , nk , rq)
    ... | inj₁ qr with <ᵖ-split q′ r (≼-false {q′} {r} qr)
    ...   | inj₂ refl = stop-last r k′ cy
    ...   | inj₁ lt   = ≺-absurd {r} {q′ ++ [ l′ ]} (≺-trans {r} {r ++ [ last ]} (≺-ext r []) cy)
                                  (Equivalence.from T-≡ (<ᵖ-apart q′ r [ l′ ] lt noext))
      where noext : ∀ ys → r ≡ q′ ++ ys → ⊥
            noext []       eq = ≺-irrefl {q′} (subst (q′ ≺_) (trans eq (++-identityʳ q′)) (Equivalence.from T-≡ lt))
            noext (l ∷ ys) eq = InvAt.flat I xy (subst (λ z → t z _) eq xr)

    bu : ∀ {c y e} → Vw c end → Vw y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)
    bu {c} (sm xc (s-own _ _)) (sm xy _) cy = InvAt.burst I xc xy cy
    bu {c} (sm xc (s-own _ _)) (sh {q = q′} {l = l′} xy _ _ _ refl) cy with ≼-or-≻ q′ c
    ... | inj₂ lt with InvAt.burst I xc xy lt
    ...   | w , w⁼ , ic , iq = w , w⁼ , ic , Equivalence.from T-≡ (inside-++ w q′ [ l′ ] (Equivalence.to T-≡ iq))
    bu {c} (sm xc (s-own _ _)) (sh {q = q′} xy _ _ _ refl) cy | inj₁ le with same-lead I xy xc (conv (⊑-refl q′) le cy (⊑-snoc⁺ q′))
    ... | refl with InvAt.func I xy xc
    ...   | ()
    bu (sh {q = r} xr nk nf sh-stop refl) (sm xy (s-own _ nfy)) cy =
      ⊥-elim (nfy (r , _ , xr , nk , ≺-trans {r} {r ++ [ last ]} (≺-ext r []) cy))
    bu {y = y} (sh {q = r} xr nk nf sh-stop refl) (sm xy (s-left {w} nfw)) cy with InvAt.pinned I xy
    ... | w⁼ , iy = w , w⁼ , Equivalence.from T-≡ (inside-++ w r [ last ] (Equivalence.to T-≡ (⊑-inside
          (conv {w} {w} {r} {y} (⊑-refl w) (λ lt → nfw (r , _ , xr , nk , lt)) (≺-trans {r} {r ++ [ last ]} {y} (≺-ext r []) cy) (inside-⊑ w y iy))))) , iy
    bu (sh {q = r} xr nk nf sh-stop refl) (sh xy nk′ nf′ k′ refl) cy = ⊥-elim (stop-sh xr nk xy nf′ k′ cy)

    -- Only skips follow an end.
    qu : ∀ {c y e} → Vw c end → Vw y e → c ≺ y → Silent e
    qu _ (sm _ (s-left _)) _ = held
    qu (sm xc (s-own _ _)) (sm xy (s-own _ _)) cy = InvAt.quiet I xc xy cy
    qu {c} (sm xc (s-own _ _)) (sh {q = q′} xy _ _ _ refl) cy with ≼-or-≻ q′ c
    ... | inj₂ lt with InvAt.quiet I xc xy lt
    ...   | ()
    qu {c} (sm xc (s-own _ _)) (sh {q = q′} xy _ _ _ refl) cy | inj₁ le with same-lead I xy xc (conv (⊑-refl q′) le cy (⊑-snoc⁺ q′))
    ... | refl with InvAt.func I xy xc
    ...   | ()
    qu (sh {q = r} xr nk nf sh-stop refl) (sm xy (s-own _ nfy)) cy =
      ⊥-elim (nfy (r , _ , xr , nk , ≺-trans {r} {r ++ [ last ]} (≺-ext r []) cy))
    qu (sh xr nk nf sh-stop refl) (sh xy nk′ nf′ k′ refl) cy = ⊥-elim (stop-sh xr nk xy nf′ k′ cy)

    pn : ∀ {y r} → Vw y (pin r) → W⁼ H p r × T (inside r y)
    pn (sm x _)          = InvAt.pinned I x
    pn (sh _ _ _ () _)

    -- Under a kept row's child lies no other: a row's child below a
    -- failing value is the value's, or under it.
    un : ∀ {q y w l e e′} → Vw q e → Vw y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
    un (sm xq _) (sm xy _) pl v le = InvAt.under I xq xy pl v le
    un (sh xr _ _ k refl) (sm xy _) pl v le = InvAt.under I xr xy (sh-plain k) (nest⁼ (inW (step here pl)) v) le
    un {q} {l = l} (sm xq kq) (sh {q = q′} xy nk nf k refl) pl v le with ⊑-snoc q′ le
    ... | inj₁ le′ = InvAt.under I xq xy pl v le′
    ... | inj₂ e with w-up (sh-plain k) (subst (W⁼ H (q ++ [ l ])) e v)
    ...   | inj₂ v′ = InvAt.under I xq xy pl v′ (⊑-refl q′)
    ...   | inj₁ eq with ∷ʳ-injectiveˡ q q′ eq
    ...     | refl = clash xq kq xy nk nf
    un {q} {l = l} (sh xr _ _ k₀ refl) (sh {q = q′} xy _ _ k refl) pl v le with ⊑-snoc q′ le
    ... | inj₁ le′ = InvAt.under I xr xy (sh-plain k₀) (nest⁼ (inW (step here pl)) v) le′
    ... | inj₂ e with w-up (sh-plain k) (subst (W⁼ H (q ++ [ l ])) e v)
    ...   | inj₁ eq = InvAt.flat I xr (subst (λ z → t z _) (sym (∷ʳ-injectiveˡ q q′ eq)) xy)
    ...   | inj₂ v′ = InvAt.under I xr xy (sh-plain k₀) (nest⁼ (inW (step here pl)) v′) (⊑-refl q′)

takeWhile-inv : ∀ {A H} (i : Bool) (keep : A → Bool) {s} → InvD {A} H s → InvD H (Op.takeWhile i keep s)
takeWhile-inv i keep inv p ok = record
  { world = λ x → wo (view (proj₁ x))
  ; real  = λ x → re (view (proj₁ x))
  ; func  = λ x x′ → fu (view (proj₁ x)) (view (proj₁ x′))
  ; flat  = λ x x′ → fl (view (proj₁ x)) (view (proj₁ x′)) refl
  ; burst = λ c y cy → bu (view (proj₁ c)) (view (proj₁ y)) cy
  ; under = λ x y → un (view (proj₁ x)) (view (proj₁ y))
  ; quiet = λ c y cy → qu (view (proj₁ c)) (view (proj₁ y)) cy
  ; pinned = λ x → pn (view (proj₁ x))
  }
  where open TI i keep (inv p ok)
