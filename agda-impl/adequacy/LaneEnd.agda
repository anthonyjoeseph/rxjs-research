{-# OPTIONS --guardedness #-}

-- A LANE'S END, READ AT ITS MERGE: a lane owing only its end at `p`,
-- every other part of the merge strictly past `p`, `n` lanes live.  Off
-- `p` the merge owes what it owes with the lane gone and `pred n` live;
-- at `p` it owes its own end when the lane was the last live one and its
-- outer is done, and a skip otherwise.
module adequacy.LaneEnd where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (Bool; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; end; _≼_)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl)
open import adequacy.Rows using (∅; Plus; old; new; Lanes; Each; Kth; AllEnd; EndsOf; module Flat)
open import adequacy.Up using (any-ʳ++; any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++)
open import adequacy.Bound using (Empty)
open import adequacy.Skip using (After; Since; _≈⟨_⟩_; after-since; since-lanes; lane-since; since-flat)
open import adequacy.Policy using (flatP)
open import adequacy.JoinEnd using (EndsAt; module Frame)

-- Two lists of ends one place apart: `x` in the one where `y` is in the
-- other.
data Sw (x y : Pos → Set) : List (Pos → Set) → List (Pos → Set) → Set₁ where
  here  : ∀ {r} → Sw x y (x ∷ r) (y ∷ r)
  there : ∀ {l xs ys} → Sw x y xs ys → Sw x y (l ∷ xs) (l ∷ ys)

sw-ends : ∀ {B} {x y} (Pre : List (EmissionSet B)) {Z W} → Sw x y (EndsOf Z) (EndsOf W) → Sw x y (EndsOf (Pre ʳ++ Z)) (EndsOf (Pre ʳ++ W))
sw-ends []        s = s
sw-ends (_ ∷ Pre) s = sw-ends Pre (there s)

-- A end somewhere among the lanes.
Has : (Pos → Set) → (Pos → Set) → Set
Has P l = Σ Pos λ c → l c × P c

kth-skip : ∀ {P l} ls k → Kth P ls k → Kth P (l ∷ ls) k
kth-skip ls zero    x = inj₂ x
kth-skip ls (suc k) x = inj₂ x

kth-less : ∀ {P} ls k → Kth P ls (suc k) → Kth P ls k
kth-less (_ ∷ ls) zero    (inj₁ (h , _)) = inj₁ h
kth-less (_ ∷ ls) zero    (inj₂ x)       = inj₂ (kth-less ls zero x)
kth-less (_ ∷ ls) (suc k) (inj₁ (h , x)) = inj₁ (h , kth-less ls k x)
kth-less (_ ∷ ls) (suc k) (inj₂ x)       = inj₂ (kth-less ls (suc k) x)

-- One end fewer: at most one fewer among them.
kth-drop : ∀ {P x y xs ys} → Sw x y xs ys → ∀ k → Kth P xs (suc k) → Kth P ys k
kth-drop {ys = _ ∷ r} here k (inj₁ (_ , kr)) = kth-skip r k kr
kth-drop {ys = _ ∷ r} here k (inj₂ kr)       = kth-skip r k (kth-less r k kr)
kth-drop (there s) zero    (inj₁ (h , _))  = inj₁ h
kth-drop (there s) zero    (inj₂ x)        = inj₂ (kth-drop s zero x)
kth-drop (there s) (suc k) (inj₁ (h , x))  = inj₁ (h , kth-drop s k x)
kth-drop (there s) (suc k) (inj₂ x)        = inj₂ (kth-drop s (suc k) x)

kth-at : ∀ {P x y xs ys} → Sw x y xs ys → Has P x → Kth P xs 0
kth-at here      h = inj₁ h
kth-at (there s) h = inj₂ (kth-at s h)

-- An end in for one that never comes: one more among them.
kth-add : ∀ {P x y xs ys} → Sw x y xs ys → Has P x → (∀ {c} → ¬ y c) → ∀ k → Kth P ys k → Kth P xs (suc k)
kth-add here      h ny zero    (inj₁ (_ , yc , _)) = ⊥-elim (ny yc)
kth-add here      h ny zero    (inj₂ kr)           = inj₁ (h , kr)
kth-add here      h ny (suc k) (inj₁ ((_ , yc , _) , _)) = ⊥-elim (ny yc)
kth-add here      h ny (suc k) (inj₂ kr)           = inj₁ (h , kr)
kth-add (there s) h ny zero    (inj₁ hl)       = inj₁ (hl , kth-at s h)
kth-add (there s) h ny zero    (inj₂ x)        = inj₂ (kth-add s h ny zero x)
kth-add (there s) h ny (suc k) (inj₁ (hl , x)) = inj₁ (hl , kth-add s h ny k x)
kth-add (there s) h ny (suc k) (inj₂ x)        = inj₂ (kth-add s h ny (suc k) x)

-- An end among the lanes is a lane's end.
kth-lanes : ∀ {B P} (Ls : List (EmissionSet B)) k → Kth P (EndsOf Ls) k → Σ Pos λ c → Lanes Ls c end × P c
kth-lanes (_ ∷ Ls) zero    (inj₁ (c , r , pc))     = c , inj₁ r , pc
kth-lanes (_ ∷ Ls) zero    (inj₂ x) with kth-lanes Ls zero x
... | c , l , pc = c , inj₂ l , pc
kth-lanes (_ ∷ Ls) (suc k) (inj₁ ((c , r , pc) , _)) = c , inj₁ r , pc
kth-lanes (_ ∷ Ls) (suc k) (inj₂ x) with kth-lanes Ls (suc k) x
... | c , l , pc = c , inj₂ l , pc

after-lanes : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → ∀ {k e} → Lanes Ls k e → ¬ k ≼ p
after-lanes (_ ∷ _)  (a , _)  (inj₁ r) kp = kp (a r)
after-lanes {p = p} (_ ∷ Ls) (_ , as) (inj₂ x) kp = after-lanes {p = p} Ls as x kp

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B}
         (ao : After p O) (apre : Each (After p) Pre) (apost : Each (After p) Post) (e₀ : Empty t₀) where

  LX = Pre ʳ++ (Plus t₀ p end ∷ Post)
  LY = Pre ʳ++ (∅ ∷ Post)
  X  = Flat.JoinT L O d n LX
  Y  = Flat.JoinT L O d (pred n) LY

  sw : Sw (λ c → Plus t₀ p end c end) (λ c → ∅ {B} c end) (EndsOf LX) (EndsOf LY)
  sw = sw-ends Pre here

  at-p : ∀ c → p ≼ c → Has (_≼ c) (λ c → Plus t₀ p end c end)
  at-p c pc = p , new , pc

  none : ∀ {c} → ¬ ∅ {B} c end
  none ()

  ends-xy : ∀ c k → AllEnd (_≼ c) k (EndsOf LX) → AllEnd (_≼ c) (pred k) (EndsOf LY)
  ends-xy c zero          _ = _
  ends-xy c (suc zero)    _ = _
  ends-xy c (suc (suc k)) x = kth-drop {P = _≼ c} sw k x

  ends-yx : ∀ c k → p ≼ c → AllEnd (_≼ c) (pred k) (EndsOf LY) → AllEnd (_≼ c) k (EndsOf LX)
  ends-yx c zero          pc _ = _
  ends-yx c (suc zero)    pc _ = kth-at {P = _≼ c} sw (at-p c pc)
  ends-yx c (suc (suc k)) pc y = kth-add {P = _≼ c} sw (at-p c pc) (λ {c′} → none {c′}) k y

  after-y : ∀ {k e} → Lanes LY k e → ¬ k ≼ p
  after-y x with any-ʳ++ Pre x
  ... | inj₁ a        = after-lanes {p = p} Pre apre a
  ... | inj₂ (inj₁ ())
  ... | inj₂ (inj₂ b) = after-lanes {p = p} Post apost b

  so : Since p O
  so {q} {e} r = ≺→≼ {p} {q} (ao {q} {e} r)

  sx : Each (Since p) LX
  sx = all-ʳ++ Pre (after-since Pre apre) (hole , after-since Post apost)
    where
      hole : Since p (Plus t₀ p end)
      hole (old r) = ⊥-elim (e₀ r)
      hole new     = ≼-refl {p}

  sy : Each (Since p) LY
  sy = all-ʳ++ Pre (after-since Pre apre) ((λ ()) , after-since Post apost)

  lanes-xy : ∀ {k e} → Lanes LX k e → Lanes LY k e ⊎ (k ≡ p × e ≡ end)
  lanes-xy x with any-ʳ++ Pre x
  ... | inj₁ a              = inj₁ (any-ʳ++ˡ Pre a)
  ... | inj₂ (inj₁ (old r)) = ⊥-elim (e₀ r)
  ... | inj₂ (inj₁ new)     = inj₂ (refl , refl)
  ... | inj₂ (inj₂ b)       = inj₁ (any-ʳ++ʳ Pre (inj₂ b))

  lanes-yx : ∀ {k e} → Lanes LY k e → Lanes LX k e
  lanes-yx x with any-ʳ++ Pre x
  ... | inj₁ a        = any-ʳ++ˡ Pre a
  ... | inj₂ (inj₁ ())
  ... | inj₂ (inj₂ b) = any-ʳ++ʳ Pre (inj₂ b)

  done-xy : ∀ c → p ≼ c → Flat.Done L O d n LX c → Flat.Done L O d (pred n) LY c
  done-xy c pc (Flat.over-at g ls , h) = Flat.over-at g (ends-xy c n ls) , h

  done-yx : ∀ c → p ≼ c → Flat.Done L O d (pred n) LY c → Flat.Done L O d n LX c
  done-yx c pc (Flat.over-at g ls , h) = Flat.over-at g (ends-yx c n pc ls) , h

  -- The merge done at `p` exactly when the lane was the last live one.
  done-at : T d → pred n ≡ 0 → Flat.Done L O d n LX p
  done-at td pn = Flat.over-at (inj₁ td) (ends n pn) , λ {q} r _ lt _ → ⊥-elim (≺→≼ {p} {q} (ao r) lt)
    where
      ends : ∀ k → pred k ≡ 0 → AllEnd (_≼ p) k (EndsOf LX)
      ends zero       _ = _
      ends (suc zero) _ = kth-at {P = _≼ p} sw (at-p p (≼-refl {p}))
      ends (suc (suc _)) ()

  outer-owes : ¬ T d → ¬ Flat.Done L O d n LX p
  outer-owes nd (Flat.over-at (inj₁ td) _ , _)             = nd td
  outer-owes nd (Flat.over-at (inj₂ (c₀ , x , c₀p)) _ , _) = c₀p (ao x)

  -- Another lane live: it ends past `p`.
  lanes-owe : ∀ {k} → pred n ≡ suc k → ¬ Flat.Done L O d n LX p
  lanes-owe pn (Flat.over-at _ ls , _) = go n pn ls
    where
      go : ∀ m {k} → pred m ≡ suc k → ¬ AllEnd (_≼ p) m (EndsOf LX)
      go zero          ()
      go (suc zero)    ()
      go (suc (suc m)) refl x with kth-lanes LY m (kth-drop {P = _≼ p} sw m x)
      ... | c , l , cp = after-y l cp

  -- The merge's two readings past `p`, the lane's end at `p` unhanded.
  ends-at : EndsAt (flatP L O d n LX) (flatP L O d (pred n) LY) p
  ends-at = record
    { o→ = λ r → r ; o← = λ r → r ; so = so ; sb = since-lanes LX sx
    ; sl = λ {q} {a} r l → lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → u ; ru← = λ _ u → u ; cu→ = λ _ () ; cu← = λ _ ()
    ; ha→ = λ _ () ; ha← = λ _ () ; dn→ = λ {c} → done-xy c ; dn← = λ {c} → done-yx c
    ; bg→ = lanes-xy ; bg← = lanes-yx ; at = any-ʳ++ʳ Pre (inj₁ new) ; nh = λ () }

  -- THE FRAME: the merge with the lane read as `Y′`, which owes `Y` and
  -- at most the merge's own end at `p`.
  frame-≈ : (Y′ : EmissionSet B) → (Flat.Done L O d n LX p → Y′ p end) → (∀ {k e} → Y k e → Y′ k e)
          → (∀ {k e} → Y′ k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O d n LX p)) → X ≈⟨ p ⟩ Y′
  frame-≈ = Frame.frame-≈ ends-at

  since-x : Since p X
  since-x = since-flat L O LX so sx

  since-y : Since p Y
  since-y = since-flat L O LY so sy
