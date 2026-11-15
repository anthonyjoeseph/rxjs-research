-- AN EXHAUST'S DECISIONS, MOVED: two exhausts whose values correspond
-- one to one in order (`R`), within bounds closed downward, and whose
-- running lanes end before a value on one side exactly when they do on
-- the other (`end←`, `end→`), run the same values (`cur←`).
module simultaneous.ExMove where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (out; end; EmissionSet; Den; _≺_; _≼_; LaneOf; module Exhaust; module Values)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-or-≻; ≼-split)

-- The last lane run's position is a value.
cur-o : ∀ {A B : Set} {f : A → Den B} {o : EmissionSet A} {q₁ q} → Exhaust.Cur f o q₁ q → Σ A λ a → o q₁ (out a)
cur-o (Exhaust.cur₀ x _)             = _ , x
cur-o (Exhaust.run _ _ _ _ x _ _)    = _ , x
cur-o (Exhaust.drop _ _ _ x _ _)     = _ , x

-- The last lane run is a run.
cur-run : ∀ {A B : Set} {f : A → Den B} {o : EmissionSet A} {q₁ q} → Exhaust.Cur f o q₁ q → Exhaust.Run f o q
cur-run c@(Exhaust.cur₀ _ _)             = c
cur-run c@(Exhaust.run _ _ _ _ _ _ _)    = c
cur-run (Exhaust.drop c _ _ _ _ _)       = cur-run c

module _ {A A₂ B B₂ : Set} (f : A → Den B) (o : EmissionSet A) (f₂ : A₂ → Den B₂) (o₂ : EmissionSet A₂)
         (R : Pos → Pos → Set) (In : Pos → Set) (InP : Pos → Set)
         (in↓ : ∀ {y y′} → In y → y′ ≺ y → In y′) (inP↓ : ∀ {q q′} → InP q → q′ ≺ q → InP q′)
         (in-p : ∀ {q y} → R q y → In y → InP q)
         (R-o : ∀ {q y} → R q y → Σ A λ a → o q (out a)) (R-o₂ : ∀ {q y} → R q y → Σ A₂ λ a → o₂ y (out a))
         (back : ∀ {y a₂} → o₂ y (out a₂) → In y → Σ Pos λ q → R q y)
         (fwd : ∀ {q a} → o q (out a) → InP q → Σ Pos λ y → R q y)
         (mono : ∀ {q q′ y y′} → R q y → R q′ y′ → q ≺ q′ → y ≺ y′)
         (R-fun : ∀ {q y y′} → R q y → R q y′ → y ≡ y′)
         (end← : ∀ {q y a a₂ q′ y′ c} → Exhaust.Run f o q → o q (out a) → o₂ y (out a₂) → R q y → R q′ y′ → In y′
               → LaneOf f₂ y a₂ c end → c ≺ y′ → Σ Pos λ c′ → LaneOf f q a c′ end × c′ ≺ q′)
         (end→ : ∀ {q y a a₂ q′ y′ c′} → Exhaust.Run f o q → o q (out a) → o₂ y (out a₂) → R q y → R q′ y′ → In y′
               → LaneOf f q a c′ end → c′ ≺ q′ → Σ Pos λ c → LaneOf f₂ y a₂ c end × c ≺ y′) where

  private
    module E = Exhaust f o
    module E₂ = Exhaust f₂ o₂

  -- Read back, values keep their order.
  reflect : ∀ {q q′ y y′} → R q y → R q′ y′ → y ≺ y′ → q ≺ q′
  reflect {q} {q′} {y} {y′} r r′ lt with ≼-or-≻ q′ q
  ... | inj₂ qq = qq
  ... | inj₁ qq with ≼-split {q′} {q} qq
  ...   | inj₁ q′q = ⊥-elim (≺-absurd {y} {y′} lt (mono r′ r q′q))
  ...   | inj₂ refl with R-fun r r′
  ...     | refl = ⊥-elim (≺-irrefl {y} lt)

  -- No plain value between two read back with none between them.
  next← : ∀ {q₀ q₁ y₀ y₁} → R q₀ y₀ → R q₁ y₁ → In y₁ → Values.Next o₂ y₀ y₁ → Values.Next o q₀ q₁
  next← r₀ r₁ i₁ nx ok q₀k kq₁ =
    let (yk , rk) = fwd ok (inP↓ (in-p r₁ i₁) kq₁) in nx (proj₂ (R-o₂ rk)) (mono r₀ rk q₀k) (mono rk r₁ kq₁)

  -- The last lane run, read back.
  cur← : ∀ {y₁ y} → E₂.Cur y₁ y → In y₁ → ∀ {q₁} → R q₁ y₁ → Σ Pos λ q → R q y × E.Cur q₁ q
  cur← (E₂.cur₀ _ least) iy {q₁} r = q₁ , r , E.cur₀ (proj₂ (R-o r)) lst
    where
      lst : ∀ {k b} → o k (out b) → q₁ ≼ k
      lst ok kq = let (yk , rk) = fwd ok (inP↓ (in-p r iy) kq) in least (proj₂ (R-o₂ rk)) (mono rk r kq)
  cur← (E₂.run cur oyr lane cy _ y₀y nx) iy {q₁} r =
    let (q₀ , r₀)     = back (proj₂ (cur-o cur)) (in↓ iy y₀y)
        (q , rq , cq) = cur← cur (in↓ iy y₀y) r₀
        (_ , oq)      = R-o rq
        (_ , l′ , c′q) = end← (cur-run cq) oq oyr rq r iy lane cy
    in q₁ , r , E.run cq oq l′ c′q (proj₂ (R-o r)) (reflect r₀ r y₀y) (next← r₀ r iy nx)
  cur← (E₂.drop cur oyr nol _ y₀y nx) iy {q₁} r =
    let (q₀ , r₀)     = back (proj₂ (cur-o cur)) (in↓ iy y₀y)
        (q , rq , cq) = cur← cur (in↓ iy y₀y) r₀
        (_ , oq)      = R-o rq
    in q , rq , E.drop cq oq (λ l′ c′q → let (_ , l , cy) = end→ (cur-run cq) oq oyr rq r iy l′ c′q in nol l cy)
                         (proj₂ (R-o r)) (reflect r₀ r y₀y) (next← r₀ r iy nx)

  -- One value read at each position.
  inj : ∀ {q q′ y} → R q y → R q′ y → q ≡ q′
  inj {q} {q′} {y} r r′ with ≼-or-≻ q q′
  ... | inj₂ q′q = ⊥-elim (≺-irrefl {y} (mono r′ r q′q))
  ... | inj₁ qq with ≼-split {q} {q′} qq
  ...   | inj₁ lt = ⊥-elim (≺-irrefl {y} (mono r r′ lt))
  ...   | inj₂ eq = eq

  -- A lane run, read back.
  run← : ∀ {y q} → E₂.Run y → In y → R q y → E.Run q
  run← {q = q} cur iy r = let (q′ , r′ , c) = cur← cur iy r in subst (E.Cur q) (inj r′ r) c
