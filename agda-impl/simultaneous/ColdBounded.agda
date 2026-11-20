{-# OPTIONS --guardedness #-}

-- A COLD'S CUTS ARE BOUNDED (`cold-bounded`).  Its cut at `N` is its
-- stream's first `3 + N` rows, and its boundary the row after them
-- (`simultaneous.HorizonTree.cold-bd`).  The stream runs in order
-- (`denotation.Laws.ColdInv.cold-asc`), so a row before the boundary is
-- shallower than it, in every deeper cut and this one; and no row lies
-- under another, so none under the boundary or over it.
module simultaneous.ColdBounded where

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; _≤?_)
open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-≤; ≰⇒>; m≤n⇒m<n∨m≡n; suc-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (yes; no)

open import Tree using (cold)
open import denotation.Position using (Pos)
open import denotation.Events using (Timeline; timelineAt; start; Events)
open import denotation.EmissionSet using (Ev; pin; _≺_; _≼_; InE; at-out; at-skip; at-end; on-out; on-skip; enter; module Op)
open import denotation.Laws.Modulus using (⟨_⟩; ≺-irrefl; ≺→≼; ≼-refl; ≺-≼-≺)
open import denotation.Laws.Worlds using (Ok; InvAt; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.Laws.ColdInv using (depth; cold-inv; cold-reach; cold-asc)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled.Exact.Base using (sound; complete)
open import simultaneous.Listing using (walkN-exact)
open import simultaneous.Horizon using (Tag; module Cuts)
open import simultaneous.Placed using (module Placing)
open import simultaneous.HorizonTree using (Cut; cold-bd)

------------------------------------------------------------------------
-- A stream's rows by depth

private
  -- Every shallower depth holds a row.
  shallower : ∀ {A} {ev : Events A} {y e} (x : InE ev y e) j → j ≤ depth x
            → Σ Pos λ y′ → Σ (Ev A) λ e′ → Σ (InE ev y′ e′) λ x′ → depth x′ ≡ j
  shallower at-out      zero    _       = _ , _ , at-out , refl
  shallower at-skip     zero    _       = _ , _ , at-skip , refl
  shallower at-end      zero    _       = _ , _ , at-end , refl
  shallower (on-out x)  zero    _       = _ , _ , at-out , refl
  shallower (on-skip x) zero    _       = _ , _ , at-skip , refl
  shallower (on-out x)  (suc j) (s≤s le) with shallower x j le
  ... | y′ , e′ , x′ , d = y′ , e′ , on-out x′ , cong suc d
  shallower (on-skip x) (suc j) (s≤s le) with shallower x j le
  ... | y′ , e′ , x′ , d = y′ , e′ , on-skip x′ , cong suc d

  -- One depth, one row.
  same-depth : ∀ {A} {ev : Events A} {y y′ e e′} (x : InE ev y e) (x′ : InE ev y′ e′) → depth x ≡ depth x′ → y ≡ y′
  same-depth at-out      at-out       _ = refl
  same-depth at-skip     at-skip      _ = refl
  same-depth at-end      at-end       _ = refl
  same-depth (on-out x)  (on-out x′)  d = same-depth x x′ (suc-injective d)
  same-depth (on-skip x) (on-skip x′) d = same-depth x x′ (suc-injective d)
  same-depth at-out      (on-out _)   ()
  same-depth (on-out _)  at-out       ()
  same-depth at-skip     (on-skip _)  ()
  same-depth (on-skip _) at-skip      ()

------------------------------------------------------------------------
-- A cold's cuts

-- A row of the cut at `N` is a row of the stream, shallower than `3 + N`.
cold-row : ∀ {Γ A} n (c : Timeline A) (ρ : ℕ → All Tb.Listed Γ) p {N y e}
         → Cut n (cold c) ρ p N y e → Σ (InE (start p (timelineAt c p)) y e) λ x → depth x < 3 + N
cold-row n c ρ p {N} (_ , refl , mem) = sound (walkN-exact (3 + N) (start p (timelineAt c p))) mem

cold-bounded : ∀ {Γ A} n (c : Timeline A) (ρ : ℕ → All Tb.Listed Γ) p {H} → Ok H p → Cuts.Bounded (Cut n (cold c) ρ p) (cold-bd c p)
cold-bounded {A = A} n c ρ p ok = record
  { gap = gap ; held-in = λ { (() , _) } ; held-under = λ { (() , _) }
  ; fwd = λ {N} {k} → fwd {N} {k} ; fwd-pin = λ {N} {q} {k} → fwd-pin {N} {q} {k} }
  where
    open Cuts (Cut n (cold c) ρ p) (cold-bd c p)

    ev : Events A
    ev = start p (timelineAt c p)

    rp = proj₁ ok

    row : ∀ {N y e} → Cut n (cold c) ρ p N y e → Σ (InE ev y e) λ x → depth x < 3 + N
    row = cold-row n c ρ p

    cut : ∀ {N y e} (x : InE ev y e) → depth x < 3 + N → Cut n (cold c) ρ p N y e
    cut {N} x lt = _ , refl , complete (walkN-exact (3 + N) ev) (x , lt)

    entered : ∀ {y e} → InE ev y e → enter (Op.cold c) p y e
    entered x = x , cold-reach p (timelineAt c p) rp x

    gap : ∀ {N b g y e} → cold-bd c p N b g → Cut n (cold c) ρ p N y e → _
    gap {N} {b} {g} {y} {e} (refl , e₀ , xb , db) r = below
      where
        x = proj₁ (row r)

        yb : y ≺ b
        yb = cold-asc p (timelineAt c p) rp x xb (subst (depth x <_) (sym db) (proj₂ (row r)))

        below : _
        below ([] , eq)     = ≺-irrefl {y} (subst (y ≺_) (trans eq (⊕-identityʳ y)) yb)
        below (l ∷ ys , eq) = InvAt.flat (cold-inv c p ok) (entered x) (subst (λ z → enter (Op.cold c) p z e₀) eq (entered xb))

    fwd : ∀ {N k} → Clear N k → Settled N k
    fwd {N} {k} cl {N′} le = ⟨ (λ {y} {e} yk → (λ r → cut (proj₁ (row r)) (<-≤-trans (proj₂ (row r)) (+-monoʳ-≤ 3 le))) , back yk) ⟩
      where
        back : ∀ {y e} → y ≼ k → Cut n (cold c) ρ p N′ y e → Cut n (cold c) ρ p N y e
        back {y} {e} yk r with 3 + N ≤? depth (proj₁ (row r))
        ... | no ¬ge = cut (proj₁ (row r)) (≰⇒> ¬ge)
        ... | yes ge with shallower (proj₁ (row r)) (3 + N) ge
        ...   | b , e₀ , xb , db = ⊥-elim (yk (≺-≼-≺ {k} {b} {y} (cl (refl , e₀ , xb , db)) by))
          where
            by : b ≼ y
            by with m≤n⇒m<n∨m≡n ge
            ... | inj₁ lt = ≺→≼ {b} {y} (cold-asc p (timelineAt c p) rp xb (proj₁ (row r)) (subst (_< depth (proj₁ (row r))) (sym db) lt))
            ... | inj₂ eq = subst (b ≼_) (same-depth xb (proj₁ (row r)) (trans db eq)) (≼-refl {b})

    -- A cold holds no pin.
    nopin : ∀ {M y q} {Z : Set} → Cut n (cold c) ρ p M y (pin q) → Z
    nopin r = ⊥-elim (ine-pin (proj₁ (row r)))

    fwd-pin : ∀ {N q k} → Clear N q → HeldClear N q k → PinSettled N q k
    fwd-pin {N} {q} {k} _ _ {N′} _ {y} _ = (λ r → nopin {N} r) , (λ r → nopin {N′} r)

-- A COLD'S BOUNDARY IS PLACED: it is a row of its stream, so it lies in
-- the stream's world, and no plain child of an earlier row leads it.
cold-placed : ∀ {Γ A} n (c : Timeline A) (ρ : ℕ → All Tb.Listed Γ) p {H : ℕ → Pos → Set} {Env : ℕ → Pos → Tag → Set}
            → (∀ N → Ok (H N) p) → Placing.Placed H Env p (Cut n (cold c) ρ p) (cold-bd c p)
cold-placed n c ρ p ok {N} (refl , e₀ , xb , _) = inj₁ (record
  { world  = InvAt.world I (entered xb)
  ; real   = InvAt.real I (entered xb)
  ; under  = λ r pl v le → InvAt.under I (entered (proj₁ (cold-row n c ρ p r))) (entered xb) pl v le
  ; holder = λ () })
  where
    I = cold-inv c p (ok N)

    entered : ∀ {y e} → InE (start p (timelineAt c p)) y e → enter (Op.cold c) p y e
    entered x = x , cold-reach p (timelineAt c p) (proj₁ (ok N)) x
