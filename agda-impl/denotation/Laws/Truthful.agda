{-# OPTIONS --guardedness #-}

-- AN APPROXIMANT NEVER LIES.  It stops short at a cut `defer`, whose spin
-- runs forever in one instant and shows nothing, but every value, mark
-- and end it shows is one the meaning shows, with the same past.  Before
-- a spin's instant it is the meaning; within it, a row past the spin's
-- first has endlessly many before it.  So wherever finitely many rows
-- precede, the approximant agrees with the meaning up to a row it shows
-- and up to the first row of an instant; and an approximant with
-- finitely many rows in all reached no cut, so it is the meaning.
--
-- Conversely the meaning is reached: up to a row with finitely many
-- before it, every deep enough approximant agrees with it (`reached`).
module denotation.Laws.Truthful where

open import Data.List using (List; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs)
open import denotation.Position using (Pos; instant)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (Ev; EmissionSet; DenEnv; Few; _≼_; enter; approx; ⟦_⟧)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (AgreeTo; upto; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Count using (ag-cnt)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; ⊑-refl)
open import denotation.Laws using (from)

-- `x` opens its instant: no row of it lies before.
Opens : ∀ {A} → EmissionSet A → Pos → Set
Opens t x = ∀ {k e} → t k e → instant k ≡ instant x → x ≼ k

-- Finitely many rows in all.
Finite : ∀ {A} → EmissionSet A → Set
Finite t = Σ (List Pos) λ ks → ∀ {k e} → t k e → k ∈ ks

-- Finitely many before, under an agreement: the same ones.
few-ag : ∀ {A Q} {t t′ : EmissionSet A} {q} → AgreeTo Q t t′ → q ≼ Q → Few t q → Few t′ q
few-ag {Q = Q} {q = q} ag qQ (ks , h) = ks , λ {k} x kq → h (proj₂ (upto ag {k} (≺→≼ {k} {Q} (≺-≼-≺ {k} {q} {Q} kq qQ))) x) kq

-- THE MEANING IS REACHED: up to a row with finitely many before it, every
-- approximant past their count agrees with the meaning.
reached : ∀ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p
        → ∀ {q} → Few (enter (⟦ o ⟧ ρ) p) q
        → Σ ℕ λ N → ∀ m → N ≤ m → AgreeTo q (enter (⟦ o ⟧ ρ) p) (enter (approx m o ρ) p)
reached o ρ g p ok {q} (ks , h) =
  length ks , λ m le → ag-cnt (from m o ρ g p ok) q (inj₁ (ks , le , λ x kq → inj₂ (Any.map (λ { refl → ⊑-refl _ }) (h x kq))))

-- NEVER A LIE, at a row shown or an instant's first.
-- FINITE, THE MEANING: an approximant with finitely many rows met no cut.
postulate
  never-lies : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p
             → ∀ {x} → Few (enter (approx n o ρ) p) x
             → Opens (enter (approx n o ρ) p) x ⊎ Σ (Ev A) (λ e → enter (approx n o ρ) p x e × Visible e)
             → AgreeTo x (enter (approx n o ρ) p) (enter (⟦ o ⟧ ρ) p)
  finite-true : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p
              → Finite (enter (approx n o ρ) p)
              → ∀ {y e} → (enter (approx n o ρ) p y e → enter (⟦ o ⟧ ρ) p y e) × (enter (⟦ o ⟧ ρ) p y e → enter (approx n o ρ) p y e)
