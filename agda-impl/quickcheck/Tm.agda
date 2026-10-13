{-# OPTIONS --guardedness #-}

-- FIRST-ORDER FUNCTIONS, for generated programs.  A term in a value
-- context `Θ` denotes an Agda function out of `Vals Θ`; `Code` turns each
-- one into the real function the tree takes.
module quickcheck.Tm where

open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming (_∷_ to _∷ᵛ_)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Data.Unit using (tt)

open import quickcheck.Ty using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; listᵗ; ⟦_⟧ᵀ)

Vals : List Ty → Set
Vals = All ⟦_⟧ᵀ

data Tm (Θ : List Ty) : Ty → Set where
  var   : ∀ {t} → t ∈ Θ → Tm Θ t
  unit  : Tm Θ unitᵗ
  bool  : Bool → Tm Θ boolᵗ
  if    : ∀ {t} → Tm Θ boolᵗ → Tm Θ t → Tm Θ t → Tm Θ t
  nat   : ℕ → Tm Θ natᵗ
  plus  : Tm Θ natᵗ → Tm Θ natᵗ → Tm Θ natᵗ
  less  : Tm Θ natᵗ → Tm Θ natᵗ → Tm Θ boolᵗ
  pair  : ∀ {s t} → Tm Θ s → Tm Θ t → Tm Θ (s ×ᵗ t)
  fst   : ∀ {s t} → Tm Θ (s ×ᵗ t) → Tm Θ s
  snd   : ∀ {s t} → Tm Θ (s ×ᵗ t) → Tm Θ t
  inl   : ∀ {s t} → Tm Θ s → Tm Θ (s +ᵗ t)
  inr   : ∀ {s t} → Tm Θ t → Tm Θ (s +ᵗ t)
  case  : ∀ {s t u} → Tm Θ (s +ᵗ t) → Tm (s ∷ Θ) u → Tm (t ∷ Θ) u → Tm Θ u
  nil   : ∀ {t} → Tm Θ (listᵗ t)
  cons  : ∀ {t} → Tm Θ t → Tm Θ (listᵗ t) → Tm Θ (listᵗ t)

⟦_⟧ᵗ : ∀ {Θ t} → Tm Θ t → Vals Θ → ⟦ t ⟧ᵀ
⟦ var i ⟧ᵗ      θ = lookup θ i
⟦ unit ⟧ᵗ       θ = tt
⟦ bool b ⟧ᵗ     θ = b
⟦ if c a b ⟧ᵗ   θ = if ⟦ c ⟧ᵗ θ then ⟦ a ⟧ᵗ θ else ⟦ b ⟧ᵗ θ
⟦ nat n ⟧ᵗ      θ = n
⟦ plus a b ⟧ᵗ   θ = ⟦ a ⟧ᵗ θ + ⟦ b ⟧ᵗ θ
⟦ less a b ⟧ᵗ   θ = ⟦ a ⟧ᵗ θ <ᵇ ⟦ b ⟧ᵗ θ
⟦ pair a b ⟧ᵗ   θ = ⟦ a ⟧ᵗ θ , ⟦ b ⟧ᵗ θ
⟦ fst p ⟧ᵗ      θ = proj₁ (⟦ p ⟧ᵗ θ)
⟦ snd p ⟧ᵗ      θ = proj₂ (⟦ p ⟧ᵗ θ)
⟦ inl a ⟧ᵗ      θ = inj₁ (⟦ a ⟧ᵗ θ)
⟦ inr b ⟧ᵗ      θ = inj₂ (⟦ b ⟧ᵗ θ)
⟦ case e l r ⟧ᵗ θ = [ (λ a → ⟦ l ⟧ᵗ (a ∷ᵛ θ)) , (λ b → ⟦ r ⟧ᵗ (b ∷ᵛ θ)) ] (⟦ e ⟧ᵗ θ)
⟦ nil ⟧ᵗ        θ = []
⟦ cons a as ⟧ᵗ  θ = ⟦ a ⟧ᵗ θ ∷ ⟦ as ⟧ᵗ θ
