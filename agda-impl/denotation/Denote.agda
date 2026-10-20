{-# OPTIONS --guardedness #-}

-- A PROGRAM TREE'S MEANING: the limit of its approximants, approximant n
-- each node replaced by its `MonotonicList` function, every path through
-- more than n `defer`s cut off at ⊥ᴰ.  So the meaning is compositional by
-- construction, and clairvoyant as `MonotonicList` is: an operator reads
-- its inputs' whole runs.  `folded` pins both, and `Main` imports it, so
-- a stepper put in the fold's place breaks the top line.
module denotation.Denote where

open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (lower)

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline)
open import denotation.MonotonicList using (MonotonicList; coldᴰ; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; emptyᴰ; ofᴰ; mapᴰ; scanᴰ; takeWhileᴰ; flatMapᴰ; deferᴰ; connectᴰ; ⊥ᴰ; lub)

-- A connect in scope means the handle `connectᴰ` passed its body.
DenEnv : List Set → Set₁
DenEnv = All MonotonicList

-- The tree and the library each declare the same policies.
flatOp : T.FlatOp → FlatOp
flatOp (T.mergeᶠ k) = mergeᶠ k
flatOp T.switchᶠ    = switchᶠ
flatOp T.exhaustᶠ   = exhaustᶠ

-- APPROXIMANT n: the meaning with every path of more than n nested
-- `defer`s cut off at ⊥ᴰ — `iterate`, for a tree.  Lexicographic on
-- (n , tree): `defer` drops n, everything else is structural.
mutual
  approx : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
  approx n       (cold c)         ρ = coldᴰ (lower c)
  approx n       empty            ρ = emptyᴰ
  approx n       (of xs)          ρ = ofᴰ xs
  approx n       (map f s)        ρ = mapᴰ f (approx n s ρ)
  approx n       (scan f z s)     ρ = scanᴰ f z (approx n s ρ)
  approx n       (takeWhile i p s) ρ = takeWhileᴰ i p (approx n s ρ)
  approx n       (flatMap op f s) ρ = flatMapᴰ (flatOp op) (λ a → approx n (f a) ρ) (approx n s ρ)
  approx n       (connect s b)    ρ = connectᴰ (approx n s ρ) λ r → approx n b (r ∷ ρ)
  approx n       (connected i)    ρ = lookup ρ i
  approx zero    (defer l)        ρ = ⊥ᴰ
  approx (suc n) (defer l)        ρ = deferᴰ (approx n (Later.force l) ρ)

⟦_⟧[_] : ∀ {Γ A} → Obs Timeline Γ A → ℕ → DenEnv Γ → MonotonicList A
⟦ o ⟧[ n ] = approx n o

-- THE MEANING: the limit of the approximants.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
⟦ o ⟧ ρ = lub λ n → approx n o ρ

-- The meaning is a fold: the limit of approximants, each an operator's
-- `MonotonicList` function applied to its children's approximants.
record Fold : Set₁ where
  field
    limitᶠ     : ∀ {Γ A} (o : Obs Timeline Γ A) ρ → ⟦ o ⟧ ρ ≡ lub (λ n → approx n o ρ)
    mapᶠ       : ∀ {Γ A B} n (f : A → B) (s : Obs Timeline Γ A) ρ → approx n (map f s) ρ ≡ mapᴰ f (approx n s ρ)
    scanᶠ      : ∀ {Γ A B} n (f : B → A → B) z (s : Obs Timeline Γ A) ρ → approx n (scan f z s) ρ ≡ scanᴰ f z (approx n s ρ)
    takeWhileᶠ : ∀ {Γ A} n i p (s : Obs Timeline Γ A) ρ → approx n (takeWhile i p s) ρ ≡ takeWhileᴰ i p (approx n s ρ)
    flatMapᶠ   : ∀ {Γ A B} n op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) ρ
               → approx n (flatMap op f s) ρ ≡ flatMapᴰ (flatOp op) (λ a → approx n (f a) ρ) (approx n s ρ)
    connectᶠ   : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) ρ
               → approx n (connect s b) ρ ≡ connectᴰ (approx n s ρ) (λ r → approx n b (r ∷ ρ))
    connectedᶠ : ∀ {Γ A} n (i : A ∈ Γ) (ρ : DenEnv Γ) → approx n (connected i) ρ ≡ lookup ρ i
    deferᶠ     : ∀ {Γ A} n (l : Later Timeline Γ A) ρ → approx (suc n) (defer l) ρ ≡ deferᴰ (approx n (Later.force l) ρ)

folded : Fold
folded = record
  { limitᶠ     = λ _ _ → refl
  ; mapᶠ       = λ _ _ _ _ → refl
  ; scanᶠ      = λ _ _ _ _ _ → refl
  ; takeWhileᶠ = λ _ _ _ _ _ → refl
  ; flatMapᶠ   = λ _ _ _ _ _ → refl
  ; connectᶠ   = λ _ _ _ _ → refl
  ; connectedᶠ = λ _ _ _ → refl
  ; deferᶠ     = λ _ _ _ → refl
  }
