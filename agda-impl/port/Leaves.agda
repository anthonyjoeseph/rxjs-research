{-# OPTIONS --guardedness #-}

-- WHAT A REST LEAVES RUNNING, AND WHEN TWO LEAVE ALIKE: the next pin a
-- rest steps to, a rest's shape, and two nodes whose rests run alike at
-- every depth.
module port.Leaves where

open import Data.List using (_∷_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import denotation.MonotonicList using (Agree)
import denotation.Unfold as U
open import port.Deep using (Deep)

-- Two steps alike as rests: the same pin, or none.
data Pinned {Γ} {B C : Set} : U.Step Γ B → U.Step Γ C → Set₁ where
  pinned   : ∀ {k x y} → Pinned (U.skipˢ k x) (U.skipˢ k y)
  unpinned : Pinned U.hushˢ U.hushˢ

-- A rest's shape, all the way down to its rests: it steps as it rests.
data Restful : ∀ {Γ B} → U.Node Γ B → Set₁ where
  rf-idle  : ∀ {Γ B} → Restful (U.idleᶜ {Γ = Γ} {B = B})
  rf-rest  : ∀ {Γ A B} {n : U.Node Γ A} → Restful (U.restᶜ {B = B} n)
  rf-union : ∀ {Γ B} {x y : U.Node Γ B} → Restful x → Restful y → Restful (U.unionᶜ x y)
  rf-burst : ∀ {Γ A B r} {t : U.Node Γ A} → Restful (U.burstingᶜ {B = B} r t)
  rf-under : ∀ {Γ A C B} {s : U.Source Γ A} {b : U.Node (A ∷ Γ) C} → Restful b → Restful (U.underᶜ {B = B} s b)

-- Two nodes leaving alike: what each still runs past an unsubscribe,
-- under every environment the first is in order at, the same at every
-- depth, the second in order when the first is; their rests' next
-- steps pinned alike.
-- `restˢ` and `cutᴺ` are read apart, so the pin is its own field.
record Leaves {Γ A B} (x : U.Node Γ A) (y : U.Node Γ B) : Set₁ where
  constructor leaves
  field agree : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} x) ρ) (U.meaning (U.restᶜ {B = ⊤} y) ρ)
        deep  : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → Deep (U.restᶜ {B = ⊤} y) ρ
        pins  : Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} y)

-- The order read back, from the witness's rest to the node's: a
-- flatMap's part is in order by its whole meaning, which no rest
-- below it holds, so only an ended source's rest carries it.
Back : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Back x y = ∀ (ρ : U.NEnv _) → Deep (U.restᶜ {B = ⊤} y) ρ → Deep (U.restᶜ {B = ⊤} x) ρ

-- Leaving alike both ways.
Twin : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Twin x y = Leaves x y × Back x y
