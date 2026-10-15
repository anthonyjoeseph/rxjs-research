{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A merge respects `≃` only between events
-- in order, so the stepper needs every meaning it merges placed.
module adequacy.Placed where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs)
open import denotation.MonotonicList using (Events; Events∞; Pos; Timeline; out; skip; end; hush; _<ᵖ_; root)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)

open Events∞

-- Nothing in `e` comes before `k`.
Atop : ∀ {A} → Pos → Events A → Set
Atop k (out h _ _) = h <ᵖ k ≡ false
Atop k (skip h _)  = h <ᵖ k ≡ false
Atop k (end h)     = h <ᵖ k ≡ false
Atop k hush        = ⊤

-- Each event at or before the one after it.
mutual
  Orders : ∀ {A} → Events A → Set
  Orders (out k _ r) = Atop k (force r) × Ordered (force r)
  Orders (skip k r)  = Atop k (force r) × Ordered (force r)
  Orders (end _)     = ⊤
  Orders hush        = ⊤

  record Ordered {A} (e : Events A) : Set where
    coinductive
    field ordered : Orders e

open Ordered public

-- A joiner joined before everything its source has yet to show.
Joined : ∀ {A} → Pos → Events A → Set
Joined p (out k _ _) = p <ᵖ k ≡ true
Joined p (skip k _)  = p <ᵖ k ≡ true
Joined p (end _)     = ⊤
Joined p hush        = ⊤

-- Every node's meaning in order, read in its own environment: a
-- connect's body reading its source's, and every joiner still reading
-- its source joined before what the source has yet to show.
mutual
  Placed : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Placed c ρ = Ordered (U.meaning c ρ) × Within c ρ

  Within : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Within (U.mapᶜ f c)               ρ = Placed c ρ
  Within (U.scanᶜ f z c)            ρ = Placed c ρ
  Within (U.takeWhileᶜ i p c)       ρ = Placed c ρ
  Within (U.flatMapᶜ op g o ls qs)  ρ = Placedᴹ o ρ × Placedᴸ ls ρ
  Within (U.connectᶜ b (U.live s))  ρ = Placed b (U.meaning s ρ ∷ᴬ ρ) × Placed s ρ
  Within (U.connectᶜ b (U.ended c)) ρ = Placed b (end c ∷ᴬ ρ)
  Within (U.joinᶜ i p xs nothing)   ρ = Joined p (lookup ρ i)
  Within _                          ρ = ⊤

  Placedᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Placedᴹ nothing  ρ = ⊤
  Placedᴹ (just c) ρ = Placed c ρ

  Placedᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Placedᴸ []       ρ = ⊤
  Placedᴸ (c ∷ cs) ρ = Placed c ρ × Placedᴸ cs ρ

postulate
  -- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root
  -- is placed.
  placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
