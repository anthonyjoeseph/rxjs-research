{-# OPTIONS --guardedness #-}

-- THE FRESH LEAF: the one thing an elaborated program needs that the
-- author's leaves do not say, a name no other subscription has.  A
-- `fresh` leaf emits one name when subscribed and completes, so a name
-- per subscription, per emission or per burst is a program around it,
-- shared by every runtime; only what a name IS differs.  The engine
-- reads names through their equality alone.
--
-- IN THE DENOTATION A NAME IS A POSITION: `fresh` emits where it was
-- subscribed, which no other subscription shares.  So a name lies in the
-- instant it was minted in, read off by `instantOf` like any position.
module simultaneous.Leaf where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
import Data.Nat as ℕ
open import Level using (lower)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import denotation.MonotonicList.Events using (Timeline; Pos; Label; Events∞; ix; sub; last; idle)
open import denotation.MonotonicList using (MonotonicList; cold; coldᴰ; ofᴱ)
import denotation.Denote as D
open Events∞

-- The author's leaves, and `fresh`.
data WithFresh (C : Set → Set₁) (N : Set) : Set → Set₁ where
  user  : ∀ {A} → C A → WithFresh C N A
  fresh : WithFresh C N N

-- `of [ p ]`, where `p` is where it is subscribed.
freshᴰ : MonotonicList Pos
freshᴰ = cold λ p → λ where
  .force → ofᴱ p 0 (p ∷ [])
  .cut   → idle

leafᴰ : ∀ {A} → WithFresh Timeline Pos A → MonotonicList A
leafᴰ (user c) = coldᴰ (lower c)
leafᴰ fresh    = freshᴰ

-- An elaborated program's meaning: the same fold, over these leaves.
open D.Over leafᴰ public using () renaming (approx to approxˢ; ⟦_⟧ to ⟦_⟧ˢ)

------------------------------------------------------------------------
-- Positions' equality, the denotation's names' only operation

mutual
  _≟ˡ_ : DecidableEquality Label
  ix m  ≟ˡ ix n  with m ℕ.≟ n
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  sub p ≟ˡ sub q with p ≟ᵖ q
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  last  ≟ˡ last  = yes refl
  ix _  ≟ˡ sub _ = no λ ()
  ix _  ≟ˡ last  = no λ ()
  sub _ ≟ˡ ix _  = no λ ()
  sub _ ≟ˡ last  = no λ ()
  last  ≟ˡ ix _  = no λ ()
  last  ≟ˡ sub _ = no λ ()

  _≟ᵖ_ : DecidableEquality Pos
  []      ≟ᵖ []      = yes refl
  []      ≟ᵖ (_ ∷ _) = no λ ()
  (_ ∷ _) ≟ᵖ []      = no λ ()
  (a ∷ p) ≟ᵖ (b ∷ q) with a ≟ˡ b | p ≟ᵖ q
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }
