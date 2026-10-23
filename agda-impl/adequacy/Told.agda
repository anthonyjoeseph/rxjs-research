{-# OPTIONS --guardedness #-}

-- WHAT A SHUT TELLS: the joiners of a binder not yet told its end,
-- and where each is told.
module port.Told where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (there)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import port.Sorted using (_≤ᵖ_)
open import denotation.MonotonicList.Events using (Pos; last; _<ᵖ_) renaming (sub to subᴾ)
import denotation.Unfold as U

-- Where a shut at `i` tells a joiner its end, the joiners untold:
-- each one's subscription.
untoldᴶ : ∀ {A B : Set} → Pos → Maybe Pos → Maybe (A ≡ B) → List Pos
untoldᴶ p nothing (just refl) = [ p ]
untoldᴶ p e       m           = []

mutual
  untold : ∀ {Γ A B} → A ∈ᴸ Γ → U.Node Γ B → List Pos
  untold i (U.mapᶜ f n)                 = untold i n
  untold i (U.scanᶜ f z n)              = untold i n
  untold i (U.takeWhileᶜ b p n)         = untold i n
  untold i (U.flatMapᶜ op g o ls qs pl) = untoldᴹ i o ++ untoldᴸ i ls ++ untold i pl
  untold i (U.joinᶜ j p xs e)           = untoldᴶ p e (U.same? i j)
  untold i (U.connectᶜ r b s)           = untold (there i) b ++ untoldˢ i s
  untold i (U.endingᶜ p n)              = untold i n
  untold i (U.restᶜ n)                  = untoldʳ i n
  untold i (U.unionᶜ x y)               = untoldʳ i x ++ untoldʳ i y
  untold i (U.burstingᶜ r t)            = untold i t ++ untoldʳ i t
  untold i (U.underᶜ s b)               = untoldʳ (there i) b
  untold i n                            = []

  -- What a node left as a rest could still tell: a rest steps only
  -- through a running source's burst, so a joiner resting is hushed.
  untoldʳ : ∀ {Γ A B} → A ∈ᴸ Γ → U.Node Γ B → List Pos
  untoldʳ i (U.mapᶜ f n)                 = untoldʳ i n
  untoldʳ i (U.scanᶜ f z n)              = untoldʳ i n
  untoldʳ i (U.takeWhileᶜ b p n)         = untoldʳ i n
  untoldʳ i (U.flatMapᶜ op g o ls qs pl) = untoldʳᴹ i o ++ untoldʳᴸ i ls ++ untoldʳ i pl
  untoldʳ i (U.connectᶜ r b s)           = untoldʳ (there i) b ++ untoldᵇ i s
  untoldʳ i (U.endingᶜ p n)              = untoldʳ i n
  untoldʳ i (U.restᶜ n)                  = untoldʳ i n
  untoldʳ i (U.unionᶜ x y)               = untoldʳ i x ++ untoldʳ i y
  untoldʳ i (U.burstingᶜ r t)            = untold i t ++ untoldʳ i t
  untoldʳ i (U.underᶜ s b)               = untoldʳ (there i) b
  untoldʳ i n                            = []

  untoldʳᴹ : ∀ {Γ A B} → A ∈ᴸ Γ → Maybe (U.Node Γ B) → List Pos
  untoldʳᴹ i nothing  = []
  untoldʳᴹ i (just n) = untoldʳ i n

  untoldʳᴸ : ∀ {Γ A B} → A ∈ᴸ Γ → List (U.Node Γ B) → List Pos
  untoldʳᴸ i []       = []
  untoldʳᴸ i (n ∷ ns) = untoldʳ i n ++ untoldʳᴸ i ns

  -- A rested connect's source, burst: its step and its own rest.
  untoldᵇ : ∀ {Γ A B} → A ∈ᴸ Γ → U.Source Γ B → List Pos
  untoldᵇ i (U.live s)    = untold i s ++ untoldʳ i s
  untoldᵇ i (U.ended e t) = untold i t ++ untoldʳ i t

  untoldᴹ : ∀ {Γ A B} → A ∈ᴸ Γ → Maybe (U.Node Γ B) → List Pos
  untoldᴹ i nothing  = []
  untoldᴹ i (just n) = untold i n

  untoldᴸ : ∀ {Γ A B} → A ∈ᴸ Γ → List (U.Node Γ B) → List Pos
  untoldᴸ i []       = []
  untoldᴸ i (n ∷ ns) = untold i n ++ untoldᴸ i ns

  untoldˢ : ∀ {Γ A B} → A ∈ᴸ Γ → U.Source Γ B → List Pos
  untoldˢ i (U.live s)    = untold i s
  untoldˢ i (U.ended e t) = untold i t

-- Every end a shut at `c` tells comes no sooner than `q`.
Tells : Pos → Pos → List Pos → Set
Tells q c = All (λ p → q ≤ᵖ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]))
