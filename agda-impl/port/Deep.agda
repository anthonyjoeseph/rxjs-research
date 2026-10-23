{-# OPTIONS --guardedness #-}

-- EVERY NODE IN ORDER, rests and their sources included: `Placed`
-- looks at no node under a rest, a union, a burst or an ended source, so
-- the order a run's rests keep is carried beside it.  A connect is in
-- order as its source's burst is, so every piece of every cut is.
module port.Deep where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import denotation.MonotonicList.Events using (ix; end)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import port.Placed.Order using (Ordered; Reaches; Headed; Sorted; Alienᴱ)

mutual
  Deep : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Deep c ρ = Ordered (U.meaning c ρ) × Deeps c ρ

  Deeps : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Deeps (U.mapᶜ f c)                    ρ = Deep c ρ
  Deeps (U.scanᶜ f z c)                 ρ = Deep c ρ
  Deeps (U.takeWhileᶜ i p c)            ρ = Deep c ρ
  Deeps (U.flatMapᶜ op g o ls qs pl)    ρ = Deepᴹ o ρ × Deepᴸ ls ρ × Deep pl ρ
    × (∀ a x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.flatMapᶜ op g o ls qs pl) ρ) → Deep (g a (x ++ [ ix 1 ])) ρ)
  Deeps (U.connectᶜ r b (U.live s))    ρ = Deep b (U.meaning s ρ ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r s) ρ) × Deep s ρ
  Deeps (U.connectᶜ r b (U.ended c t)) ρ = Deep b (end c ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  Deeps (U.deferᶜ l p ns)               ρ = Headed p × Sorted (U.replay ns ρ) × Alienᴱ p (U.replay ns ρ)
  Deeps (U.endingᶜ p n)                 ρ = Deep n ρ
  Deeps (U.restᶜ n)                     ρ = DeepR n ρ
  Deeps (U.unionᶜ x y)                  ρ = Deep x ρ × Deep y ρ
  Deeps (U.burstingᶜ r t)               ρ = Deep t ρ
  Deeps (U.underᶜ (U.live s) b)         ρ = Deep s ρ × Deep b (U.meaning s ρ ∷ ρ)
  Deeps (U.underᶜ (U.ended c t) b)      ρ = Deep t ρ × Deep b (end c ∷ ρ)
  Deeps _                               ρ = ⊤

  Deepᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Deepᴹ nothing  ρ = ⊤
  Deepᴹ (just c) ρ = Deep c ρ

  Deepᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Deepᴸ []       ρ = ⊤
  Deepᴸ (c ∷ cs) ρ = Deep c ρ × Deepᴸ cs ρ

  -- What a node's rest runs, in order to every depth: the parts its
  -- rest keeps running, never what it would subscribe next.
  DeepR : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  DeepR (U.mapᶜ f c)                    ρ = DeepR c ρ
  DeepR (U.scanᶜ f z c)                 ρ = DeepR c ρ
  DeepR (U.takeWhileᶜ i p c)            ρ = DeepR c ρ
  DeepR (U.flatMapᶜ op g o ls qs pl)    ρ = DeepRᴹ o ρ × DeepRᴸ ls ρ × DeepR pl ρ
  DeepR (U.connectᶜ r b (U.live s))    ρ = DeepR b (U.meaning s ρ ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r s) ρ) × Deep s ρ
  DeepR (U.connectᶜ r b (U.ended c t)) ρ = DeepR b (end c ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  DeepR (U.endingᶜ p n)                 ρ = DeepR n ρ
  DeepR (U.restᶜ n)                     ρ = DeepR n ρ
  DeepR (U.unionᶜ x y)                  ρ = DeepR x ρ × DeepR y ρ
  DeepR (U.burstingᶜ r t)               ρ = Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  DeepR (U.underᶜ (U.live s) b)         ρ = Deep s ρ × DeepR b (U.meaning s ρ ∷ ρ)
  DeepR (U.underᶜ (U.ended c t) b)      ρ = Deep t ρ × DeepR b (end c ∷ ρ)
  DeepR _                               ρ = ⊤

  DeepRᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  DeepRᴹ nothing  ρ = ⊤
  DeepRᴹ (just c) ρ = DeepR c ρ

  DeepRᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  DeepRᴸ []       ρ = ⊤
  DeepRᴸ (c ∷ cs) ρ = DeepR c ρ × DeepRᴸ cs ρ
