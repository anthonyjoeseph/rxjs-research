{-# OPTIONS --guardedness #-}

module port.Placed.Trail where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.List using ([_]; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; _<ᵖ_; Tail; Tail∞; pin; idle)
open import port.Placed.Order using (Disjoint; EveryT; Ext)
open import port.Placed.Rising using (AtopT)

open Events∞
open Tail∞

-- A tail's steps in order.
mutual
  SortedTs : Tail → Set
  SortedTs (pin k u) = AtopT k (later u) × SortedT (later u)
  SortedTs idle      = ⊤

  record SortedT (t : Tail) : Set where
    coinductive
    field sortedᵀ : SortedTs t

open SortedT public

sortedT-idle : SortedT idle
sortedᵀ sortedT-idle = tt

-- Neither strictly inside the other.
Apart : Pos → Pos → Set
Apart a b = ¬ Ext a b × ¬ Ext b a

-- A tail's steps never inside one before them.
mutual
  FlatTs : Tail → Set
  FlatTs (pin k u) = EveryT (λ h → ¬ Ext k h) (later u) × FlatT (later u)
  FlatTs idle      = ⊤

  record FlatT (t : Tail) : Set where
    coinductive
    field flatᵀ : FlatTs t

open FlatT public

flatT-idle : FlatT idle
flatᵀ flatT-idle = tt

-- `n` marks the step at `k`: just past it, or just past a mark of it.
data Marks (k : Pos) : Pos → Set where
  shown   : Marks k (k ++ [ ix 0 ])
  reshown : ∀ {n} → Marks k n → Marks k (n ++ [ ix 0 ])

-- What a skip at `n` lets run on: no step before it but one it marks.
Marked : Pos → Pos → Set
Marked n k = k <ᵖ n ≡ false ⊎ Marks k n

-- What a cut leaves running trails the run's next event.
TrailE : ∀ {A} → Events A → Pos → Set
TrailE (out n _ _) k = k <ᵖ n ≡ false × Disjoint n k
TrailE (skip n _)  k = Marked n k
TrailE (end n)     k = n <ᵖ k ≡ true × Disjoint (n ++ [ ix 1 ]) k × ¬ Ext n k
TrailE hush        k = ⊥

mutual
  Trailings : ∀ {A} → Events A → Set
  Trailings (out n _ r) = Trail (force r) (cut r) × EveryT (Disjoint n) (cut r)
  Trailings (skip _ r)  = Trail (force r) (cut r)
  Trailings (end _)     = ⊤
  Trailings hush        = ⊤

  record Trail {A} (x : Events A) (c : Tail) : Set where
    coinductive
    field trail  : SortedT c × EveryT (TrailE x) c × Trailings x
          trailᶠ : FlatT c

open Trail public

Trailing : ∀ {A} → Events∞ A → Set
Trailing r = Trail (force r) (cut r)
