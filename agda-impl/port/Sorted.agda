{-# OPTIONS --guardedness #-}

-- SORTEDNESS: the machine shows the root its values at positions that
-- never fall.  A fact about the machine alone; no meaning is consulted.
-- What is claimed is a rising run (`Rising`), and a rising run's record,
-- read to any step and any tick, ascends.
module port.Sorted where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (suc; _<ᵇ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Pos; _<ᵖ_; <ᵖ-trans; <ᵖ-below)
open import operation.PureObservable using (module Driver)

------------------------------------------------------------------------
-- The order, reflexive

_≤ᵖ_ : Pos → Pos → Set
p ≤ᵖ q = p ≡ q ⊎ p <ᵖ q ≡ true

≤ᵖ-trans : ∀ {p q r} → p ≤ᵖ q → q ≤ᵖ r → p ≤ᵖ r
≤ᵖ-trans (inj₁ refl) h           = h
≤ᵖ-trans h           (inj₁ refl) = h
≤ᵖ-trans {p} {q} {r} (inj₂ a) (inj₂ b) = inj₂ (<ᵖ-trans p q r a b)

-- A child comes after its parent.
≤ᵖ-child : ∀ q {l lo} → lo ≤ᵖ q → lo ≤ᵖ (q ++ [ l ])
≤ᵖ-child q le = ≤ᵖ-trans le (inj₂ (<ᵖ-below q []))

module Sorting (R : Set) where
  open Driver R using (Mach; Step; silent; value; complete; drained; step; trace; shown; reading; marks)

  ----------------------------------------------------------------------
  -- What is claimed: the root's values at positions that never fall

  mutual
    record Rising (lo : Pos) (m : Mach) : Set₁ where
      coinductive
      field rises : RisingStep lo (step m)

    data RisingStep (lo : Pos) : Step → Set₁ where
      silentʳ   : ∀ {m lo′} → lo ≤ᵖ lo′ → Rising lo′ m → RisingStep lo (silent m)
      valueʳ    : ∀ {t p a m} → lo ≤ᵖ p → Rising p m → RisingStep lo (value t p a m)
      completeʳ : ∀ {p} → lo ≤ᵖ p → RisingStep lo (complete p)
      drainedʳ  : RisingStep lo drained

  data Ascending (lo : Pos) : List Pos → Set where
    []ᵃ  : Ascending lo []
    _∷ᵃ_ : ∀ {p ps} → lo ≤ᵖ p → Ascending p ps → Ascending lo (p ∷ ps)

  ascending-from : ∀ {lo lo′ ps} → lo ≤ᵖ lo′ → Ascending lo′ ps → Ascending lo ps
  ascending-from le []ᵃ        = []ᵃ
  ascending-from le (h ∷ᵃ a)   = ≤ᵖ-trans le h ∷ᵃ a

  -- A rising run's record is ascending, however far it is read: a step
  -- past the horizon cuts the record there, adding nothing.
  mutual
    ascending : ∀ {lo m} → Rising lo m → ∀ n h c → Ascending lo (marks (reading h n c (trace m)))
    ascending r 0       h c = []ᵃ
    ascending r (suc n) h c = ascendingˢ (Rising.rises r) n h c

    ascendingˢ : ∀ {lo s} → RisingStep lo s → ∀ n h c → Ascending lo (marks (reading h (suc n) c (shown s)))
    ascendingˢ (silentʳ {m = m} le r) n h c with h <ᵇ Mach.clock m
    ... | true  = []ᵃ
    ... | false = ascending-from le (ascending r n h _)
    ascendingˢ (valueʳ {t = t} le r)  n h c with h <ᵇ t
    ... | true  = []ᵃ
    ... | false = le ∷ᵃ ascending r n h _
    ascendingˢ (completeʳ le)         n h c = le ∷ᵃ []ᵃ
    ascendingˢ drainedʳ               n h c = []ᵃ
