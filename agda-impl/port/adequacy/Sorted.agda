{-# OPTIONS --guardedness #-}

-- SORTEDNESS: the machine shows the root its values at positions that
-- never fall.  A fact about the machine alone; no meaning is consulted.
-- What is claimed is a rising run (`Rising`), and a rising run's record,
-- read to any step and any tick, ascends.
module port.adequacy.Sorted where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc; _<ᵇ_)

open import denotation.MonotonicList.Events using (Pos)
open import port.operation.PureObservable using (module Driver; module Machine)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-trans)

module Sorting (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step; reading; Read)
  open Machine using (Conf)

  ----------------------------------------------------------------------
  -- What is claimed: the root's values at positions that never fall

  mutual
    record Rising (lo : Pos) (m : Conf R) : Set₁ where
      coinductive
      field rises : RisingStep lo (step m)

    data RisingStep (lo : Pos) : Step → Set₁ where
      silentʳ   : ∀ {t m lo′} → lo ≤ᵖ lo′ → Rising lo′ m → RisingStep lo (silent t m)
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
  ascending : ∀ {lo m} → Rising lo m → ∀ n h c → Ascending lo (Read.marks (reading h n c m))
  ascending r zero h c = []ᵃ
  ascending {m = m} r (suc n) h c with step m | Rising.rises r
  ... | silent t k | silentʳ le r′ with h <ᵇ t
  ...   | true  = []ᵃ
  ...   | false = ascending-from le (ascending r′ n h _)
  ascending r (suc n) h c | value t p a k | valueʳ le r′ with h <ᵇ t
  ...   | true  = []ᵃ
  ...   | false = le ∷ᵃ ascending r′ n h t
  ascending r (suc n) h c | complete p | completeʳ le = le ∷ᵃ []ᵃ
  ascending r (suc n) h c | drained    | drainedʳ     = []ᵃ
