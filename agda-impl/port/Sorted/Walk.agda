{-# OPTIONS --guardedness #-}

-- THE WALK: a well configuration rises.  `WellMach` is the machine's
-- invariant, kept by every step (`preserve`) and held at the launch
-- (`begin-well`); a run from a well configuration is a rising one.
module port.Sorted.Walk where

open import Data.List using ([])

open import denotation.MonotonicList.Events using (Pos; root)
open import operation.PureObservable using (PureObs; module Driver)
open import port.Sorted using (_≤ᵖ_; module Sorting)

module SortingWalk (R : Set) where
  open Driver R using (Mach; Step; silent; value; complete; drained; step; begin)
  open Sorting R using (Rising; RisingStep; silentʳ; valueʳ; completeʳ; drainedʳ)

  postulate
    -- A configuration well past `lo`, the last position delivered.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Sorted/Walk.agda
    WellMach : Pos → Mach → Set₁

  -- One step, its next configuration well and never earlier.
  data WellStep (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {m lo′} → lo ≤ᵖ lo′ → WellMach lo′ m → WellStep lo (silent m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → WellMach p m → WellStep lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → WellStep lo (complete p)
    drainedʷ  : WellStep lo drained

  postulate
    -- The machine's fundamental lemma: a well configuration's step keeps
    -- it well, and a value it shows is no earlier than the last.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Sorted/Walk.agda
    preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)

    -- The run begins well, the program loaded at the root.
    --
    -- OLD BODY: 9ec3e6c62e05857feabffdd65a05929de347e532 agda-impl/adequacy/Sorted/Walk.agda
    begin-well : (o : PureObs [] R) → WellMach root (begin o)

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ le w)  = silentʳ le (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (begin o)
  sorted o = rising (begin-well o)
