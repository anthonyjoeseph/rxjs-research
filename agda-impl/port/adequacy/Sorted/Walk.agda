{-# OPTIONS --guardedness #-}

-- THE WALK: a well configuration rises.  `WellMach` is the machine's
-- invariant, kept by every step (`preserve`) and held at the launch
-- (`begin-well`); a run from a well configuration is a rising one.
module port.adequacy.Sorted.Walk where

open import Data.List using ([])

open import denotation.MonotonicList.Events using (Pos; root)
open import port.operation.PureObservable using (PureObs; module Driver; module Machine)
open import port.adequacy.Sorted using (_≤ᵖ_; module Sorting)

module SortingWalk (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step)
  open Machine using (Conf; load)
  open Sorting R using (Rising; RisingStep; silentʳ; valueʳ; completeʳ; drainedʳ)

  postulate
    -- A configuration well past `lo`, the last position delivered.
    WellMach : Pos → Conf R → Set₁

  -- One step, its next configuration well and never earlier.
  data WellStep (lo : Pos) : Step → Set₁ where
    silentʷ   : ∀ {t m lo′} → lo ≤ᵖ lo′ → WellMach lo′ m → WellStep lo (silent t m)
    valueʷ    : ∀ {t p a m} → lo ≤ᵖ p → WellMach p m → WellStep lo (value t p a m)
    completeʷ : ∀ {p} → lo ≤ᵖ p → WellStep lo (complete p)
    drainedʷ  : WellStep lo drained

  postulate
    -- The machine's fundamental lemma: a well configuration's step keeps
    -- it well, and a value it shows is no earlier than the last.
    preserve : ∀ {lo m} → WellMach lo m → WellStep lo (step m)

    -- The run begins well, the program loaded at the root.
    begin-well : (o : PureObs [] R) → WellMach root (load o)

  mutual
    rising : ∀ {lo m} → WellMach lo m → Rising lo m
    rising w .Rising.rises = risingˢ (preserve w)

    risingˢ : ∀ {lo s} → WellStep lo s → RisingStep lo s
    risingˢ (silentʷ le w)  = silentʳ le (rising w)
    risingˢ (valueʷ le w)   = valueʳ le (rising w)
    risingˢ (completeʷ le)  = completeʳ le
    risingˢ drainedʷ        = drainedʳ

  -- SORTEDNESS: the program's run rises from the root.
  sorted : (o : PureObs [] R) → Rising root (load o)
  sorted o = rising (begin-well o)
