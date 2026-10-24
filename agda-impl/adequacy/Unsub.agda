{-# OPTIONS --guardedness #-}

-- A SILENT RUN: the machine's own silent steps, from one configuration
-- to another, at whatever ticks.
module adequacy.Unsub where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import operation.PureObservable using (module Driver; module Machine)

module Unsubbing (R : Set) where
  open Driver R using (step; silent)
  open Machine using (Conf)

  data _⇝_ (m : Conf R) : Conf R → Set₁ where
    now  : m ⇝ m
    then : ∀ {t m₁ m′} → step m ≡ silent t m₁ → m₁ ⇝ m′ → m ⇝ m′

