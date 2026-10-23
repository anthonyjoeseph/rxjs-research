{-# OPTIONS --guardedness #-}

-- A SILENT RUN: the machine's own silent steps, from one configuration
-- to another.
module port.Unsub where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import operation.PureObservable using (module Driver)

module Unsubbing (R : Set) where
  open Driver R using (Mach; step; silent)

  data _⇝_ (m : Mach) : Mach → Set₁ where
    now  : m ⇝ m
    then : ∀ {m₁ m′} → step m ≡ silent m₁ → m₁ ⇝ m′ → m ⇝ m′

  ⇝-trans : ∀ {m₁ m₂ m₃} → m₁ ⇝ m₂ → m₂ ⇝ m₃ → m₁ ⇝ m₃
  ⇝-trans now          q = q
  ⇝-trans (then e p) q = then e (⇝-trans p q)
