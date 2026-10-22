{-# OPTIONS --guardedness #-}

-- A SILENT RUN: the machine's own silent steps, from one configuration
-- to another.
module port.Unsub where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import operation.StateTree.Pure using (module Driver)

module Unsubbing (R : Set) where
  open Driver R using (Mach; step; silent)

  data _⇝_ (m : Mach) : Mach → Set₁ where
    now  : m ⇝ m
    then : ∀ {m₁ m′} → step m ≡ silent m₁ → m₁ ⇝ m′ → m ⇝ m′
