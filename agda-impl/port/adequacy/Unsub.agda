{-# OPTIONS --guardedness #-}

-- A SILENT RUN: the machine's own silent steps, from one configuration
-- to another, at whatever ticks.
module port.adequacy.Unsub where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import port.operation.PureObservable using (module Driver; module Machine)

module Unsubbing (R : Set) where
  open Driver R using (step; silent)
  open Machine using (Conf)

  data _⇝_ (m : Conf R) : Conf R → Set₁ where
    now  : m ⇝ m
    then : ∀ {t m₁ m′} → step m ≡ silent t m₁ → m₁ ⇝ m′ → m ⇝ m′

  ⇝-trans : ∀ {m₁ m₂ m₃} → m₁ ⇝ m₂ → m₂ ⇝ m₃ → m₁ ⇝ m₃
  ⇝-trans now          q = q
  ⇝-trans (then e p) q = then e (⇝-trans p q)
