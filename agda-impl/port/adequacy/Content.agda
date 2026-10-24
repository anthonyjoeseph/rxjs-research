{-# OPTIONS --guardedness #-}

-- CONTENT: the root's record is the meaning's events, as a set.
-- Sortedness (`port.adequacy.Sorted`) says nothing of WHAT arrives; this
-- says nothing of the ORDER, so neither proof reads the other.
module port.adequacy.Content where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ)

open import denotation.MonotonicList.Events using (root)
open import denotation.MonotonicList using (observe)
open import denotation.Denote using (⟦_⟧)
open import port.operation.PureObservable using (PureObs; module Driver; module Machine)
open import adequacy.Ghost using (module Ghosting)

module Honesty (R : Set) where
  open Driver R using (reading; Read)
  open Machine using (load)
  open Ghosting R using (Alike)

  postulate
    -- CONTENT: every prefix's record alike the meaning's events as a set.
    --
    -- OLD BODY: 85c14392490061b71342d104b2d16a16cb4ec724 agda-impl/adequacy/Content.agda
    content : (o : PureObs [] R) (n h : ℕ) → let x = reading h n 0 (load o) in Alike (Read.endedAs x) (Read.marks x) (Read.log x) (observe (⟦ o ⟧ []) root)
