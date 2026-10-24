{-# OPTIONS --guardedness #-}

-- THE RUN'S RE-ENTRY CONFIGURATIONS, against the ghost.  Every other
-- configuration is reached from one of these by its own silent steps, so
-- is related to the ghost by nothing else.
module adequacy.Strong where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList.Events using (root)
import denotation.Unfold as U
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open import adequacy.Sane using (Sane)
open import adequacy.Placed.Order using (Placed)

open Machine using (Conf; load)

module Strongly (R : Set) where
  open Driver R using (step; complete)

  postulate
    -- WHAT A RE-ENTRY CONFIGURATION KEEPS against the ghost.
    -- RECOVERY: git show a8e641fe:agda-impl/adequacy/Strong.agda restores the CPS machine's `Carried` record (flags, depth, leftovers), whose fields are the candidates for this one
    Carried : U.Node [] R → Conf R → Set₁

    -- What a carried configuration holds its ghost to.
    carried-sane : ∀ {g m} → Carried g m → Sane [] g × Placed g []

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST: carried, or the root's
  -- completion about to be shown where the ghost ends.
  data Strong (g : U.Node [] R) (m : Conf R) : Set₁ where
    carried : Carried g m → Strong g m
    closing : ∀ {p} → step m ≡ complete p → U.step g ≡ U.endˢ p → Sane [] g → Placed g [] → Strong g m

  postulate
    -- The launch is a re-entry configuration against the program
    -- subscribed at the root.
    strong-begin : (o : PureObs [] R) → Strong (U.subscribe o root) (load o)
