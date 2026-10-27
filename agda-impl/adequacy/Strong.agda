{-# OPTIONS --guardedness #-}

-- THE RUN'S RE-ENTRY CONFIGURATIONS, against the ghost.  Every other
-- configuration is reached from one of these by its own silent steps, so
-- is related to the ghost by nothing else.
module adequacy.Strong where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList.Events using (root)
import denotation.Unfold as U
open import operation.PureObservable using (PureObs; module Machine)
open import adequacy.Sane using (Sane; sane-subscribe)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Placed using (placed-subscribe)
open import adequacy.Engine.Meaning using (M; _≅_; ≅-refl)
open import adequacy.Engine.Inv using (Inv; inv-load)
open import adequacy.Record using (Ahead)

open Machine using (Conf; load)

module Strongly (R : Set) where
  -- THE ENGINE RUNS ITS GHOST: the configuration keeps the engine's
  -- invariant, and means, as a set, what the ghost has left to show;
  -- and whatever items the ghost's meaning reaches, so does its own.
  -- A set does not see a silence: a ghost showing nothing agrees as one
  -- with a cold stalling forever.
  record Agrees (g : U.Node [] R) (m : Conf R) : Set₁ where
    field
      inv   : Inv m
      same  : U.meaning g [] ≅ M m
      ahead : ∀ {k} → Ahead (U.meaning g []) k → Ahead (M m) k

  -- THE GHOST COMES TO `s` by none or more of its own skips.
  data Leads : U.Node [] R → U.Step [] R → Set₁ where
    shown : ∀ {g s} → U.step g ≡ s → Leads g s
    skips : ∀ {g g₁ k s} → U.step g ≡ U.skipˢ k g₁ → Leads g₁ s → Leads g s

  -- WHAT A RE-ENTRY CONFIGURATION KEEPS against the ghost: the stepper's
  -- own invariants, and that the engine runs it.
  record Carried (g : U.Node [] R) (m : Conf R) : Set₁ where
    field
      sane   : Sane [] g
      placed : Placed g []
      agrees : Agrees g m

  -- What a carried configuration holds its ghost to.
  carried-sane : ∀ {g m} → Carried g m → Sane [] g × Placed g []
  carried-sane cr = Carried.sane cr , Carried.placed cr

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST.
  data Strong (g : U.Node [] R) (m : Conf R) : Set₁ where
    carried : Carried g m → Strong g m

  -- The launch runs the program subscribed at the root.
  agrees-begin : (o : PureObs [] R) → Agrees (U.subscribe o root) (load o)
  agrees-begin o = record { inv = inv-load o ; same = ≅-refl ; ahead = λ a → a }

  -- The launch is a re-entry configuration against the program
  -- subscribed at the root.
  strong-begin : (o : PureObs [] R) → Strong (U.subscribe o root) (load o)
  strong-begin o = carried record { sane = sane-subscribe o root (λ ()) ; placed = placed-subscribe o ; agrees = agrees-begin o }
