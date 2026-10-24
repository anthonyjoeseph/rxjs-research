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
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open import adequacy.Sane using (Sane; sane-subscribe)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Placed using (placed-subscribe)

open Machine using (Conf; load)

module Strongly (R : Set) where
  open Driver R using (step; complete)

  postulate
    -- THE ENGINE RUNS ITS GHOST: what the configuration's search finds
    -- next is what the ghost's step shows next, or a silent mark no later.
    -- RECOVERY: git show 85c14392:agda-impl/spike/MarkedHead.agda restores the per-node head agreement (`Head`, `Agrees`, `Quiet`) against the spike's computed ghost, proven by `head-agrees` in `spike/MarkedHead/Agrees.agda` for of / empty / map / merge / connect / joiner / cold
    -- RECOVERY: git show 85c14392:agda-impl/spike/MarkedInv.agda restores the fold invariant (`Wf`, `Base`, `inv-next`) the head agreement read
    -- RECOVERY: git show 3e39632d:agda-impl/adequacy/Deep.agda restores order to every depth of a node (`Deep`, `deep-rest`), and `adequacy/Leaves.agda` and `adequacy/Opens.agda` at that commit a source tied to its leftover and where each subscription opens
    -- RECOVERY: git show 3e39632d:agda-impl/adequacy/Told.agda restores what a shut tells its joiners, and `adequacy/Calm.agda` at that commit what a shut falls back on
    Agrees : U.Node [] R → Conf R → Set₁

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

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST: carried, or the root's
  -- completion about to be shown where the ghost ends.
  data Strong (g : U.Node [] R) (m : Conf R) : Set₁ where
    carried : Carried g m → Strong g m
    closing : ∀ {p} → step m ≡ complete p → U.step g ≡ U.endˢ p → Sane [] g → Placed g [] → Strong g m

  postulate
    -- The launch runs the program subscribed at the root.
    agrees-begin : (o : PureObs [] R) → Agrees (U.subscribe o root) (load o)

  -- The launch is a re-entry configuration against the program
  -- subscribed at the root.
  strong-begin : (o : PureObs [] R) → Strong (U.subscribe o root) (load o)
  strong-begin o = carried record { sane = sane-subscribe o root (λ ()) ; placed = placed-subscribe o ; agrees = agrees-begin o }
