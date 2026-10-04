-- WHAT THE ROOT SUBSCRIBES OPEN WITH, outside the stores: the sources
-- live before anything is subscribed and the schedules the subscribes
-- leave, at concrete programs.
-- TARGET: init-sources @8b0228
-- TARGET: subscribe-sync @ee8e99
module Probed.Opening where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Simulation.Statement using (subscribe-sync)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (data~)
open import Simulation.Walk using (init-sources)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals; defer-in)

-- LOAD-BEARING: a hot script live before the subscribe, two payloads
-- left on each side; fails if either side drops or reorders one
_ : Confirms (init-sources (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = data~ refl (refl ∷ refl ∷ []) ∷ []

-- LOAD-BEARING: the hot read's share leaves one source live on each
-- side, at the same tick; fails if the impl made a second live
_ : Confirms (subscribe-sync (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = (refl , []) ∷ []

-- a deferred hot read: the hop and the script, both ranked alike

_ : Confirms (subscribe-sync (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in))
_ = (refl , refl ∷ []) ∷ (refl , []) ∷ []
