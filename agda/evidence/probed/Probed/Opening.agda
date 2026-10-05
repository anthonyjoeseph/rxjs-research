-- WHAT THE ROOT SUBSCRIBES OPEN WITH AND SEND, outside the stores: the
-- sources and schedules live before anything is subscribed, and the
-- instants of what the subscribes send, at concrete programs.
-- TARGET: init-sources @8b0228
-- TARGET: init-sync @75c849
-- TARGET: subscribe-stamps @57c779
module Probed.Opening where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Fin using (zero; suc)
open import Data.Nat using (z≤n; _<?_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Rx.Prim using (hot; after_,_)
open import SExp.Syntax using (ofˢ; natˢ; emptyˢ)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Simulation.Statement using (subscribe-stamps)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (data~)
open import Simulation.Walk using (init-sources; init-sync)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals)

-- LOAD-BEARING: a hot script live before the subscribe, two payloads
-- left on each side; fails if either side drops or reorders one
_ : Confirms (init-sources (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []

-- LOAD-BEARING: one hot script live on each side before the subscribe,
-- at the same ticks; fails if the impl's embedding moved or doubled it
_ : Confirms (init-sync (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = (refl , []) ∷ []

-- LOAD-BEARING: an `of` sends at subscribe, so the list is not empty and
-- `OneIn` is not ⊤; fails if the value's instant is not below the clock
-- the subscribe leaves
of-one : Point
of-one = record { d₀ = hot ((after 1 , 5) ∷ []) ; prog = ofˢ (natˢ 3 ∷ []) ; d₁ = emptyˢ }

_ : Confirms (subscribe-stamps (κᵖ of-one) (Point.prog of-one) (insᵖ of-one))
_ = z≤n , toWitness {a? = _ <? _} tt , []

-- LOAD-BEARING: two values sent by one subscribe; fails if the second
-- carries an instant of its own
of-two : Point
of-two = record { d₀ = hot ((after 1 , 5) ∷ []) ; prog = ofˢ (natˢ 3 ∷ natˢ 4 ∷ []) ; d₁ = emptyˢ }

_ : Confirms (subscribe-stamps (κᵖ of-two) (Point.prog of-two) (insᵖ of-two))
_ = z≤n , toWitness {a? = _ <? _} tt , refl ∷ []
