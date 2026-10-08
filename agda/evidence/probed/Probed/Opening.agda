-- WHAT THE ROOT SUBSCRIBES OPEN WITH AND SEND, outside the stores: the
-- sources and schedules live before anything is subscribed, and the
-- instants an `of`'s emits carry, at concrete programs.
-- TARGET: init-sources @8b0228
-- TARGET: init-sync @75c849
-- TARGET: of-emits @5de96e
module Probed.Opening where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Fin using (zero; suc)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (there)
open import Rx.Prim using (after_,_)
open import SExp.Syntax using (natˢ)
open import Rx.Exp using (natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_)
open import CLI.Unit-Test.Prelude using (Γ₂)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (data~)
open import Simulation.Walk using (init-sources; init-sync; of-emits)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals)

-- LOAD-BEARING: a hot script live before the subscribe, two payloads
-- left on each side; fails if either side drops or reorders one
_ : Confirms (init-sources (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []

-- LOAD-BEARING: one hot script live on each side before the subscribe,
-- at the same ticks; fails if the impl's embedding moved or doubled it
_ : Confirms (init-sync (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = (refl , []) ∷ []

-- LOAD-BEARING: two values at the root, the frame 7 and the `of`'s own
-- source 9 apart; fails if an emit carries the source, or any instant
-- but the frame, or is not subscribe-kind
_ : Confirms (of-emits {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} (natˢ 3 ∷ natˢ 4 ∷ []) (λ x → x) {ρ′ = 7 ∷ᵉ []ᵉ} refl 9)
_ = refl ∷ refl ∷ []

-- LOAD-BEARING: under one value binder, the frame read past the value
-- 5; fails if the frame is read at the binder's slot
_ : Confirms (of-emits {Γ = Γ₂} (κᵖ two-arrivals) {Θ = natᵗ ∷ []} (natˢ 3 ∷ []) (λ x → x) {ρ′ = 5 ∷ᵉ 7 ∷ᵉ []ᵉ} refl 9)
_ = refl ∷ []

-- LOAD-BEARING: at the root, a renaming moving the frame past a value 5
-- it does not own; fails if the frame is read at its unrenamed slot
_ : Confirms (of-emits {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} (natˢ 3 ∷ natˢ 4 ∷ []) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} there {ρ′ = 5 ∷ᵉ 7 ∷ᵉ []ᵉ} refl 9)
_ = refl ∷ refl ∷ []

-- LOAD-BEARING: under one value binder, a renaming moving both the bound
-- value and the frame one slot out; fails if either is read unrenamed
_ : Confirms (of-emits {Γ = Γ₂} (κᵖ two-arrivals) {Θ = natᵗ ∷ []} (natˢ 3 ∷ []) {Θ′ = natᵗ ∷ natᵗ ∷ uniqᵗ ∷ []} there {ρ′ = 8 ∷ᵉ 5 ∷ᵉ 7 ∷ᵉ []ᵉ} refl 9)
_ = refl ∷ []

-- LOAD-BEARING: at the root under a mint's binder, the frame moved past a
-- token 2; fails if the frame is read at the token's slot
_ : Confirms (of-emits {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} (natˢ 3 ∷ natˢ 4 ∷ []) {Θ′ = uniqᵗ ∷ uniqᵗ ∷ []} there {ρ′ = 2 ∷ᵉ 7 ∷ᵉ []ᵉ} refl 9)
_ = refl ∷ refl ∷ []
