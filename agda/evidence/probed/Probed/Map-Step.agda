-- THE ELABORATED MAP STEP AGAINST THE PLAIN MAP, at one emit: the
-- payloads mapped one for one and the stamp kept.
-- TARGET: lifts-map @9f48b2
module Probed.Map-Step where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import Rx.Exp using (add; natᵗ; uniqᵗ; []ᵉ; _∷ᵉ_)
open import SExp.Syntax using (primˢ; pairˢ; varˢᵗ; natˢ)

open import Simulation.Walk using (lifts-map)
open import CLI.Unit-Test.Prelude using (Γ₂)
open import Probed.Apparatus using (Confirms; κᵖ; two-arrivals)

-- LOAD-BEARING: `x + 1` over an emit opening with an `init`, then two
-- payloads; fails if the step counts the frame event as a payload,
-- maps a payload twice, or moves the instant or the kind
_ : Confirms (lifts-map {Γ = Γ₂} (κᵖ two-arrivals) (primˢ add (pairˢ (varˢᵗ (here refl)) (natˢ 1))) {Θ′ = uniqᵗ ∷ []} (λ x → x)
                        {ρ′ = 0 ∷ᵉ []ᵉ} {ρ = []ᵉ} (λ ())
                        (inj₁ 9 ∷ inj₂ (inj₁ 3) ∷ inj₂ (inj₁ 4) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                        (3 ∷ 4 ∷ []) (refl ∷ refl ∷ []))
_ = (refl ∷ refl ∷ []) , refl

-- LOAD-BEARING: the payload plus the author's variable, past the mint's
-- binder; fails if the step reads the variable at the slot the binder
-- took, so each payload would gain the mint's source instead
_ : Confirms (lifts-map {Γ = Γ₂} (κᵖ two-arrivals) (primˢ add (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl)))))
                        {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                        {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl })
                        (inj₁ 9 ∷ inj₂ (inj₁ 3) ∷ inj₂ (inj₁ 5) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                        (3 ∷ 5 ∷ []) (refl ∷ refl ∷ []))
_ = (refl ∷ refl ∷ []) , refl

-- LOAD-BEARING: the same step at a renaming that moves the author's
-- variable one slot down, past a value it does not bind; fails if the
-- step reads the slot the variable had before the renaming
_ : Confirms (lifts-map {Γ = Γ₂} (κᵖ two-arrivals) (primˢ add (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl)))))
                        {Θ′ = natᵗ ∷ natᵗ ∷ uniqᵗ ∷ []} there
                        {ρ′ = 8 ∷ᵉ 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl })
                        (inj₁ 9 ∷ inj₂ (inj₁ 3) ∷ inj₂ (inj₁ 5) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                        (3 ∷ 5 ∷ []) (refl ∷ refl ∷ []))
_ = (refl ∷ refl ∷ []) , refl

-- LOAD-BEARING: the same step under a mint's binder, the renaming moving
-- the author's variable past a token 2; fails if the step reads the token
_ : Confirms (lifts-map {Γ = Γ₂} (κᵖ two-arrivals) (primˢ add (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl)))))
                        {Θ′ = uniqᵗ ∷ natᵗ ∷ uniqᵗ ∷ []} there
                        {ρ′ = 2 ∷ᵉ 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl })
                        (inj₁ 9 ∷ inj₂ (inj₁ 3) ∷ inj₂ (inj₁ 5) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                        (3 ∷ 5 ∷ []) (refl ∷ refl ∷ []))
_ = (refl ∷ refl ∷ []) , refl
