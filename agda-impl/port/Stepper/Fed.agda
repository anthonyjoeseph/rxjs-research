{-# OPTIONS --guardedness #-}

-- A FED NODE STAYS PLACED: a node placed reading its sources, fed a
-- running source's step and read past it, is placed.  Likewise a node
-- told a source's end.
module port.Stepper.Fed where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)

import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.MonotonicList.Events using (end)
open import port.Sane using (Mode; runs; Sane)
open import port.Placed.Order using (Placed)
open import port.Env using (Same)
open import port.Stepper.Parts using (Fed)
open import port.Stepper.Past using (_≃_)

postulate
  -- OLD BODY: adequacy.Stepper.Fed
  -- Blocked: everyᴱ-agree, meaning-same, sorted-agree absent from port.Env.
  placed-fed : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) {ρ ρ′ : NEnv Γ}
             → Sane ν c → lookup ν i ≡ runs → Fed q a i ρ ρ′ → Placed c ρ → Placed (U.feed i q a c) ρ′

  -- OLD BODY: adequacy.Stepper.Fed
  -- Blocked: everyᴱ-agree, meaning-same, sorted-agree absent from port.Env.
  placed-shut : ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) {ρ ρ′ : NEnv Γ} → lookup ρ i ≃ end c → Same ρ ρ′
              → Placed n ρ → Placed (U.shut i c n) ρ′
