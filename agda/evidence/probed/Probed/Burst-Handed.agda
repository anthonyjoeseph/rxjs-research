-- THE LEAF OF THE BURST REPORT THAT PRICES A DATA VALUE, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  `data-handed` reads no arithmetic
-- at all: the rank enters `ValOK` only under `obs`, and a data type has
-- none, so the row's content is that the READING agrees with the side
-- condition at a type where it recurses.  Flat at `natᵗ` that is
-- degenerate; at a pair and at a sum it is load-bearing, since either
-- component could carry the head the reading charges for and the row
-- would then be unclosable.
--
-- COVERAGE: a flat type, a product and a sum, at lists of two so the
-- fold is exercised.  NOT reached: a data type nested under a sum under
-- a product.
--
-- TARGET: data-handed @42a356
module Probed.Burst-Handed where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)

open import Rx.Exp using (Ctx; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_)
open import Rx.Evaluator.Burst-Report using (data-handed)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

η₀ : Fin 0 → ℕ
η₀ ()

----------------------------------------------------------------------
-- 1.  THE DATA LEAF.  Each row is the target applied at a type and a
-- list of values of that type, so the type is generated from the
-- statement and the probe chooses only the point.
----------------------------------------------------------------------

-- flat: degenerate, and it is here to say the premise is inhabited
row-data-flat : Confirms (data-handed {Γ = Γ₀} {u = natᵗ} η₀ (0 , 0 , 0)
                           (3 ∷ 5 ∷ []) tt)
row-data-flat = tt ∷ᵃ tt ∷ᵃ []ᵃ

-- a product, where the reading recurses into both components
row-data-pair : Confirms (data-handed {Γ = Γ₀} {u = natᵗ ×ᵗ boolᵗ} η₀ (0 , 0 , 0)
                           ((3 , true) ∷ []) tt)
row-data-pair = (tt , tt) ∷ᵃ []ᵃ

-- a sum, where it selects on the injection
row-data-sum : Confirms (data-handed {Γ = Γ₀} {u = natᵗ +ᵗ boolᵗ} η₀ (0 , 0 , 0)
                          (inj₁ 3 ∷ inj₂ false ∷ []) tt)
row-data-sum = tt ∷ᵃ tt ∷ᵃ []ᵃ
