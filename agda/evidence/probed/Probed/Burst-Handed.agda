-- THE TWO LEAVES OF THE BURST REPORT THAT PRICE A VALUE, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  `data-handed` reads no arithmetic
-- at all: the rank enters `ValOK` only under `obs`, and a data type has
-- none, so the row's content is that the READING agrees with the side
-- condition at a type where it recurses.  Flat at `natᵗ` that is
-- degenerate; at a pair and at a sum it is load-bearing, since either
-- component could carry the head the reading charges for and the row
-- would then be unclosable.  `of-handed` is the opposite: its conclusion
-- is a strict inequality at every element, so a row at a term the
-- premise prices EXACTLY is what a wrong reading fails.
--
-- COVERAGE: the data leaf at a flat type, at a product and at a sum, at
-- a list of two so the fold is exercised; the evaluation leaf at a term
-- carrying an observable, at the tightest rank its own premise admits,
-- and at a list of two whose readings differ so the join is spent.
-- NOT reached: a data type nested under a sum under a product, and any
-- evaluation at a term whose observable is not written by the term
-- itself — that second gap is the whole of what `slot-carries` is for,
-- and it is not instantiable here because no burst reaches this file.
--
-- TARGET: data-handed @42a356
-- TARGET: of-handed @b97e64
module Probed.Burst-Handed where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)

open import Rx.Exp using (Ctx; Tm; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; nat̂; strmᵗ; ofᵉ; emptyᵉ)
open import Rx.Evaluator.Burst-Report using (data-handed; of-handed)

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

----------------------------------------------------------------------
-- 2.  THE EVALUATION LEAF.  A `strmᵗ` evaluates to the expression it
-- wraps, so the value is an observable and the conclusion is a strict
-- comparison of that observable's reading against the rank.  The rank
-- here is the SMALLEST the premise admits, which is what makes the row
-- fail under any reading that prices the term lower than it delivers.
----------------------------------------------------------------------

t-empty : Tm Γ₀ [] [] [] (obs natᵗ)
t-empty = strmᵗ emptyᵉ

t-of : Tm Γ₀ [] [] [] (obs natᵗ)
t-of = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

-- one term, at the rank its own reading forces
row-of-one : Confirms (of-handed {Γ = Γ₀} {U = 0} {r = 1} {sz = 0} η₀
                        (t-of ∷ []) (s≤s z≤n))
row-of-one = s≤s z≤n ∷ᵃ []ᵃ

-- two terms whose readings differ, so the premise is a join and the
-- shallower element is carried by the deeper one's bound
row-of-join : Confirms (of-handed {Γ = Γ₀} {U = 0} {r = 1} {sz = 0} η₀
                         (t-empty ∷ t-of ∷ []) (s≤s z≤n))
row-of-join = s≤s z≤n ∷ᵃ s≤s z≤n ∷ᵃ []ᵃ
