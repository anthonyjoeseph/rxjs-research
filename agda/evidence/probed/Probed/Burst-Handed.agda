-- THE TWO LEAVES OF THE BURST REPORT THAT PRICE A VALUE, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHAT IS NOT.  `data-handed` reads no arithmetic
-- at all: the rank enters `ValOK` only under `obs`, and a data type has
-- none, so the row's content is that the READING agrees with the side
-- condition at a type where it recurses.  Flat at `natᵗ` that is
-- degenerate; at a pair and at a sum it is load-bearing, since either
-- component could carry the head the reading charges for and the row
-- would then be unclosable.  `eval-silent` is the other side of the
-- same reading: a term reading nought wrote no observable, so the
-- predicate holds at every rank — and what could fail it is a TYPE that
-- reaches an observable while the value does not, which is the shape
-- the row below stands at.
--
-- COVERAGE: the data leaf at a flat type, at a product and at a sum, at
-- lists of two so the fold is exercised; the silent leaf at a flat type
-- and at a sum whose other arm is an observable, so the reading has to
-- select on the injection rather than on the type, and at a term
-- reading a data binder.  NOT reached: a data type nested under a sum
-- under a product, and a binder at a compound data type.
--
-- TARGET: data-handed @42a356
-- TARGET: eval-silent @07a37c
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

open import Relation.Binary.PropositionalEquality using (refl)

open import Data.List.Relation.Unary.Any using (here)

open import Rx.Exp using (Ctx; Tm; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; nat̂; inlᵗ; varᵗ)
open import Rx.Obs-Depth.Substitution using ([]ᵈ; _∷ᵈ_)
open import Rx.Evaluator.Burst-Report using (data-handed; eval-silent)

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
-- 2.  THE SILENT LEAF.  A term whose reading is nought carries no
-- observable at all, so the predicate holds at EVERY rank -- the rank
-- nought included, which is the case the strict drop cannot reach.  The
-- second row is the load-bearing one: its TYPE reaches an observable
-- while its value takes the other arm.  The third stands at the binder
-- the statement is open for, where the data hypothesis is what keeps
-- the reading nought.
----------------------------------------------------------------------

row-silent-flat : Confirms
  (eval-silent {Γ = Γ₀} {Θ = []} {τ = 0 , 0 , 0} η₀ []ᵈ (nat̂ 7) []ᵃ refl)
row-silent-flat = tt

t-left : Tm Γ₀ [] [] [] (natᵗ +ᵗ obs natᵗ)
t-left = inlᵗ (nat̂ 3)

row-silent-sum : Confirms
  (eval-silent {Γ = Γ₀} {Θ = []} {τ = 0 , 0 , 0} η₀ []ᵈ t-left []ᵃ refl)
row-silent-sum = tt

t-binder : Tm Γ₀ [] [] (natᵗ ∷ []) natᵗ
t-binder = varᵗ (here refl)

row-silent-binder : Confirms
  (eval-silent {Γ = Γ₀} {Θ = natᵗ ∷ []} {τ = 0 , 0 , 0} η₀ (refl ∷ᵈ []ᵈ)
    t-binder (7 ∷ᵃ []ᵃ) refl)
row-silent-binder = tt
