-- AN UNROLLING AS AN AUTHOR'S PROGRAM, at two μ-bodies: the witness
-- written by hand, both equations by `refl`, the elaborated one at an
-- ABSTRACT renaming.
-- TARGET: μ-unfolds @adc7ea
module Probed.Unfold where

open import Data.List using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Fin using (zero)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import Rx.Exp using (natᵗ; mergeᶠ)
open import SExp.Syntax using (SExp; inputˢ; emptyˢ; mapˢ; scanˢ; takeWhileˢ; fstˢ; boolˢ; flattenˢ; μˢ; varˢ; varˢᵗ; deferˢ; pairˢ; inlˢ; inrˢ; unitˢ; strmˢ)

open import Simulation.Walk using (μ-unfolds)
open import CLI.Unit-Test.Prelude using (Γ₂)
open import Probed.Apparatus using (Confirms; κᵖ; two-arrivals)

-- the μ-var read straight under the defer, no value binder between
loop : ∀ {Θ} → SExp Γ₂ (natᵗ ∷ []) [] Θ natᵗ
loop = deferˢ (varˢ (here refl))

-- a lane per arrival of slot zero, each lane the whole program again:
-- the μ-var under a defer under the map's value binder
lanes : ∀ {Θ} → SExp Γ₂ (natᵗ ∷ []) [] Θ natᵗ
lanes = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (strmˢ (deferˢ (varˢ (here refl)))))) (inputˢ zero))

-- DEGENERATE in the binder: fails if the defer's context transport or
-- the elaborated hop's wrapper does not commute with the substitution
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} loop)
_ = deferˢ (μˢ loop) , refl , λ w → refl

-- LOAD-BEARING: fails if the inserted μ's frame term, elaborated under
-- the map's binder, is not the outer frame weakened past it
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} lanes)
_ = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (strmˢ (deferˢ (μˢ lanes))))) (inputˢ zero))
  , refl , λ w → refl

-- a lane per arrival of slot zero, each lane the whole program again,
-- built as a scan's accumulator: the μ-var under a defer under the
-- scan step's binder
scanned : ∀ {Θ} → SExp Γ₂ (natᵗ ∷ []) [] Θ natᵗ
scanned = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (varˢᵗ (here refl))))
            (scanˢ (strmˢ (deferˢ (varˢ (here refl)))) (strmˢ emptyˢ) (inputˢ zero)))

-- LOAD-BEARING: fails if the inserted μ's frame term, elaborated under
-- the scan step's binder, is not the outer frame weakened past it
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} scanned)
_ = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (varˢᵗ (here refl))))
      (scanˢ (strmˢ (deferˢ (μˢ scanned))) (strmˢ emptyˢ) (inputˢ zero)))
  , refl , λ w → refl

-- LOAD-BEARING: fails if the frame term reads a nonempty outer
-- telescope the unrolling's weakening moved
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = natᵗ ∷ []} lanes)
_ = flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (strmˢ (deferˢ (μˢ lanes))))) (inputˢ zero))
  , refl , λ w → refl

-- the μ-var under a defer inside a test's predicate, under its binder
tested : ∀ {Θ} → SExp Γ₂ (natᵗ ∷ []) [] Θ natᵗ
tested = takeWhileˢ (fstˢ (pairˢ (boolˢ true) (strmˢ (deferˢ (varˢ (here refl)))))) (inputˢ zero)

-- LOAD-BEARING: fails if the inserted μ's frame term, elaborated under
-- the test's binder, is not the outer frame weakened past it
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} tested)
_ = takeWhileˢ (fstˢ (pairˢ (boolˢ true) (strmˢ (deferˢ (μˢ tested))))) (inputˢ zero) , refl , λ w → refl

-- a μ inside a μ, the inner's defer reading the OUTER var
nested : ∀ {Δ Θ} → SExp Γ₂ (natᵗ ∷ []) Δ Θ natᵗ
nested = μˢ (deferˢ (varˢ (there (here refl))))

-- LOAD-BEARING: fails if the substitution does not reach past the
-- inner μ's binder
_ : Confirms (μ-unfolds {Γ = Γ₂} (κᵖ two-arrivals) {Θ = []} (nested {Δ = []}))
_ = μˢ (deferˢ (μˢ nested)) , refl , λ w → refl
