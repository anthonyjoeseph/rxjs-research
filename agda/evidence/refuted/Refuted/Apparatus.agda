-- THE REFUTATION TREE'S APPARATUS: the zero environment and the four
-- readings taken against it, which is what every witness here is
-- written in.
--
-- WHY IT IS OUT HERE RATHER THAN IN `src`.  The measure is generic in
-- what a slot reference is worth, and `Refuted.Carried-Derived` is the
-- witness that pricing a reference at nought is NOT the entry
-- invariant's rank -- so `src` states the measure and offers no reading
-- without an environment at all.  The witnesses that killed it still
-- have to STATE it, and a refutation states its target in its own
-- tree: that is the whole reason this module exists, and it is the
-- same locality the claim roots rest on.
--
-- Nothing here is a claim.  Every definition is a specialisation of a
-- measure `src` proves nothing about at this environment, so a reader
-- looking for content should read the witnesses.
module Refuted.Apparatus where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ; depᵛ)

zeroη : ∀ {n} → Fin n → ℕ
zeroη _ = 0

obsDepthᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
obsDepthᵉ = depᵉ zeroη

obsDepthᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
obsDepthᵗ = depᵗ zeroη

obsDepthᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
obsDepthᵗˢ = depᵗˢ zeroη

obsDepthᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
obsDepthᵛ = depᵛ zeroη
