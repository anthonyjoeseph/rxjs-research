-- OCCURRENCES PROBE (2026-08-06).  Rehearsal for
-- Verify-Budget-Sufficient.Occurrences — defines the two predicates
-- frameOccs? / pathOccs? and states the two structural postulates
-- (subΘTm-occs-le and occsᵗ≤sizeᵗ) that justify threading
-- pathOccs? sz path ≡ true into the demand postulates of Anchor-Dry.
--
-- CLASS: LANDING: Verify-Budget-Sufficient/Occurrences.agda
-- (this file IS the content; its module name just changes on landing)
--
-- STRUCTURAL FACT (Exp.agda:254-257, 266-270):
-- subΘExp for mapᵉ/scanᵉ pushes the input type into Θloc BEFORE
-- descending; subΘTm on varᵗ x leaves it unchanged (inj₁, local) or
-- replaces it with a CLOSED term whose occsᵗ = 0 (inj₂).  Therefore
-- occsᵗ (subΘTm Θloc σ tm) ≤ occsᵗ tm — non-increasing.  Combined
-- with occsᵗ tm ≤ sizeᵗ tm (postulate (b)), every function fn whose
-- original occurrence count is bounded by sizeᵉ e (structural subterm
-- argument) satisfies pathOccs? (sizeᵉ e + slotsSize sl) path ≡ true
-- even after Θ-substitution.
--
-- WHY A PROBE.  The definitions below import only Rx.Exp and
-- Rx.Evaluator (both cached); no Measures, no heavy SCC.  Iterating
-- here costs seconds, not minutes.  Land only green bodies.
module Occurrences-Probe where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat  using (ℕ; _≤ᵇ_; _≤_)
open import Data.List using (List; []; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ty; Ctx; Tm; Fn; Val; occsᵗ; sizeᵗ; subΘTm)
open import Rx.Evaluator
  using (Frame; Path; AllOp; NodeId;
         map-f; scan-f; take-f; from-inner; thru-outer;
         root; share-sink; _↠_)

------------------------------------------------------------------
-- § 1  THE TWO PREDICATES
------------------------------------------------------------------

-- Does every function stored in a Frame have ≤ k occurrences of any
-- Θ-variable?  (Only map-f and scan-f carry functions; other frame
-- shapes contribute no copy-fanout.)
frameOccs? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameOccs? k (map-f fn)           = occsᵗ fn ≤ᵇ k
frameOccs? k (scan-f fn _)        = occsᵗ fn ≤ᵇ k
frameOccs? _ (take-f _)           = true
frameOccs? _ (from-inner _ _ _)   = true
frameOccs? _ (thru-outer _ _)     = true

-- All frames in a path satisfy frameOccs? k.
pathOccs? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathOccs? _ root           = true
pathOccs? _ (share-sink _) = true
pathOccs? k (f ↠ p)        = frameOccs? k f ∧ pathOccs? k p

------------------------------------------------------------------
-- § 2  THE TWO STRUCTURAL POSTULATES
--
-- POSTULATE (b) — BOUND.  The occurrence count of any term is at most
-- its syntactic size.  Provable by mutual structural induction
-- mirroring occsᵗ/occsᵉ/occsᵗˢ; here kept as a postulate until a
-- consumer chain is in place (the proof is a one-liner via
-- Measures' occs≤syncᵗ and syncSize≤sizeᵗ).
-- CONSUMER: will be pathOccs?-from-pathB? once that lands.
postulate
  occsᵗ≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t)
    → occsᵗ tm ≤ sizeᵗ tm

-- POSTULATE (a) — SUBSTITUTION INVARIANCE.  Substituting outer Θ
-- variables by closed terms (Exp.agda:266-270) does not increase the
-- occurrence count: local (inj₁) leaves the var unchanged; non-local
-- (inj₂) replaces it with a closed term whose Θ is empty (zero occs).
-- CONSUMER: Caps-Bridge.agda once the demand call sites are updated.
postulate
  subΘTm-occs-le : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t}
    (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)
    → occsᵗ (subΘTm Θloc σ tm) ≤ occsᵗ tm

------------------------------------------------------------------
-- § 3  SANITY: pathOccs? is structurally correct
--
-- Verify that for a one-frame path the unfolding is definitional.
-- map-f unfolds to ≤ᵇ-check ∧ pathOccs? on the tail.
-- take-f / from-inner / thru-outer frames contribute nothing.
------------------------------------------------------------------

-- map-f frame: expands to the ≤ᵇ check ∧ tail
_ : ∀ {n} {Γ : Ctx n} {s u} (k : ℕ)
      (fn : Fn Γ [] [] [] s u) →
    pathOccs? k (map-f fn ↠ root) ≡ ((occsᵗ fn ≤ᵇ k) ∧ true)
_ = λ k fn → refl

-- take-f frame: always true regardless of k
_ : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (nid : NodeId) →
    pathOccs? k (take-f {Γ = Γ} {s = s} nid ↠ root) ≡ true
_ = λ k nid → refl
