------------------------------------------------------------------
-- OCCURRENCES: occurrence-count predicates for Frames and Paths,
-- and two structural postulates that justify threading the predicate
-- into the demand hypotheses of Anchor-Dry.agda.
--
-- STRUCTURAL FACT (Exp.agda:254-257, 266-270):
-- subΘExp for mapᵉ/scanᵉ pushes the input type into Θloc BEFORE
-- descending into the body.  subΘTm on varᵗ x then does
--   ∈-++⁻ Θloc x:
--     inj₁ y → varᵗ y   (local, occurrence count unchanged)
--     inj₂ z → wkTm (reify (lookupEnv σ z))
--              (closed term from the environment; occsᵗ = 0)
-- Therefore occsᵗ (subΘTm Θloc σ tm) ≤ occsᵗ tm — non-increasing
-- under outer Θ-substitution.  Combined with occsᵗ tm ≤ sizeᵗ tm
-- (POSTULATE (b) below, one-liner proof deferred until a consumer
-- chain is in place), every function fn whose original occurrence
-- count is bounded by sizeᵉ e (structural subterm argument) satisfies
-- pathOccs? (sizeᵉ e + slotsSize sl) path ≡ true even after the
-- Θ-substitution that evaluating mapᵉ/scanᵉ performs.
--
-- WIRING.
--   frameOccs?         consumed by pathOccs?  (§ 1)
--   pathOccs?          consumed by chainStep-demand, foldPath-demand,
--                      subscribeInner-demand and their dry wrappers
--                      (Anchor-Dry.agda § 1–2)
--   occsᵗ≤sizeᵗ        POSTULATE — zero consumers until
--                      pathOccs?-from-pathB? is added with a consumer
--   subΘTm-occs-le     POSTULATE — future consumer Caps-Bridge.agda
--
-- CONSUMER NOTE for Anchor-Dry.agda callers (Caps-Bridge.agda):
--   The new hypothesis pathOccs? sz path ≡ true
--   (with sz = sizeᵉ e + slotsSize sl) must be supplied by the
--   caller; it cannot be derived from pathB? B Ψ path ≡ true alone
--   (the direction B ≥ sz makes pathB?'s bound weaker for pathOccs?).
--   The structural argument is: functions in a registered path are
--   subterms of the original program, so sizeᵗ fn ≤ sizeᵉ e ≤ sz,
--   and subΘTm-occs-le then gives occsᵗ fn (after substitution) ≤ sz.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Occurrences where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat  using (ℕ; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp
  using (Ty; Ctx; Tm; Fn; occsᵗ; sizeᵗ)
open import Rx.Evaluator
  using (Frame; Path; AllOp; NodeId;
         map-f; scan-f; take-f; from-inner; thru-outer;
         root; share-sink; _↠_)

------------------------------------------------------------------
-- § 1  THE TWO PREDICATES
--
-- frameOccs? k f: true iff every function stored in f has ≤ k
-- occurrences of any Θ-variable.  Only map-f and scan-f carry
-- functions; the other frame shapes contribute no copy-fanout so
-- they vacuously satisfy any bound.
--
-- pathOccs? k p: all frames in p satisfy frameOccs? k.
------------------------------------------------------------------

frameOccs? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameOccs? k (map-f fn)           = occsᵗ fn ≤ᵇ k
frameOccs? k (scan-f fn _)        = occsᵗ fn ≤ᵇ k
frameOccs? _ (take-f _)           = true
frameOccs? _ (from-inner _ _ _)   = true
frameOccs? _ (thru-outer _ _)     = true

pathOccs? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathOccs? _ root           = true
pathOccs? _ (share-sink _) = true
pathOccs? k (f ↠ p)        = frameOccs? k f ∧ pathOccs? k p

-- § 2  DEFERRED STRUCTURAL POSTULATES
--
-- The two postulates stated in the probe (Occurrences-Probe.agda) are
-- held back from this src module until their consumer chain is ready:
--
--   occsᵗ≤sizeᵗ : ∀ ... tm → occsᵗ tm ≤ sizeᵗ tm
--     Proof: one-liner via Measures' occs≤syncᵗ and syncSize≤sizeᵗ.
--     Consumer: pathOccs?-from-pathB? (a definition that calls it) →
--       which is consumed by Caps-Bridge.agda call sites once they
--       supply pathOccs? sz path.
--
--   subΘTm-occs-le : ∀ ... Θloc σ tm → occsᵗ (subΘTm Θloc σ tm) ≤ occsᵗ tm
--     Proof: structural induction on tm (Exp.agda:266-270).
--     Consumer: pathOccs?-structural in Caps-Bridge.agda, which
--       establishes pathOccs? sz path from subterm provenance.
--
-- The wiring law requires consumers for all postulates.  These will
-- land together with their consumers in a subsequent commit.
