------------------------------------------------------------------
-- THE REMAINING-HOP DEPTH, candidate replacement for dBound's `r`.
--
-- `rank ∘ measureE` was refuted as the hop-descending quantity on
-- 2026-07-27 (agda/probe/Hop-Descent-Probe.agda): a two-use template
-- copies the plugged value's shells once per occurrence, so the hop's
-- multiset can EXCEED the carrier's.  hopD is the replacement under
-- measurement.  It is stated here, alone, so the probes can gate it
-- before the walk statement takes a dependency on it.
--
-- WHAT IT COUNTS: an upper bound on the number of *All frames a
-- subscription can still enter — hop edges remaining.  Two design
-- points, each forced by a witness rather than chosen:
--
--   · `+` AT mapᵉ, not `⊔`.  A fn's template is applied to the
--     source's values, so the two chains CONCATENATE.  With `⊔` the
--     measure is already false: lift the probe's leaf from `big` to
--     mergeAll (of (strm big)) and the first hop reads 2 ↦ 2.
--
--   · OCCURRENCE WEIGHTING.  A first draft used a bare `+` and did
--     not survive a nested map: substitution plugs the value at EVERY
--     Θ-var occurrence, and when two of those sit on opposite sides of
--     a `+` the plugged depth is counted twice.  So the source's depth
--     enters scaled by occsᵗ — the same multiplicity the proven
--     sync-linearity ledger (plugs-lenᵉ, inner-len-subΘ) already uses.
--     `⊔ 1` keeps the scale ≥ 1 so a fn that drops its argument still
--     dominates the source's own walk.
--
-- WHY IT IS V-PARAMETERISED: at scanᵉ the accumulator is REFOLDED, so
-- its depth compounds once per folded value — syncBudget's memo,
-- "after k folded values the acc nests k deep".  k is bounded by the
-- store bound, not by the program, so hopD takes V and the scan clause
-- pays (2 + occs)^V.  Solving aₖ ≤ F + c·(aₖ₋₁ ⊔ m) with a₀ = Z gives
-- aₖ ≤ (1 + c)^k · (F + Z + m), which is that clause with k ≤ V.
--
-- k ≤ V IS NOT AN EXTRA ASSUMPTION.  A scan accumulator is a STORED
-- value — Verify-Budget-Sufficient's boundedNode reads exactly
-- `boundedNode B (scan-st v) = sizeᵛ v ≤ᵇ B` — so the store invariant
-- the proof already carries bounds its SIZE by V.  A fold that deepens
-- the accumulator adds at least one constructor, so k ≤ sizeᵛ accₖ ≤ V,
-- and a fold that does not deepen it does not raise hopD either.  The
-- margin is not close: V is sizeBudgetAt, a TOWER of 2s of height
-- (4 + size)(1 + id), hence ≥ towerℕ 5 ≡ 2^65536.  This is why there is
-- no corpus counter for k ≤ V — V is not even computable, so the
-- comparison would be vacuous rather than informative.
--
-- Everything here is an UPPER bound; no clause needs to be tight.
------------------------------------------------------------------
module Rx.Hop-Depth where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                          Ctx; Exp; Tm; Val;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          occsᵗ)

mutual
  hopDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  -- a slot is reached by a CONNECT, which pays with unconn, not with
  -- hopD — the share boundary is not this measure's business
  hopDᵉ V (input i)       = 0
  hopDᵉ V (ofᵉ ts)        = hopDᵗˢ V ts
  hopDᵉ V emptyᵉ          = 0
  -- the fn's chain concatenates with the source's, and the source's
  -- depth lands at every Θ-var occurrence
  hopDᵉ V (mapᵉ f e)      = hopDᵗ V f + (occsᵗ f ⊔ 1) * hopDᵉ V e
  -- the count is a natᵗ term: its value carries no observable
  hopDᵉ V (takeᵉ c e)     = hopDᵉ V e
  -- the refold, bounded by V — see the header
  hopDᵉ V (scanᵉ f z e)   =
    (2 + occsᵗ f) ^ V * (hopDᵗ V f + hopDᵗ V z + hopDᵉ V e)
  -- THE HOP EDGE: entering an inner costs exactly one
  hopDᵉ V (mergeAllᵉ e)   = suc (hopDᵉ V e)
  hopDᵉ V (concatAllᵉ e)  = suc (hopDᵉ V e)
  hopDᵉ V (switchAllᵉ e)  = suc (hopDᵉ V e)
  hopDᵉ V (exhaustAllᵉ e) = suc (hopDᵉ V e)
  -- unfoldμ substitutes the ORIGINAL closed μ for a Δᵍ var, and Δᵍ
  -- vars are reachable only under deferᵉ, which this measure cuts —
  -- so an unfold cannot change hopD, and the μ edge stays weakly
  -- monotone (it pays with dBound-μ's s, as it already did)
  hopDᵉ V (μᵉ e)          = hopDᵉ V e
  hopDᵉ V (varᵉ x)        = 0
  hopDᵉ V (deferᵉ e)      = 0

  hopDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  hopDᵗ V (varᵗ x)      = 0
  hopDᵗ V unit̂          = 0
  hopDᵗ V (bool̂ _)      = 0
  hopDᵗ V (nat̂ _)       = 0
  hopDᵗ V (pairᵗ a b)   = hopDᵗ V a ⊔ hopDᵗ V b
  hopDᵗ V (fstᵗ p)      = hopDᵗ V p
  hopDᵗ V (sndᵗ p)      = hopDᵗ V p
  hopDᵗ V (inlᵗ a)      = hopDᵗ V a
  hopDᵗ V (inrᵗ a)      = hopDᵗ V a
  -- caseᵗ BINDS, so it plugs like a fn: the scrutinee's depth lands at
  -- every occurrence of the branch's bound variable
  hopDᵗ V (caseᵗ s l r) =
    (hopDᵗ V l ⊔ hopDᵗ V r) + (occsᵗ l ⊔ occsᵗ r ⊔ 1) * hopDᵗ V s
  hopDᵗ V (ifᵗ c a b)   = hopDᵗ V a ⊔ hopDᵗ V b
  -- every PrimOp lands in natᵗ or boolᵗ, so its value carries nothing
  hopDᵗ V (primᵗ _ a)   = 0
  hopDᵗ V (strmᵗ e)     = hopDᵉ V e

  hopDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  hopDᵗˢ V []       = 0
  hopDᵗˢ V (y ∷ ys) = hopDᵗ V y ⊔ hopDᵗˢ V ys

-- the same reading on a runtime value: an embedded observable is its
-- expression's, a ground payload carries no hops
hopDᵛ : ∀ {n} {Γ : Ctx n} (V : ℕ) (t : Ty) → Val Γ t → ℕ
hopDᵛ V unitᵗ    _        = 0
hopDᵛ V boolᵗ    _        = 0
hopDᵛ V natᵗ     _        = 0
hopDᵛ V (s ×ᵗ t) (a , b)  = hopDᵛ V s a ⊔ hopDᵛ V t b
hopDᵛ V (s +ᵗ t) (inj₁ a) = hopDᵛ V s a
hopDᵛ V (s +ᵗ t) (inj₂ b) = hopDᵛ V t b
hopDᵛ V (obs t)  e        = hopDᵉ V e
