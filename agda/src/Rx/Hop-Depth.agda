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
--   · THE COEFFICIENT IS A MULTIPLIER, NOT A COUNT.  A first draft
--     used a bare `+` and did not survive a nested map: a substitution
--     plugs its value wherever the bound variable occurs, and hopD can
--     read that value's depth more than once.  So the source's depth
--     enters SCALED, and `⊔ 1` keeps the scale ≥ 1 so a fn that drops
--     its argument still dominates the source's own walk.
--
--     Three drafts of "scaled by what", each refuted by a witness in
--     agda/probe/Hop-Descent-Probe.agda, all on 2026-07-28:
--
--       occsᵗ — the index-blind count the sync-linearity ledger
--       (plugs-lenᵉ, inner-len-subΘ) uses.  It reads every varᵗ as 1,
--       so a template that merely MENTIONS an outer Θ variable inflates
--       the coefficient, and substituting a reified observable for that
--       variable inflates it again (the plug arrives carrying its own
--       binders' variables).  The coefficient grew under a substitution
--       that duplicated nothing.
--
--       occs0ᵗ — the same count restricted to the binder's own index.
--       It fixes the phantom inflation and stays put under
--       substitution, and it is still wrong, because it is still a
--       COUNT.  hopD combines by `⊔` at ofᵉ and pairᵗ, where two
--       mentions cost the same as one; and it MULTIPLIES at mapᵉ, where
--       a plug in an inner map's source is scaled by that inner
--       template's coefficient — a factor no count of outer mentions
--       can see.  mul-exceeds is that witness: one mention, no
--       duplication, an emission of 6 against an allowance of 4.
--
--       pmᵗ V 0 — the plug MULTIPLIER, below.  This is what a
--       coefficient in these clauses has always meant.
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

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≡ᵇ_)
open import Data.Bool using (if_then_else_)
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
                          varIx)

------------------------------------------------------------------
-- THE PLUG MULTIPLIER, which is what the coefficients actually are.
--
-- Read hopD as a function of ONE substituted value's depth.  It is
-- affine in that depth:
--
--     hopD (e[v]) ≤ hopD e + pm k e · hopD v
--
-- and `pm k e` is the slope — the factor hopD's own arithmetic applies
-- along every path from the root of `e` to an occurrence of the
-- variable at de Bruijn index k.  That is exactly what a coefficient
-- in a hopD clause has to be, and it is NOT an occurrence count.  Two
-- refutations say so, and they point in opposite directions:
--
--   · an occurrence count OVER-prices `ofᵉ` and `pairᵗ`, where hopD
--     combines by `⊔`.  Mentioning a value twice under a `⊔` does not
--     deepen anything, so the multiplier there is 1, not 2.
--   · an occurrence count UNDER-prices a nested mapᵉ, where hopD
--     MULTIPLIES.  A plug in an inner map's source is scaled by that
--     inner template's coefficient, and a count of the outer mentions
--     cannot see the inner factor at all.  (agda/probe/Hop-Descent-
--     Probe.agda's mul-exceeds: one mention, no duplication, 6 against
--     an allowance of 4.)
--
-- So pm is hopD's own recursion with two changes and nothing else: a
-- variable at index k contributes 1 where hopD contributes 0, and the
-- *All frames drop their `suc`, because an operator's own hop is ADDED
-- to the plug's depth rather than multiplied by it.  Same tree, a
-- different semiring at the leaves.
--
-- pm is defined before hopD and does not mention it — hopD reads pm
-- for its coefficients, not the other way round — so there is no
-- mutual recursion between the two, and pm's own coefficients are pm's
-- (`pmᵗ V 0 f` on a strict subterm).
--
-- THE INVARIANCE that makes it usable: index 0 at a clause's binder is
-- LOCAL, and a substitution plugs Θ-CLOSED values, so every variable a
-- plug brings is compared against an index already bumped past it and
-- contributes 0.  A clause's coefficient therefore cannot move under
-- substitution — which is the property the emitted-value invariant
-- needs, and the property a raw occurrence count also had but for the
-- wrong quantity.
------------------------------------------------------------------

mutual
  pmᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  pmᵉ V k (input i)       = 0
  pmᵉ V k (ofᵉ ts)        = pmᵗˢ V k ts
  pmᵉ V k emptyᵉ          = 0
  pmᵉ V k (mapᵉ f e)      = pmᵗ V (suc k) f + (pmᵗ V 0 f ⊔ 1) * pmᵉ V k e
  pmᵉ V k (takeᵉ c e)     = pmᵉ V k e
  pmᵉ V k (scanᵉ f z e)   =
    (2 + pmᵗ V 0 f) ^ V * (pmᵗ V (suc k) f + pmᵗ V k z + pmᵉ V k e)
  -- the frame's own hop is a `suc` in hopD: added, so it is not part
  -- of the slope
  pmᵉ V k (mergeAllᵉ e)   = pmᵉ V k e
  pmᵉ V k (concatAllᵉ e)  = pmᵉ V k e
  pmᵉ V k (switchAllᵉ e)  = pmᵉ V k e
  pmᵉ V k (exhaustAllᵉ e) = pmᵉ V k e
  pmᵉ V k (μᵉ e)          = pmᵉ V k e
  pmᵉ V k (varᵉ x)        = 0
  pmᵉ V k (deferᵉ e)      = 0

  pmᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  -- THE LEAF, and the only place pm and hopD differ in kind
  pmᵗ V k (varᵗ x)      = if varIx x ≡ᵇ k then 1 else 0
  pmᵗ V k unit̂          = 0
  pmᵗ V k (bool̂ _)      = 0
  pmᵗ V k (nat̂ _)       = 0
  pmᵗ V k (pairᵗ a b)   = pmᵗ V k a ⊔ pmᵗ V k b
  pmᵗ V k (fstᵗ p)      = pmᵗ V k p
  pmᵗ V k (sndᵗ p)      = pmᵗ V k p
  pmᵗ V k (inlᵗ a)      = pmᵗ V k a
  pmᵗ V k (inrᵗ a)      = pmᵗ V k a
  pmᵗ V k (caseᵗ s l r) =
    (pmᵗ V (suc k) l ⊔ pmᵗ V (suc k) r)
      + (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * pmᵗ V k s
  pmᵗ V k (ifᵗ c a b)   = pmᵗ V k a ⊔ pmᵗ V k b
  -- a PrimOp lands in natᵗ or boolᵗ, so nothing plugged into it can
  -- reach a hop — hopD reads this as 0 and so must its slope
  pmᵗ V k (primᵗ _ a)   = 0
  pmᵗ V k (strmᵗ e)     = pmᵉ V k e

  pmᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pmᵗˢ V k []       = 0
  pmᵗˢ V k (y ∷ ys) = pmᵗ V k y ⊔ pmᵗˢ V k ys

mutual
  hopDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  -- a slot is reached by a CONNECT, which pays with unconn, not with
  -- hopD — the share boundary is not this measure's business
  hopDᵉ V (input i)       = 0
  hopDᵉ V (ofᵉ ts)        = hopDᵗˢ V ts
  hopDᵉ V emptyᵉ          = 0
  -- the fn's chain concatenates with the source's, and the source's
  -- depth lands at every Θ-var occurrence
  hopDᵉ V (mapᵉ f e)      = hopDᵗ V f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ V e
  -- the count is a natᵗ term: its value carries no observable
  hopDᵉ V (takeᵉ c e)     = hopDᵉ V e
  -- the refold, bounded by V — see the header
  hopDᵉ V (scanᵉ f z e)   =
    (2 + pmᵗ V 0 f) ^ V * (hopDᵗ V f + hopDᵗ V z + hopDᵉ V e)
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
    (hopDᵗ V l ⊔ hopDᵗ V r) + (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ V s
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
