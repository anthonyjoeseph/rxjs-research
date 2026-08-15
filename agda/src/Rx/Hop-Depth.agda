------------------------------------------------------------------
-- THE REMAINING-HOP DEPTH, candidate replacement for dBound's `r`.
--
-- `rank ∘ measureE` was refuted as the hop-descending quantity on
-- 2026-07-27 (Hop-Descent-Probe (DELETED; git history)): a two-use template
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
--     Hop-Descent-Probe (DELETED; git history), all on 2026-07-28:
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
open import Data.Fin  using (Fin)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any       using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                          Ctx; Exp; Tm; Val;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          varIx;
                          elimGExp; elimGTm; elimGTms; unfoldμ)

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

-- WHY IT IS η-PARAMETERISED (η : Fin n → ℕ, the SLOT HOP ENVIRONMENT):
-- the constant-0 input clause was REFUTED (input-wet, machine-checked —
-- Verify-Budget-Sufficient.Walk-Level, Demand-Probe series W): an
-- obs-typed shared slot's def emits values of positive hop, and a
-- subscription that connects to the slot receives them, so a bound
-- that zeroes the share boundary is false at the first mergeAllᵉ over
-- an input.  The clause now reports η i — the caller's assignment of a
-- hop depth to each slot.  The honest instantiation is Rx.Slot-Hop's
-- slotHop, computable by recursion on the slot index because the
-- telescope is stratified (a shared def reads only earlier inputs —
-- `inputsBelowᵉ`, Rx.Slots).  η ≡ const 0 recovers the old measure,
-- so nothing downstream is forced to care until it meets an input.
mutual
  hopDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (η : Fin n → ℕ) →
          Exp Γ Δᵍ Δ Θ t → ℕ
  -- THE SLOT: a connect delivers the def's emissions, so the input
  -- reads the slot's own hop off the environment — see the header
  hopDᵉ V η (input i)       = η i
  hopDᵉ V η (ofᵉ ts)        = hopDᵗˢ V η ts
  hopDᵉ V η emptyᵉ          = 0
  -- the fn's chain concatenates with the source's, and the source's
  -- depth lands at every Θ-var occurrence
  hopDᵉ V η (mapᵉ f e)      = hopDᵗ V η f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ V η e
  -- the count is a natᵗ term: its value carries no observable
  hopDᵉ V η (takeᵉ c e)     = hopDᵉ V η e
  -- the refold, bounded by V — see the header
  hopDᵉ V η (scanᵉ f z e)   =
    (2 + pmᵗ V 0 f) ^ V * (hopDᵗ V η f + hopDᵗ V η z + hopDᵉ V η e)
  -- THE HOP EDGE: entering an inner costs exactly one
  hopDᵉ V η (mergeAllᵉ e)   = suc (hopDᵉ V η e)
  hopDᵉ V η (concatAllᵉ e)  = suc (hopDᵉ V η e)
  hopDᵉ V η (switchAllᵉ e)  = suc (hopDᵉ V η e)
  hopDᵉ V η (exhaustAllᵉ e) = suc (hopDᵉ V η e)
  -- unfoldμ substitutes the ORIGINAL closed μ for a Δᵍ var, and Δᵍ
  -- vars are reachable only under deferᵉ, which this measure cuts —
  -- so an unfold cannot change hopD, and the μ edge stays weakly
  -- monotone (it pays with dBound-μ's s, as it already did)
  hopDᵉ V η (μᵉ e)          = hopDᵉ V η e
  hopDᵉ V η (varᵉ x)        = 0
  hopDᵉ V η (deferᵉ e)      = 0

  hopDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (η : Fin n → ℕ) →
          Tm Γ Δᵍ Δ Θ t → ℕ
  hopDᵗ V η (varᵗ x)      = 0
  hopDᵗ V η unit̂          = 0
  hopDᵗ V η (bool̂ _)      = 0
  hopDᵗ V η (nat̂ _)       = 0
  hopDᵗ V η (pairᵗ a b)   = hopDᵗ V η a ⊔ hopDᵗ V η b
  hopDᵗ V η (fstᵗ p)      = hopDᵗ V η p
  hopDᵗ V η (sndᵗ p)      = hopDᵗ V η p
  hopDᵗ V η (inlᵗ a)      = hopDᵗ V η a
  hopDᵗ V η (inrᵗ a)      = hopDᵗ V η a
  -- caseᵗ BINDS, so it plugs like a fn: the scrutinee's depth lands at
  -- every occurrence of the branch's bound variable
  hopDᵗ V η (caseᵗ s l r) =
    (hopDᵗ V η l ⊔ hopDᵗ V η r) + (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ V η s
  hopDᵗ V η (ifᵗ c a b)   = hopDᵗ V η a ⊔ hopDᵗ V η b
  -- every PrimOp lands in natᵗ or boolᵗ, so its value carries nothing
  hopDᵗ V η (primᵗ _ a)   = 0
  hopDᵗ V η (strmᵗ e)     = hopDᵉ V η e

  hopDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (η : Fin n → ℕ) →
           List (Tm Γ Δᵍ Δ Θ t) → ℕ
  hopDᵗˢ V η []       = 0
  hopDᵗˢ V η (y ∷ ys) = hopDᵗ V η y ⊔ hopDᵗˢ V η ys

-- the same reading on a runtime value: an embedded observable is its
-- expression's, a ground payload carries no hops
hopDᵛ : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (t : Ty) → Val Γ t → ℕ
hopDᵛ V η unitᵗ    _        = 0
hopDᵛ V η boolᵗ    _        = 0
hopDᵛ V η natᵗ     _        = 0
hopDᵛ V η (s ×ᵗ t) (a , b)  = hopDᵛ V η s a ⊔ hopDᵛ V η t b
hopDᵛ V η (s +ᵗ t) (inj₁ a) = hopDᵛ V η s a
hopDᵛ V η (s +ᵗ t) (inj₂ b) = hopDᵛ V η t b
hopDᵛ V η (obs t)  e        = hopDᵉ V η e

------------------------------------------------------------------
-- ELIMINATION CONGRUENCES: hopD and pm are invariant under
-- Δᵍ-variable substitution (elimGExp rewrites Δᵍ-variables only).
------------------------------------------------------------------

mutual
  pm-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    pmᵉ V k (elimGExp x cl b) ≡ pmᵉ V k b
  pm-elimGᵉ V k x cl (input i)       = refl
  pm-elimGᵉ V k x cl (ofᵉ ts)        = pm-elimGᵗˢ V k x cl ts
  pm-elimGᵉ V k x cl emptyᵉ          = refl
  pm-elimGᵉ V k x cl (mapᵉ f b)      =
    cong₂ _+_ (pm-elimGᵗ V (suc k) x cl f)
              (cong₂ _*_ (cong (_⊔ 1) (pm-elimGᵗ V 0 x cl f))
                         (pm-elimGᵉ V k x cl b))
  pm-elimGᵉ V k x cl (takeᵉ c b)     = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (scanᵉ f z b)   =
    cong₂ _*_ (cong (λ y → (2 + y) ^ V) (pm-elimGᵗ V 0 x cl f))
              (cong₂ _+_ (cong₂ _+_ (pm-elimGᵗ V (suc k) x cl f)
                                    (pm-elimGᵗ V k x cl z))
                         (pm-elimGᵉ V k x cl b))
  pm-elimGᵉ V k x cl (mergeAllᵉ b)   = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (concatAllᵉ b)  = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (switchAllᵉ b)  = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (exhaustAllᵉ b) = pm-elimGᵉ V k x cl b
  pm-elimGᵉ V k x cl (μᵉ b)          = pm-elimGᵉ V k (there x) cl b
  pm-elimGᵉ V k x cl (varᵉ y)        = refl
  pm-elimGᵉ V k x cl (deferᵉ b)      = refl

  pm-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    pmᵗ V k (elimGTm x cl f) ≡ pmᵗ V k f
  pm-elimGᵗ V k x cl (varᵗ y)      = refl
  pm-elimGᵗ V k x cl unit̂          = refl
  pm-elimGᵗ V k x cl (bool̂ b)      = refl
  pm-elimGᵗ V k x cl (nat̂ m)       = refl
  pm-elimGᵗ V k x cl (pairᵗ a b)   =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl a) (pm-elimGᵗ V k x cl b)
  pm-elimGᵗ V k x cl (fstᵗ p)      = pm-elimGᵗ V k x cl p
  pm-elimGᵗ V k x cl (sndᵗ p)      = pm-elimGᵗ V k x cl p
  pm-elimGᵗ V k x cl (inlᵗ a)      = pm-elimGᵗ V k x cl a
  pm-elimGᵗ V k x cl (inrᵗ a)      = pm-elimGᵗ V k x cl a
  pm-elimGᵗ V k x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (pm-elimGᵗ V (suc k) x cl l)
                         (pm-elimGᵗ V (suc k) x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pm-elimGᵗ V 0 x cl l)
                                               (pm-elimGᵗ V 0 x cl r))
                                    refl)
                         (pm-elimGᵗ V k x cl s))
  pm-elimGᵗ V k x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl a) (pm-elimGᵗ V k x cl b)
  pm-elimGᵗ V k x cl (primᵗ op a)  = refl
  pm-elimGᵗ V k x cl (strmᵗ b)     = pm-elimGᵉ V k x cl b

  pm-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V k : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    pmᵗˢ V k (elimGTms x cl ts) ≡ pmᵗˢ V k ts
  pm-elimGᵗˢ V k x cl []       = refl
  pm-elimGᵗˢ V k x cl (y ∷ ys) =
    cong₂ _⊔_ (pm-elimGᵗ V k x cl y) (pm-elimGᵗˢ V k x cl ys)

mutual
  hopD-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (η : Fin n → ℕ)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    hopDᵉ V η (elimGExp x cl b) ≡ hopDᵉ V η b
  hopD-elimGᵉ V η x cl (input i)       = refl
  hopD-elimGᵉ V η x cl (ofᵉ ts)        = hopD-elimGᵗˢ V η x cl ts
  hopD-elimGᵉ V η x cl emptyᵉ          = refl
  hopD-elimGᵉ V η x cl (mapᵉ f b)      =
    cong₂ _+_ (hopD-elimGᵗ V η x cl f)
              (cong₂ _*_ (cong (_⊔ 1) (pm-elimGᵗ V 0 x cl f))
                         (hopD-elimGᵉ V η x cl b))
  hopD-elimGᵉ V η x cl (takeᵉ c b)     = hopD-elimGᵉ V η x cl b
  hopD-elimGᵉ V η x cl (scanᵉ f z b)   =
    cong₂ _*_ (cong (λ y → (2 + y) ^ V) (pm-elimGᵗ V 0 x cl f))
              (cong₂ _+_ (cong₂ _+_ (hopD-elimGᵗ V η x cl f)
                                    (hopD-elimGᵗ V η x cl z))
                         (hopD-elimGᵉ V η x cl b))
  hopD-elimGᵉ V η x cl (mergeAllᵉ b)   = cong suc (hopD-elimGᵉ V η x cl b)
  hopD-elimGᵉ V η x cl (concatAllᵉ b)  = cong suc (hopD-elimGᵉ V η x cl b)
  hopD-elimGᵉ V η x cl (switchAllᵉ b)  = cong suc (hopD-elimGᵉ V η x cl b)
  hopD-elimGᵉ V η x cl (exhaustAllᵉ b) = cong suc (hopD-elimGᵉ V η x cl b)
  hopD-elimGᵉ V η x cl (μᵉ b)          = hopD-elimGᵉ V η (there x) cl b
  hopD-elimGᵉ V η x cl (varᵉ y)        = refl
  hopD-elimGᵉ V η x cl (deferᵉ b)      = refl

  hopD-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (η : Fin n → ℕ)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    hopDᵗ V η (elimGTm x cl f) ≡ hopDᵗ V η f
  hopD-elimGᵗ V η x cl (varᵗ y)      = refl
  hopD-elimGᵗ V η x cl unit̂          = refl
  hopD-elimGᵗ V η x cl (bool̂ b)      = refl
  hopD-elimGᵗ V η x cl (nat̂ m)       = refl
  hopD-elimGᵗ V η x cl (pairᵗ a b)   =
    cong₂ _⊔_ (hopD-elimGᵗ V η x cl a) (hopD-elimGᵗ V η x cl b)
  hopD-elimGᵗ V η x cl (fstᵗ p)      = hopD-elimGᵗ V η x cl p
  hopD-elimGᵗ V η x cl (sndᵗ p)      = hopD-elimGᵗ V η x cl p
  hopD-elimGᵗ V η x cl (inlᵗ a)      = hopD-elimGᵗ V η x cl a
  hopD-elimGᵗ V η x cl (inrᵗ a)      = hopD-elimGᵗ V η x cl a
  hopD-elimGᵗ V η x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (hopD-elimGᵗ V η x cl l) (hopD-elimGᵗ V η x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pm-elimGᵗ V 0 x cl l)
                                               (pm-elimGᵗ V 0 x cl r))
                                    refl)
                         (hopD-elimGᵗ V η x cl s))
  hopD-elimGᵗ V η x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (hopD-elimGᵗ V η x cl a) (hopD-elimGᵗ V η x cl b)
  hopD-elimGᵗ V η x cl (primᵗ op a)  = refl
  hopD-elimGᵗ V η x cl (strmᵗ b)     = hopD-elimGᵉ V η x cl b

  hopD-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (V : ℕ) (η : Fin n → ℕ)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    hopDᵗˢ V η (elimGTms x cl ts) ≡ hopDᵗˢ V η ts
  hopD-elimGᵗˢ V η x cl []       = refl
  hopD-elimGᵗˢ V η x cl (y ∷ ys) =
    cong₂ _⊔_ (hopD-elimGᵗ V η x cl y) (hopD-elimGᵗˢ V η x cl ys)

hopD-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (η : Fin n → ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  hopDᵉ V η (unfoldμ body) ≡ hopDᵉ V η (μᵉ body)
hopD-unfoldμ V η body = hopD-elimGᵉ V η (here refl) (μᵉ body) body
