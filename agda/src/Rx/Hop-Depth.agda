------------------------------------------------------------------
-- THE REMAINING-HOP DEPTH: an upper bound on how many more *All
-- frames a subscription can still enter.
--
-- The descent's rank is currently seeded from the PROGRAM, and every
-- reading of that kind is refuted: the hop edge subscribes a runtime
-- VALUE, structurally unrelated to the caller, so no quantity read off
-- the term, the store or the arrival bounds what comes after it.  This
-- measure is the other direction — it is a quantity a value CARRIES,
-- so a bound on it can be threaded as a strengthened postcondition
-- through the very induction that builds the value, instead of being
-- asserted about the value from outside.
------------------------------------------------------------------

------------------------------------------------------------------
-- TWO DESIGN POINTS, each forced by a counterexample rather than
-- chosen.
--
--   · `+` AT mapᵉ, NOT `⊔`.  A template is applied to the source's
--     values, so the two chains CONCATENATE.  Under `⊔` the measure is
--     already false at a leaf lifted from a plain observable to a
--     flattener over a reified one: the first hop reads two against an
--     allowance of two.
--
--   · THE COEFFICIENT IS A MULTIPLIER, NOT A COUNT.  A substitution
--     plugs its value wherever the bound variable occurs, and the
--     measure can read that value's depth more than once — so the
--     source's depth enters SCALED, and `⊔ 1` keeps the scale at least
--     one so a template that DROPS its argument still dominates the
--     source's own walk.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHY IT IS V-PARAMETERISED.  At a scan the accumulator is REFOLDED,
-- so its depth compounds once per folded value: after k folded values
-- the accumulator nests k deep.  k is bounded by the STORE bound and
-- not by the program, so the measure takes that bound as V and the
-- scan clause pays a V-th power.  Solving the recurrence for the
-- accumulator's depth against a per-fold constant and a per-fold
-- coefficient gives exactly that clause, with k at most V.
--
-- k ≤ V is not an extra assumption: a scan accumulator is a STORED
-- value, so whatever bounds the store bounds it.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHY IT IS η-PARAMETERISED.  η assigns a hop depth to each slot of
-- the telescope, and the `input` clause reports it.  A constant-zero
-- reading there is false: an obs-typed shared slot's def emits values
-- of positive hop, and a subscription connecting to that slot receives
-- them, so zeroing the share boundary breaks at the first flattener
-- over an input.  The honest instantiation recurses on the slot index,
-- which terminates because the telescope is stratified — a shared def
-- reads only earlier inputs.  η at constant zero recovers the naive
-- measure, so nothing downstream has to care until it meets an input.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE AFFINE READING, which is what makes the coefficient's shape
-- decidable rather than a matter of taste.  Read the measure as a
-- function of ONE substituted value's depth: it is affine in that
-- depth, and `pm` at the plugged index is the slope — the factor the
-- measure's own arithmetic applies along every path from the root to
-- an occurrence of that variable.
--
-- So `pm` is the same recursion with two changes and nothing else: a
-- variable at the index contributes one where the measure contributes
-- zero, and the flatteners drop their `suc`, because an operator's own
-- hop is ADDED to the plug's depth rather than multiplied by it.  Same
-- tree, a different semiring at the leaves.  `pm` is defined first and
-- never mentions the measure, so the two are not mutual.
--
-- THE INVARIANCE that makes it usable: the index at a clause's binder
-- is LOCAL, and a substitution plugs Θ-closed values, so every
-- variable a plug brings is compared against an index already bumped
-- past it and contributes zero.  A clause's coefficient therefore
-- cannot move under substitution, which is the property a strengthened
-- postcondition on emitted values needs.
--
-- DEAD ROUTE: an OCCURRENCE COUNT cannot be the coefficient, in either
--   of its two forms, and the two failures point opposite ways.  An
--   index-blind count OVER-prices the `⊔` clauses, where mentioning a
--   value twice deepens nothing, and it inflates further under a
--   substitution that duplicates nothing, because the plug arrives
--   carrying its own binders' variables.  Restricting the count to the
--   binder's own index fixes the phantom inflation and is still wrong,
--   because it is still a count: a plug in an inner map's source is
--   scaled by that inner template's coefficient, a factor no count of
--   outer mentions can see.
-- RECOVERY: git show 919f115 restores two things this port leaves
--   out because nothing reaches them yet — the substitution congruences
--   saying the measure and its slope are invariant under Δᵍ-variable
--   elimination, which is what makes the μ edge free, and the walk they
--   were proven against, whose evaluator this development has replaced.
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

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                          Ctx; Exp; Tm; Val;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

-- the de Bruijn index a Θ-variable stands at.  It has exactly one
-- consumer, `pmᵗ`'s leaf clause, so it lives here rather than beside
-- the syntax it reads
varIx : ∀ {t} {Θ : List Ty} → t ∈ Θ → ℕ
varIx (here _)  = zero
varIx (there p) = suc (varIx p)

------------------------------------------------------------------
-- THE PLUG MULTIPLIER: the slope of the measure in a plugged value's
-- depth, at the variable standing at de Bruijn index k.
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
  -- the frame's own hop is a `suc` in the measure: added, so it is not
  -- part of the slope
  pmᵉ V k (mergeAllᵉ lim e)   = pmᵉ V k e
  pmᵉ V k (switchAllᵉ e)  = pmᵉ V k e
  pmᵉ V k (exhaustAllᵉ e) = pmᵉ V k e
  pmᵉ V k (μᵉ e)          = pmᵉ V k e
  pmᵉ V k (varᵉ x)        = 0
  pmᵉ V k (deferᵉ e)      = 0

  pmᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  -- THE LEAF, and the only place the slope and the measure differ in
  -- kind
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
  -- reach a hop: the measure reads this as zero and so must its slope
  pmᵗ V k (primᵗ _ a)   = 0
  pmᵗ V k (strmᵗ e)     = pmᵉ V k e

  pmᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pmᵗˢ V k []       = 0
  pmᵗˢ V k (y ∷ ys) = pmᵗ V k y ⊔ pmᵗˢ V k ys

------------------------------------------------------------------
-- THE MEASURE.
------------------------------------------------------------------

mutual
  hopDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (η : Fin n → ℕ) →
          Exp Γ Δᵍ Δ Θ t → ℕ
  -- THE SLOT: a connect delivers the def's emissions, so the input
  -- reads the slot's own hop off the environment
  hopDᵉ V η (input i)       = η i
  hopDᵉ V η (ofᵉ ts)        = hopDᵗˢ V η ts
  hopDᵉ V η emptyᵉ          = 0
  -- the template's chain concatenates with the source's, and the
  -- source's depth lands at every Θ-var occurrence
  hopDᵉ V η (mapᵉ f e)      = hopDᵗ V η f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ V η e
  -- the count is a natᵗ term: its value carries no observable
  hopDᵉ V η (takeᵉ c e)     = hopDᵉ V η e
  hopDᵉ V η (scanᵉ f z e)   =
    (2 + pmᵗ V 0 f) ^ V * (hopDᵗ V η f + hopDᵗ V η z + hopDᵉ V η e)
  -- THE HOP EDGE: entering an inner costs exactly one
  hopDᵉ V η (mergeAllᵉ lim e)   = suc (hopDᵉ V η e)
  hopDᵉ V η (switchAllᵉ e)  = suc (hopDᵉ V η e)
  hopDᵉ V η (exhaustAllᵉ e) = suc (hopDᵉ V η e)
  -- an unfold substitutes the original closed μ for a Δᵍ var, and Δᵍ
  -- vars are reachable only under a defer, which this measure cuts, so
  -- an unfold cannot change it
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
  -- a case BINDS, so it plugs like a template: the scrutinee's depth
  -- lands at every occurrence of the branch's bound variable
  hopDᵗ V η (caseᵗ s l r) =
    (hopDᵗ V η l ⊔ hopDᵗ V η r) + (pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) * hopDᵗ V η s
  hopDᵗ V η (ifᵗ c a b)   = hopDᵗ V η a ⊔ hopDᵗ V η b
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

