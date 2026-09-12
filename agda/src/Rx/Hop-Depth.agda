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
--
-- AND THAT LAST SENTENCE IS THE ONE THING HERE NOTHING PAYS FOR, which
-- is worth saying where the premise is made rather than where it is
-- spent.  A run's bound is the FUEL its caller hands `evaluate`, and
-- fuel counts ARRIVALS — so a cascade delivering entirely inside one
-- subscribe frame refolds as many times as its source has literals
-- while consuming no fuel at all.  Measured in `Probed.Operator-Root`:
-- a fold over four sources differing in literals alone reads the SAME
-- at every length, 532899 at a bound of six, while the depth its own
-- run hands out multiplies by three per literal — so the two meet at
-- twelve literals, and the root there is a flattener that subscribes
-- every layer.  Whether k really is under V is therefore a question
-- about what the store counts, not a corollary of the accumulator
-- being stored, and the arithmetic above is only sound once something
-- answers it.
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
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Walk-Level.agda`
--   restores the walk these congruences were first proven against, whose
--   evaluator this development has replaced.
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
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          elimGExp; elimGTm; elimGTms; unfoldμ)

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

------------------------------------------------------------------
-- THE MEASURE AND ITS SLOPE ARE INVARIANT UNDER Δᵍ-ELIMINATION, which
-- is what makes the μ edge free.  A `μᵉ` unfolding substitutes the
-- ORIGINAL closed redex for a Δᵍ-variable, and Δᵍ-variables are
-- reachable only under a `deferᵉ`, which both recursions cut — so
-- every clause is either a congruence over subterms or an outright
-- `refl` at the two leaves that could have seen the plug.
--
-- The slope's congruence is proven first and separately because the
-- measure reads it for its coefficients: the measure's `mapᵉ`, `scanᵉ`
-- and `caseᵗ` clauses each need the slope's invariance at the same
-- subterm, and the two families are not mutual.
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
  pm-elimGᵉ V k x cl (mergeAllᵉ lim b)   = pm-elimGᵉ V k x cl b
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
  hopD-elimGᵉ V η x cl (mergeAllᵉ lim b)   = cong suc (hopD-elimGᵉ V η x cl b)
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

-- THE μ EDGE, in one line: the redex and its unfolding read EQUAL, so
-- the rank component survives the step at no cost and the μ guard pays
-- with the sync component alone.
hopD-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (η : Fin n → ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  hopDᵉ V η (unfoldμ body) ≡ hopDᵉ V η (μᵉ body)
hopD-unfoldμ V η body = hopD-elimGᵉ V η (here refl) (μᵉ body) body

