------------------------------------------------------------------
-- THE NESTING MEASURE: how many `*All` layers a run can descend
-- through, as opposed to how many payloads travel abreast.  The three
-- clauses that carry it are read off the evaluator rather than fitted
-- to a number.
--
-- A `*All` LAYER IS WORTH ONE `suc`, because that is what `depthFrame`
-- at a `thru-outer` frame charges, and a `thru-outer` frame is one of
-- only two places the depth measure spends anything at all.
--
-- A `scanᵉ` IS WORTH ITS STEP FUNCTION'S LAYERS ONCE, because on any
-- ONE chain the walk enters the step function once per scan frame; the
-- layers the folds pile onto the ACCUMULATOR live in the store, whose
-- measure is read off the state and so sees them as they accrue.  The
-- fold-times-wrap product is real, but it is priced where the folds
-- happen — the per-instant cap's increment — never inside a measure of
-- syntax, which cannot know a count that has not happened yet.
--
-- A LIST OF PAYLOADS IS WORTH THEIR MAX, NOT THEIR SUM, because
-- `depthWalk` is a `⊔` over the burst's values — they are entered one
-- at a time, each from the same frame, so two payloads abreast cost
-- what the deeper of them costs.

------------------------------------------------------------------
-- THE MEASURE IS RAW, AND ITS TWO PREDECESSORS DIED OF NOT BEING SO.
-- The first read a fold count off the width family at the UNSUBSTITUTED
-- source, where a payload variable weighs nothing, so two programs
-- differing only in how many literals a map consumed shared one cap
-- against depths of 4 and 8.  The second took the count as a PARAMETER
-- and multiplied by it — and any count worth supplying is defined off
-- the caps recurrence, so the parameter moves with the instant while a
-- preservation step prices its increment at the old one; that is the
-- squeeze the count-parametric predicate was machine-refuted by.  A raw
-- layer count has no parameter to move: what a fold ADDS is priced at
-- the fold, by the per-instant cap's increment, in a currency read off
-- the real dynamics rather than off any cap.
--
-- AND IT IS NOT THE WIDTH FAMILY WEARING A NEW NAME.  That family
-- measures payloads abreast, and a bare wrap layer multiplies its
-- verdict by one and adds nothing, so everything over there is blind to
-- how deeply a step function wraps its own accumulator.  Blindness to
-- exactly this is what refuted it.

------------------------------------------------------------------
-- THE MAX IS NOT A TIGHTENING FOR ITS OWN SAKE — the summing form was
-- priced dead by the one statement this measure exists to support.  The
-- depth face's `*All` arm bounds a burst by descending into each
-- emitted inner, so it needs an emitted inner's nesting to be under its
-- EMITTER'S; under a summing list clause it is not, because a step
-- function may hand its input observable to a list TWICE — the emitter
-- reads 2, the inner it emits reads 3, and the inner's own depth is 2,
-- so the sum was over the depth by exactly the duplication.
--
-- THE DEFER GATE TRUNCATES, AND THE μ CLAUSE IS WHY.  `depthE` returns
-- zero at a `deferᵉ` — a deferred body is not entered synchronously, it
-- mints its own source and is walked later as a subject in its own right
-- — so passing through the gate would buy the measure nothing on the
-- clause it is read at.  What it would COST is the μ clause: `depthE`
-- peels one gas and recurses on `unfoldμ body`, so the bound needs the
-- measure not to grow under unfolding, and unfolding substitutes the
-- whole `μᵉ` term at every guarded occurrence.  With the gate at zero
-- both sides read `nestDᵉ` of the body and the clause is an equality;
-- passing through, a body naming itself twice under a `*All` doubles the
-- measure per unfold and no bound survives.  Same design as the
-- synchronous size, which truncates at the gate for the same reason.
--
-- THE `input` CLAUSE CONTRIBUTES NOTHING, AND A DESCENDING ONE IS
-- STRUCTURALLY DEAD.  Descending into the slot definition on slot fuel
-- with a visited set — how the width family does it — does not work
-- here, because the consumer fixes the fuel at the slot count, which is
-- a VARIABLE: the clause never reduces, and the parent has no more fuel
-- than the child it would recurse into, so there is no inequality to
-- prove even in principle.  The width family gets away with it by
-- threading its fuel through its consumers; a measure read off a `Sched`
-- cannot.  So a slot's nesting is charged where the slots are.
--
-- DEAD ROUTE: charging a slot's nesting by its SIZE.  The measure is
--   exponential in the program — one factor per nested scan — so no
--   bound of it by a syntactic size exists to be proven.
------------------------------------------------------------------
module Rx.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; suc; _+_; _⊔_)

open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Rx.Exp using (Ctx; Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Val;
  Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
  strmᵗ)

mutual
  nestDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  nestDᵉ (input i)       = 0
  nestDᵉ (ofᵉ ts)        = nestDᵗˢ ts
  nestDᵉ emptyᵉ          = 0
  nestDᵉ (mapᵉ f e)      = nestDᵗ f + nestDᵉ e
  nestDᵉ (takeᵉ c e)     = nestDᵉ e
  -- THE PRODUCT: one re-wrap per delivered payload
  nestDᵉ (scanᵉ f z e)   = nestDᵗ z + nestDᵗ f + nestDᵉ e
  -- THE SPENDING ARC: one suc per *All layer
  nestDᵉ (mergeAllᵉ e)   = suc (nestDᵉ e)
  nestDᵉ (concatAllᵉ e)  = suc (nestDᵉ e)
  nestDᵉ (switchAllᵉ e)  = suc (nestDᵉ e)
  nestDᵉ (exhaustAllᵉ e) = suc (nestDᵉ e)
  nestDᵉ (μᵉ e)          = nestDᵉ e
  nestDᵉ (varᵉ x)        = 0
  -- THE GATE TRUNCATES, and it is what makes μ safe
  nestDᵉ (deferᵉ e)      = 0

  nestDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  nestDᵗ (varᵗ x)      = 0
  nestDᵗ unit̂          = 0
  nestDᵗ (bool̂ _)      = 0
  nestDᵗ (nat̂ _)       = 0
  nestDᵗ (pairᵗ a b)   = nestDᵗ a ⊔ nestDᵗ b
  nestDᵗ (fstᵗ p)      = nestDᵗ p
  nestDᵗ (sndᵗ p)      = nestDᵗ p
  nestDᵗ (inlᵗ a)      = nestDᵗ a
  nestDᵗ (inrᵗ a)      = nestDᵗ a
  nestDᵗ (caseᵗ s l r) = nestDᵗ s + (nestDᵗ l ⊔ nestDᵗ r)
  nestDᵗ (ifᵗ c a b)   = nestDᵗ c ⊔ nestDᵗ a ⊔ nestDᵗ b
  nestDᵗ (primᵗ _ a)   = nestDᵗ a
  nestDᵗ (strmᵗ e)     = nestDᵉ e

  nestDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} →
    List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestDᵗˢ []       = 0
  nestDᵗˢ (y ∷ ys) = nestDᵗ y ⊔ nestDᵗˢ ys

-- A STORED VALUE IS CHARGED THROUGH ITS TYPE, exactly as its size is:
-- `Val` is a computed family, so the only way in is to recurse on the
-- `Ty`, and `obs` is where a value becomes syntax again.  A pair takes
-- the MAX of its components for the same reason a burst does — they are
-- entered separately, from the same frame.
nestDᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
nestDᵛ unitᵗ    _        = 0
nestDᵛ boolᵗ    _        = 0
nestDᵛ natᵗ     _        = 0
nestDᵛ (s ×ᵗ t) (a , b)  = nestDᵛ s a ⊔ nestDᵛ t b
nestDᵛ (s +ᵗ t) (inj₁ a) = nestDᵛ s a
nestDᵛ (s +ᵗ t) (inj₂ b) = nestDᵛ t b
nestDᵛ (obs t)  e        = nestDᵉ e
