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
-- A `scanᵉ` IS WORTH ITS FOLD COUNT TIMES ITS STEP FUNCTION'S LAYERS,
-- because the accumulator is re-wrapped once per delivered payload
-- while the scan's own frame charges its emissions nothing
-- (`burst-scf-zero`).  That product is the whole reason a syntactic
-- measure of the subject cannot serve: emission k of a w-layer step
-- sits w·k deep under syntax that does not grow with k.
--
-- A LIST OF PAYLOADS IS WORTH THEIR MAX, NOT THEIR SUM, because
-- `depthWalk` is a `⊔` over the burst's values — they are entered one
-- at a time, each from the same frame, so two payloads abreast cost
-- what the deeper of them costs.

------------------------------------------------------------------
-- THE FOLD COUNT IS A PARAMETER, AND THAT IS THE ONE THING THIS
-- MEASURE'S PREDECESSOR GOT WRONG.  It read the count off the width
-- family at the UNSUBSTITUTED source, where a payload variable weighs
-- nothing, so two programs differing only in how many literals a map
-- consumed shared one cap against depths of 4 and 8.  `W` is supplied
-- instead, and the measure is monotone in it.  `W` does no second job
-- here: it multiplies, and nothing is required to fit under it, which is
-- what makes it unlike the refold exponent that killed the hop currency.
--
-- WHAT THE CONSUMER SUPPLIES IS THE INSTANT'S FOLD COUNT, and it is not
-- the burst-width cap even though a burst is what delivers the payloads.
-- The width cap steps by exponentiation once per fold, so it towers over
-- the height cap it would have to fit under; the fold count is the
-- number the caps recurrence itself runs a frame step for, and the
-- height's own pooled summand exists to dominate it.  Same product,
-- different — and available — currency.
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
open import Data.Nat  using (ℕ; suc; _+_; _*_; _⊔_)

open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Rx.Exp using (Ctx; Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Val;
  Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
  strmᵗ)

mutual
  nestDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (W : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  nestDᵉ W (input i)       = 0
  nestDᵉ W (ofᵉ ts)        = nestDᵗˢ W ts
  nestDᵉ W emptyᵉ          = 0
  nestDᵉ W (mapᵉ f e)      = nestDᵗ W f + nestDᵉ W e
  nestDᵉ W (takeᵉ c e)     = nestDᵉ W e
  -- THE PRODUCT: one re-wrap per delivered payload
  nestDᵉ W (scanᵉ f z e)   = nestDᵗ W z + W * nestDᵗ W f + nestDᵉ W e
  -- THE SPENDING ARC: one suc per *All layer
  nestDᵉ W (mergeAllᵉ e)   = suc (nestDᵉ W e)
  nestDᵉ W (concatAllᵉ e)  = suc (nestDᵉ W e)
  nestDᵉ W (switchAllᵉ e)  = suc (nestDᵉ W e)
  nestDᵉ W (exhaustAllᵉ e) = suc (nestDᵉ W e)
  nestDᵉ W (μᵉ e)          = nestDᵉ W e
  nestDᵉ W (varᵉ x)        = 0
  -- THE GATE TRUNCATES, and it is what makes μ safe
  nestDᵉ W (deferᵉ e)      = 0

  nestDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (W : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  nestDᵗ W (varᵗ x)      = 0
  nestDᵗ W unit̂          = 0
  nestDᵗ W (bool̂ _)      = 0
  nestDᵗ W (nat̂ _)       = 0
  nestDᵗ W (pairᵗ a b)   = nestDᵗ W a ⊔ nestDᵗ W b
  nestDᵗ W (fstᵗ p)      = nestDᵗ W p
  nestDᵗ W (sndᵗ p)      = nestDᵗ W p
  nestDᵗ W (inlᵗ a)      = nestDᵗ W a
  nestDᵗ W (inrᵗ a)      = nestDᵗ W a
  nestDᵗ W (caseᵗ s l r) = nestDᵗ W s + (nestDᵗ W l ⊔ nestDᵗ W r)
  nestDᵗ W (ifᵗ c a b)   = nestDᵗ W c ⊔ nestDᵗ W a ⊔ nestDᵗ W b
  nestDᵗ W (primᵗ _ a)   = nestDᵗ W a
  nestDᵗ W (strmᵗ e)     = nestDᵉ W e

  nestDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (W : ℕ) →
    List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestDᵗˢ W []       = 0
  nestDᵗˢ W (y ∷ ys) = nestDᵗ W y ⊔ nestDᵗˢ W ys

-- A STORED VALUE IS CHARGED THROUGH ITS TYPE, exactly as its size is:
-- `Val` is a computed family, so the only way in is to recurse on the
-- `Ty`, and `obs` is where a value becomes syntax again.  A pair takes
-- the MAX of its components for the same reason a burst does — they are
-- entered separately, from the same frame.
nestDᵛ : ∀ {n} {Γ : Ctx n} (W : ℕ) (t : Ty) → Val Γ t → ℕ
nestDᵛ W unitᵗ    _        = 0
nestDᵛ W boolᵗ    _        = 0
nestDᵛ W natᵗ     _        = 0
nestDᵛ W (s ×ᵗ t) (a , b)  = nestDᵛ W s a ⊔ nestDᵛ W t b
nestDᵛ W (s +ᵗ t) (inj₁ a) = nestDᵛ W s a
nestDᵛ W (s +ᵗ t) (inj₂ b) = nestDᵛ W t b
nestDᵛ W (obs t)  e        = nestDᵉ W e
