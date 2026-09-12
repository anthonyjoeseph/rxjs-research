------------------------------------------------------------------
-- THE NESTING MEASURE: how many `*All` layers a run can descend
-- through, as opposed to how many payloads travel abreast.  It is the
-- reading the descent's RANK component is about — the rank peels once
-- per `subscribeInner` hop, and a hop is a `*All` layer entered — so
-- this is the one measure an entry invariant can state the rank
-- against.  The three clauses that carry it are read off the
-- evaluator rather than fitted to a number.
--
-- A `*All` LAYER IS WORTH ONE `suc`, because a `thru-outer` frame is
-- where a burst's payload is re-entered as a subject in its own
-- right, and that re-entry is the hop.
--
-- A `scanᵉ` IS WORTH ITS STEP FUNCTION'S LAYERS ONCE, because on any
-- ONE chain the walk enters the step function once per scan frame.
-- What that does NOT price is the layers the folds pile onto the
-- ACCUMULATOR.  That product is real and it grows with the deliveries a
-- run makes, so no measure of syntax can carry it: a term does not know
-- a count that has not happened yet.  A reading here therefore bounds
-- the subject a walk is ENTERED on, and says nothing about what the run
-- goes on to emit.
--
-- A LIST OF PAYLOADS IS WORTH THEIR MAX, NOT THEIR SUM, because a
-- burst's values are entered one at a time, each from the same frame,
-- so two payloads abreast cost what the deeper of them costs.

-- THE MAX IS NOT A TIGHTENING FOR ITS OWN SAKE, AND IT BUYS LESS THAN
-- IT WAS CHOSEN FOR.  The clause was picked so that an emitted inner
-- reads STRICTLY under its EMITTER, which is what would turn one peel
-- of the rank into a re-established invariant; a summing clause loses
-- that outright, since a step function may hand its input observable to
-- a list TWICE — the emitter reads 2, the inner it emits reads 3, and
-- the inner's own depth is 2, so the sum is over by the duplication.
-- The max decides that case and NOT the fold, and the fold is fatal:
-- the strictly-under reading is false here and false for every measure
-- of syntax, since an accumulator gains a layer per delivery and no
-- term knows how many deliveries there will be.  So what this measure
-- is for is the ENTRY side — bounding the subject a walk is entered on
-- — and the hop has to be paid out of the seed's own slack instead.
--
-- REFUTED: `Refuted.Burst-Nesting` instantiates the strictly-under
--   reading at a scan whose step re-wraps its accumulator in one merge
--   layer, and kills even the non-strict form: program 1, burst 3.

-- THE DEFER GATE TRUNCATES, AND THE μ CLAUSE IS WHY.  The measure
-- returns zero at a `deferᵉ` — a deferred body is not entered
-- synchronously, it mints its own source and is walked later as a
-- subject in its own right — so passing through the gate would buy
-- nothing on the clause it is read at.  What it would COST is the μ
-- clause, where the walk descends into `unfoldμ body` while the
-- witness keeps its rank, so the bound needs the measure not to grow
-- under unfolding — and unfolding substitutes the whole `μᵉ` term at
-- every guarded occurrence.  With the gate at zero both sides read
-- the body's own reading and the clause is an EQUALITY; passing
-- through, a body naming itself twice under a `*All` doubles the
-- measure per unfold and no bound survives.  Same design as the
-- synchronous size, which truncates at the gate for the same reason,
-- and it is the whole reason this measure reaches where a size bound
-- on the term cannot.

-- THE MEASURE IS RAW, AND ITS TWO PREDECESSORS DIED OF NOT BEING SO.
-- The first read a fold count off the width family at the
-- UNSUBSTITUTED source, where a payload variable weighs nothing, so
-- two programs differing only in how many literals a map consumed
-- shared one bound against depths of 4 and 8.  The second took the
-- count as a PARAMETER and multiplied by it — and any count worth
-- supplying is defined off the recurrence it is meant to bound, so
-- the parameter moves with the instant while a preservation step
-- prices its increment at the old one.  A raw layer count has no
-- parameter to move.

-- THE `input` CLAUSE CONTRIBUTES NOTHING, AND A DESCENDING ONE IS
-- STRUCTURALLY DEAD.  Descending into the slot definition on slot
-- fuel with a visited set does not work here, because a consumer
-- fixes that fuel at the slot COUNT, which is a variable: the clause
-- never reduces, and the parent has no more fuel than the child it
-- would recurse into, so there is no inequality to prove even in
-- principle.  So a slot's nesting is charged where the slots are —
-- which the root seeding already does, since it adds the slot
-- telescope's own size to the rank it seeds.
--
-- DEAD ROUTE: charging a slot's nesting by the number of slots.  The
--   count is a variable in the consumer, so the descending clause
--   never reduces and the child gets no less fuel than the parent.
-- RECOVERY: git show
--   919f115:agda/src/Verify-Budget-Sufficient/Nest-Depth-Size.agda
--   restores `nestDᵛ`'s pointwise bound by a value size, proven and
--   gas-free.
--   Nothing spends it while the run's reading is seeded from the store
--   rather than compared against a size, which is what the value arm
--   below is for.
------------------------------------------------------------------
module Rx.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat  using (ℕ; suc; _+_; _⊔_)

open import Rx.Exp using (Ctx; Ty; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

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
  nestDᵉ (mergeAllᵉ lim e)   = suc (nestDᵉ e)
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
-- the MAX of its components for the same reason a payload list does —
-- they are entered separately, from the same frame.
--
-- IT IS WHAT LETS A MEASURE READ THE RUN AND NOT THE PROGRAM.  A store
-- holds values rather than terms, and an accumulator a fold hands back
-- is a value that grows once per delivery; no reading of the program
-- reaches it, and the arm at `obs` is the whole of the bridge.
nestDᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
nestDᵛ unitᵗ    _        = 0
nestDᵛ boolᵗ    _        = 0
nestDᵛ natᵗ     _        = 0
nestDᵛ (s ×ᵗ t) (a , b)  = nestDᵛ s a ⊔ nestDᵛ t b
nestDᵛ (s +ᵗ t) (inj₁ a) = nestDᵛ s a
nestDᵛ (s +ᵗ t) (inj₂ b) = nestDᵛ t b
nestDᵛ (obs t)  e        = nestDᵉ e


