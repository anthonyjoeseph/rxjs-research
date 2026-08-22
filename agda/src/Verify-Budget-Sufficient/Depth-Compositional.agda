------------------------------------------------------------------
-- THE SUBSCRIBE-SIDE DEPTH BOUND, in the tree's own depth currency.
--
-- WHAT THIS MODULE WAS, AND WHY ALMOST ALL OF IT IS GONE.  It used to
-- carry `depthCap` — a linear sum of syntactic measures read at the
-- subject expression — together with a 16-clause induction
-- (`depth-compositional-go`), seven `emit-*` leaves, the store measure
-- `storeNestMax` and its helpers, and the exported widening
-- `cap-≤-store`.  All of it was the decomposition of a FALSE
-- STATEMENT, refuted 2026-08-22 at the exported conclusion and not
-- merely at a leaf, and it was deleted rather than repaired.  The
-- findings that outlive it are below; the code is in git.
--
-- -- RECOVERY: git show 725296e:agda/src/Verify-Budget-Sufficient/Depth-Compositional.agda
-- restores the whole nesting face — `depthCap`, `depthCapN`, the
-- 16-head induction, the `emit-*` leaves, `emit-cap`, `depth-μ-bound`,
-- `depth-subst-guarded`, `storeNestMax`, `cap-≤-store`; its measure
-- `Rx.Nest-Depth`; its tower arithmetic
-- `Verify-Budget-Sufficient.Nest-Tower`; and the ten evidence files
-- that could no longer be STATED once it went (Refuted.Depth-Comp,
-- .Depth-Nest, .Depth-Conn, .Depth-Chain, .Emit-Map, .Emit-Scan;
-- Probed.Depth-All, .Depth-Mu, .Emit-Cap, .Nest-Depth).
--
-- ⚠ WHAT WAS REFUTED, AND IT IS THE PART TO READ BEFORE PROPOSING A
-- MEASURE.  The cap was `nestDᵉ b + pathNestD κ` plus a store term.
-- The argument for dropping its size term was that an emitted inner
-- can be arbitrarily LARGER than its emitter (a scan whose step
-- re-wraps its accumulator) but never more deeply NESTED, "because
-- that measure's product term charges one re-wrap per delivered
-- payload precisely to cover this."  IT CHARGES NOTHING, BECAUSE IT
-- CHARGES AT THE WRONG TERM: the product is `outWᵉ src * nestDᵗ f`,
-- and `outWᵉ` is read at the UNSUBSTITUTED source, where a bare
-- payload variable is 0.  Put the payload variable in a scan's SOURCE,
-- re-wrap the accumulator in the step, and stack two `*All` layers so
-- the walk descends into what the scan emits: `depthE` read FOUR
-- against a cap of THREE.
--
-- AND THE GAP IS THE PAYLOAD COUNT, so no constant repair reaches it —
-- widening the map's source from three literals to seven took the
-- depth 4 → 8 with the cap at 3 in both.  The cap is read off the
-- SYNTAX; the depth is the count the RUN delivers; that count is a
-- WIDTH, and no syntactic term bounds it.
--
-- AND RESTORING `sizeᵉ` IS REFUTED TOO, BY DEGREE RATHER THAN BY A
-- CONSTANT, which is what settled it: `sizeᵉ b + nestDᵉ b + pathLen κ
-- + storeNestMax` read 56 where `depthE` read 70.  A scan whose step
-- merges its accumulator with a CONSTANT emitter grows its emission
-- count by a constant per tick, so the total over the scan's own
-- emissions is QUADRATIC in the tick count while every term of that
-- bound is linear in it.  The paired row two ticks earlier sits UNDER
-- the bound (35 against 52) deliberately — a crossing is a difference
-- in degree, which no re-weighting of a syntactic sum survives.
--
-- AND ITERATING ON THE GAS IS NOT THE ANSWER, which is worth saying
-- because it is the first thing the shape suggests.  Gas is the one
-- index that moves the right way at a descent — the `gs` clause is the
-- only entry into a payload and it peels one — so a cap iterated once
-- per unit of gas closes the burst arm structurally.  It is dead all
-- the same: `budgetAt-gs-pad` (Burst-Walk) exhibits the budget as a
-- gas TOWER at a height above `capsH`'s own, and anything iterated per
-- unit of gas is larger still.  A cap must be SMALLER than the gas to
-- be spendable, which rules out the whole family.
--
-- ⚠ AND FIVE REFUTATIONS CAME OUT OF ONE REGION, which is the
-- convergence test's STOP CONDITION and not an invitation to
-- subdivide again: `emit-map` as stated, `emit-scan` as stated, the
-- occurrence repair, the cap itself, and the size-restored export.
-- Every one was an attempt to keep a bound on `depthE` TIGHT — a
-- linear sum of syntactic measures, read at the subject.  THE
-- TIGHTNESS IS THE MECHANISM ERROR, and the precedent against it was
-- already in this proof one module away: `capsBase` carries
-- `entryCeil`, and `ceilᵉ` is a deliberately GENEROUS ceiling — a
-- recursive ⊔ of every node's five width measures with its children's,
-- joined with the slot telescope's.  Its own comment says why: "the
-- five static width measures TOWER in the syntax and no closed bracket
-- on them exists that is worth proving", and reading them "costs
-- nothing: the height is never normalised".  The width face did not
-- bracket its measures; it read them, and paid for the generosity with
-- tower growth it already had.
------------------------------------------------------------------

module Verify-Budget-Sufficient.Depth-Compositional where

open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (⊔-lub)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Rx.Prim using (Gas; Id; Tick; InstEmit)
open import Rx.Exp using (Ctx; Closed; Val; sizeᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeId; Path; Stream; _↠_; map-f; scan-f; take-f;
  from-inner; thru-outer; root; share-sink; splitEvents; stepFrame)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthBurst)

------------------------------------------------------------------
-- THE PATH MEASURE — the one arc on a path that a subscribe actually
-- spends.  `depthFrame` returns 0 on map-f, scan-f and take-f
-- definitionally, so counting all frames makes a cap pay for descent
-- steps that cost nothing.  Only `thru-outer` charges.
--
-- `from-inner` charges NOTHING here, and it is the one clause worth
-- justifying: the arc it funds (`depthFinC`'s completion `suc`) is
-- reached only through `depthFold`, and its contents are the queued
-- observables the node half already charges.  A unit here would double
-- charge the layer the `thru-outer` above it already bought.
------------------------------------------------------------------

pathNestD : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathNestD root                    = 0
pathNestD (share-sink i)          = 0
pathNestD (map-f _ ↠ p)           = pathNestD p
pathNestD (scan-f _ _ ↠ p)        = pathNestD p
pathNestD (take-f _ ↠ p)          = pathNestD p
pathNestD (from-inner _ _ _ ↠ p)  = pathNestD p
pathNestD (thru-outer _ _ ↠ p)    = suc (pathNestD p)

------------------------------------------------------------------
-- THE FRAME BURSTS THAT COST NOTHING.  `depthFrame` returns 0
-- definitionally for take-f, so `depthBurst` over that frame is a fold
-- of `0 ⊔ IH` — a three-line list induction.
--
-- -- RECOVERY: git show 725296e:agda/src/Verify-Budget-Sufficient/Depth-Compositional.agda
-- restores `burst-mapf-zero` and `burst-scf-zero`, the map-f and
-- scan-f siblings of this proof (same induction, same shape).  They
-- were unwired when the nesting face went, since their only consumer
-- was its induction; a depth induction in any currency will want them
-- back at its map and scan clauses.
------------------------------------------------------------------

burst-takef-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (take-f nid) κ stream sched st ≤ 0
burst-takef-zero fuel bid now nid κ [] sched st = z≤n
burst-takef-zero {Γ = Γ} {s = s} fuel bid now nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-takef-zero fuel bid now nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ s} (InstEmit.events em)
  r      = stepFrame fuel bid now (take-f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

------------------------------------------------------------------
-- THE RESTATEMENT, AND IT IS A SWAP RATHER THAN A REPAIR.
--
-- A search for the substitution lemma the refuted cap needed found
-- `hopDᵉ` (Rx.Hop-Depth) instead — the accounting that cap was
-- reaching for, written correctly.  `suc` per `*All` layer, the same as
-- there; but `mapᵉ f e` charges `hopDᵗ f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ e`,
-- MULTIPLYING the source's depth by the template's occurrence count
-- because "the source's depth lands at every Θ-var occurrence" — which
-- is precisely what `nestDᵗ f + nestDᵉ b` does not do; and
-- `scanᵉ f z e` charges `(2 + pmᵗ V 0 f) ^ V * (…)`, an exponential in
-- the refold bound rather than a product with the source's width, so
-- the quadratic gadget cannot outrun it.  Its `input` clause reads a
-- slot ENVIRONMENT `η i`, and its own header records the constant-0
-- version as machine-REFUTED — the same refutation the dead cap's slot
-- half was rebuilt around, arrived at independently.
--
-- IT IS ALSO ALREADY CLOSED UNDER SUBSTITUTION, WHICH IS THE WHOLE
-- DIFFICULTY: `hopD-sub-spnᵉ` (Hop-Spine-Sub) bounds
-- `hopDᵉ V η (subΘExp Θloc σ e)` under an `EnvPlug` hypothesis about
-- the environment, `applyFn-hopSpn` (Hop-Spine-Step) is the emitted-
-- payload instance, `hopD-unfoldμ` gives the μ clause, `hopD-η-congᵉ`
-- the slot-cut congruence and `slotHop-fix` the slot half.  So the
-- nesting mirror `nest-subΘ` should never be written: it is
-- `hopD-sub-spnᵉ`, proven.  The `emit-*` leaf set is likewise already
-- discharged in this currency — `valHopSpn?` is a hereditary value
-- invariant that `applyFn-hopSpn` preserves.
--
-- AND THE TWO MEASURES AGREE AT `deferᵉ` WHERE THE OLD ONE DID NOT.
-- `depthE` reads a defer as 0 — a defer's body is a fresh subscription
-- at a later tick, not part of this one — and `hopDᵉ` cuts there for
-- its own reason (Δᵍ vars are reachable only under a defer).  `nestDᵉ`
-- descended instead.  Harmless there, and one more place the two were
-- not the same measure.
--
-- AND THE CONSUMER ALREADY ASKS IN THIS CURRENCY, which is the part
-- that says the swap is a reinvention undone and not a coincidence.
-- `subscribeE-wet-via-caps` (Caps-Bridge) carries, in ONE signature, a
-- gas hypothesis stated over `hopDᵉ Ŝ (slotHop Ŝ sl) b` and the
-- `depOK` hypothesis `depthE g b κ id now sched st ≤ capsH e sl id`
-- that this module exists to discharge — same `sl`, same
-- `Ŝ = sizeCapAt e sl (suc id)`, adjacent lines.  So `V` and `η` do
-- not have to be invented: `V`'s two nameable instantiations coincide,
-- the consumer's `sizeCapAt e sl (suc id)` and `suc (entryCeil n ins
-- e)`, which is the `M` the tower arithmetic is stated at.
-- `make dup-check` could not see that: the two statements are not the
-- same fact, only the same job.
--
-- -- PROBED 2026-08-22: DOMINATION AT THE FOUR REFUTATION WITNESSES.
-- `hopDᵉ` dominates `depthE` at every program that killed the
-- predecessor — the two small programs at a refold bound of one (depth
-- 4 and 8), and both rows of the quadratic gadget at four (35 and 70).
-- That is evidence reaching the RISKY region rather than a degenerate
-- row, because those four programs ARE the region.
--
-- ⚠ AND IT IS NOT TRUE FOR EVERY `V` — REFUTED 2026-08-22 as first
-- stated (`Refuted.Depth-Hop`).  `hopDᵉ`'s scan clause is
-- `(2 + pmᵗ V 0 f) ^ V * (…)`, so at `V = 0` the factor is 1 and a scan
-- is charged its step, seed and source with nothing for refolding.  The
-- witness is the CHEAP one — the seven-literal program, whose widening
-- `hopDᵉ` charges 0 for at every `V`, so only the refold factor could
-- ever pay for its depth of 8, and at `V = 0` there is no factor.  It
-- needs twenty units of gas and a program of constant size; the
-- quadratic gadget is not required.  The two
-- conditions below are that refutation's repair and not a weakening —
-- the unconditional form is false, so the conditioned one replaces it —
-- and they are the shape every other hop consumer in this tree already
-- uses.  `thruOuter-face-core-go` takes `2 ≤ C` with `sizeᵉ o ≤ C`, and
-- `subscribeE-wet-via-caps` reads `hopDᵉ Ŝ (slotHop Ŝ sl) b` at
-- `Ŝ = sizeCapAt e sl (suc id)`, where `2≤sizeCapAt` and
-- `size≤sizeCapAt` are both PROVEN — which is why the root consumer can
-- discharge both without a new leaf.
--
-- ⚠ AND `sizeᵉ b ≤ V` IS THE CONDITION THE BURST ARM WILL TEST, which is
-- worth writing down before it is ground: `b` shrinks at every
-- structural descent, so the condition is inherited for free there, but
-- at the burst arm `b` becomes an emitted PAYLOAD whose size may EXCEED
-- its emitter's — that is the difficulty the whole face is about.  The
-- caps machinery is what re-establishes it (`applyFn-iterSize` bounds an
-- emitted payload's size by the cap), which is why `V` is a size CAP and
-- not `sizeᵉ e`.  If that arm cannot re-establish it from what the
-- statement carries, the finding is a caps hypothesis — the shape
-- `cascade-depth-capsH` already has — and not a smaller `V`.
--
-- ⚠ AND NOTHING WIDER: the four rows are all at the ROOT path, with an
-- empty store and no slot telescope, and they say nothing about the
-- `input` clause — which is where the predecessor's first two
-- refutations lived.  FALSITY class until it is probed off the root.
--
-- ⚠ AND THE CONDITIONS ARE NOT KNOWN TO BE TIGHT — the refutation kills
-- `V = 0` and nothing more.  `V = 1` was MEASURED to hold on the same
-- program, with no margin whatever (the green row is in
-- `Probed.Depth-Hop`), so `2 ≤ V` is the tree's idiom rather than a
-- boundary this evidence found.  Do not weaken either condition on the
-- strength of the refutation alone.
-- The predecessor's own μ receipt transfers as the shape to re-run
-- first: a one-layer guarded body gave depth 1 and a two-layer body 2,
-- measured at two gas values twenty apart with the store held at 0 by
-- an all-`scripted` slot, so depth tracks the BODY's own nesting and
-- nothing else — but no `mergeAllᵉ`-free guard, no nested `μᵉ`, and no
-- shared slot was ever covered.
------------------------------------------------------------------

postulate
  depth-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ V → sizeᵉ b ≤ V →
    depthE g b κ bid now sched st
      ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ
