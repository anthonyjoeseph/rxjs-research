------------------------------------------------------------------
-- THE SUBSCRIBE-SIDE DEPTH BOUND, in the tree's own depth currency.

-- WHAT THIS MODULE WAS, AND WHY ALMOST ALL OF IT IS GONE.  It used to
-- carry `depthCap` — a linear sum of syntactic measures read at the
-- subject expression — together with a 16-clause induction
-- (`depth-compositional-go`), seven `emit-*` leaves, the store measure
-- `storeNestMax` and its helpers, and the exported widening
-- `cap-≤-store`.  All of it was the decomposition of a FALSE
-- STATEMENT, refuted at the exported conclusion and not
-- merely at a leaf, and it was deleted rather than repaired.  The
-- findings that outlive it are below; the code is in git.
--
-- RECOVERY: `git show 725296e:agda/src/Verify-Budget-Sufficient/Depth-Compositional.agda`
--   restores the whole nesting face — `depthCap`, `depthCapN`, the
--   16-head induction, the `emit-*` leaves, `emit-cap`, `depth-μ-bound`,
--   `depth-subst-guarded`, `storeNestMax`, `cap-≤-store`; its measure
--   `Rx.Nest-Depth`; its tower arithmetic
--   `Verify-Budget-Sufficient.Nest-Tower`; and the ten evidence files
--   that could no longer be STATED once it went (Refuted.Depth-Comp,
--   .Depth-Nest, .Depth-Conn, .Depth-Chain, .Emit-Map, .Emit-Scan;
--   Probed.Depth-All, .Depth-Mu, .Emit-Cap, .Nest-Depth).

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

-- AND THE GAP IS THE PAYLOAD COUNT, so no constant repair reaches it —
-- widening the map's source from three literals to seven took the
-- depth 4 → 8 with the cap at 3 in both.  The cap is read off the
-- SYNTAX; the depth is the count the RUN delivers; that count is a
-- WIDTH, and no syntactic term bounds it.

-- AND RESTORING `sizeᵉ` IS REFUTED TOO, BY DEGREE RATHER THAN BY A
-- CONSTANT, which is what settled it: `sizeᵉ b + nestDᵉ b + pathLen κ
-- + storeNestMax` read 56 where `depthE` read 70.  A scan whose step
-- merges its accumulator with a CONSTANT emitter grows its emission
-- count by a constant per tick, so the total over the scan's own
-- emissions is QUADRATIC in the tick count while every term of that
-- bound is linear in it.  The paired row two ticks earlier sits UNDER
-- the bound (35 against 52) deliberately — a crossing is a difference
-- in degree, which no re-weighting of a syntactic sum survives.

-- AND ITERATING ON THE GAS IS NOT THE ANSWER, which is worth saying
-- because it is the first thing the shape suggests.  Gas is the one
-- index that moves the right way at a descent — the `gs` clause is the
-- only entry into a payload and it peels one — so a cap iterated once
-- per unit of gas closes the burst arm structurally.  It is dead all
-- the same: `budgetAt-gs-pad` (Burst-Walk) exhibits the budget as a
-- gas TOWER at a height above `capsH`'s own, and anything iterated per
-- unit of gas is larger still.  A cap must be SMALLER than the gas to
-- be spendable, which rules out the whole family.

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

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (⊔-lub; ≤-trans; m≤n+m; m≤n⊔m;
  *-identityˡ; *-monoˡ-≤; +-monoˡ-≤; +-monoʳ-≤; +-suc; ≤-reflexive; n≤1+n; ≤ᵇ⇒≤)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (lookup)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Decide using (∧-trueˡ; ∧-trueʳ; ∧-intro; T-to)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit; InstEvent;
  value; init; close; handoff; complete)
open import Rx.Exp using (Ctx; Closed; Val; Exp; Fn; Tm; _×ᵗ_; natᵗ; obs;
  syncSizeᵉ; unfoldμ; evalTm;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slot; Slots; slotsSize; scripted; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeId; Path; Stream; AllOp; NodeState; _↠_; map-f; scan-f; take-f;
  from-inner; thru-outer; root; share-sink; splitEvents; stepFrame; subscribeE; mintNode;
  installNode; take-st; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; thruConsume; switchKill;
  lookupNode; merge-st; concat-st; switch-st; exhaust-st; scan-st)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; pmᵗ; hopD-unfoldμ)
open import Rx.Slot-Hop using (slotHop; slotHop-fix)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthBurst; depthAll; depthTake; depthSlot; depthWalk;
  depthConsume; depthConsumeS; depthInner)
open import Verify-Budget-Sufficient.Measures
  using (syncSize-unfoldμ; syncSize≤sizeᵉ; slotDef-size; 1≤pow;
  burstHopD?; hopDev?)
open import Verify-Budget-Sufficient.Hop-Burst-Face
  using (burstSync?; syncEv?; subscribeE-hops)
open import Verify-Budget-Sufficient.Keeps-Ring
  using (KeepsC; subscribeE-slots; stepFrame-keeps; thruConsume-keeps;
  switchKill-keeps)

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
-- THE THREE FRAME BURSTS THAT COST NOTHING.  `depthFrame` returns 0
-- definitionally for map-f, scan-f and take-f alike, so `depthBurst`
-- over any of the three is a fold of `0 ⊔ IH` — one list induction per
-- frame, and the reason `depth-hop`'s chain clauses need no arithmetic
-- on their burst disjunct at all: it is bounded by zero, so `⊔-lub`
-- closes that side with `z≤n` whatever the subject's hop turns out to
-- be.  The `from-inner` and `thru-outer` frames are NOT here, and that
-- is the whole content of the split: those two reach `depthReact` and
-- `depthWalk`, which is where the depth actually lives.
------------------------------------------------------------------

burst-mapf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] s u) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (map-f f) κ stream sched st ≤ 0
burst-mapf-zero fuel bid now f κ [] sched st = z≤n
burst-mapf-zero {Γ = Γ} {u = u} fuel bid now f κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-mapf-zero fuel bid now f κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (map-f f) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

burst-scf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (scan-f f nid) κ stream sched st ≤ 0
burst-scf-zero fuel bid now f nid κ [] sched st = z≤n
burst-scf-zero {Γ = Γ} {u = u} fuel bid now f nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-scf-zero fuel bid now f nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (scan-f f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

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
------------------------------------------------------------------
-- THE WALK ARM'S SUBJECT, NAMED.  A `thru-outer` frame's burst is the
-- one `depthBurst` this face cannot bound by zero, and its bound has to
-- be stated at the SUBSCRIBE'S OWN OUTPUTS rather than over an
-- arbitrary stream: an inner delivered by some other stream has a depth
-- unrelated to `b`, so the general form is FALSE.  This abbreviation is
-- what pins the three arguments to the subscribe that produced them.
------------------------------------------------------------------

allBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  → Gas → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ u t
  → Id → Tick → (sched : Sched Γ) → EvalSt e → ℕ
allBurst g op ns b κ bid now sched st =
  depthBurst g bid now (thru-outer op nid) κ
    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀

------------------------------------------------------------------
-- THE WALK IS THE ONLY GAP, AND IT IS A FOLD.  Of `depthE`'s four heads
-- only the `thru-outer` burst is one: the other three reduce to this
-- face's own induction plus arithmetic, and the three chain frames'
-- bursts are bounded by zero.  A `thru-outer` burst reaches `depthWalk`,
-- which SUBSCRIBES every emitted inner — so the hop edge's `suc` has to
-- be earned against payloads of `b` rather than read off a clause of the
-- measure.
--
-- SO THE FOLD IS WRITTEN OUT rather than asserted, which is what makes
-- its arithmetic checked: `depthBurst` peels an emission, `depthWalk`
-- peels a payload, `depthConsume` picks the operator's branch and
-- `depthInner` peels the gas and re-enters `depth-hop`.  Each of those
-- is a head of the block below, and what the fold cannot supply itself
-- is ONE leaf: the payload condition.  Everything else it needs about
-- the schedule the `Keeps` ring already proves.
------------------------------------------------------------------

-- THE FOLD CARRIES ITS CURRENCY AT A FIXED SLOT VECTOR, so each stepper
-- owes one equation — and it costs NO LEAF, because the whole subscribe
-- clique already carries the fact through the `Keeps` ring: one `slotsEq`
-- projection per stepper, at the exact tuple position each fold reads.
-- `mintNode` and the node bump inside `depthInner` need not even that,
-- since a record update on another field reduces.
-- THE SOURCE CONDITION, AS A PREDICATE ON THE STREAM.  The hop half is
-- `burstHopD?`, which .Measures already has and the walk face already
-- lands; the re-entry also wants `depth-hop`'s own source condition at
-- each payload, and stating it the same way is what lets both halves
-- travel through the fold as `all`s over one list — so a tail is a
-- projection instead of a re-establishment.
-- the frame is handed the VALUES and both predicates speak of EVENTS, so
-- one induction over the event list moves each of them across the split
split-hop : ∀ {n} {Γ : Ctx n} {u} {A : Set} (V : ℕ) (η : Fin n → ℕ) (d : ℕ)
  (evs : List (InstEvent (Val Γ (obs u)))) →
  all (hopDev? V η d) evs ≡ true →
  all (λ o → hopDᵉ V η o ≤ᵇ d)
      (proj₁ (splitEvents {Γ = Γ} {u = obs u} {A = A} evs)) ≡ true
split-hop V η d []               h = refl
split-hop V η d (value v   ∷ es) h =
  ∧-intro (∧-trueˡ h) (split-hop V η d es (∧-trueʳ h))
split-hop V η d (init _    ∷ es) h = split-hop V η d es (∧-trueʳ h)
split-hop V η d (close _ _ ∷ es) h = split-hop V η d es (∧-trueʳ h)
split-hop V η d (handoff _ ∷ es) h = split-hop V η d es (∧-trueʳ h)
split-hop V η d (complete  ∷ es) h = split-hop V η d es (∧-trueʳ h)

split-sync : ∀ {n} {Γ : Ctx n} {u} {A : Set} (V : ℕ)
  (evs : List (InstEvent (Val Γ (obs u)))) →
  all (syncEv? V) evs ≡ true →
  all (λ o → syncSizeᵉ o ≤ᵇ V)
      (proj₁ (splitEvents {Γ = Γ} {u = obs u} {A = A} evs)) ≡ true
split-sync V []               h = refl
split-sync V (value v   ∷ es) h =
  ∧-intro (∧-trueˡ h) (split-sync V es (∧-trueʳ h))
split-sync V (init _    ∷ es) h = split-sync V es (∧-trueʳ h)
split-sync V (close _ _ ∷ es) h = split-sync V es (∧-trueʳ h)
split-sync V (handoff _ ∷ es) h = split-sync V es (∧-trueʳ h)
split-sync V (complete  ∷ es) h = split-sync V es (∧-trueʳ h)

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

-- AND THE TWO MEASURES AGREE AT `deferᵉ` WHERE THE OLD ONE DID NOT.
-- `depthE` reads a defer as 0 — a defer's body is a fresh subscription
-- at a later tick, not part of this one — and `hopDᵉ` cuts there for
-- its own reason (Δᵍ vars are reachable only under a defer).  `nestDᵉ`
-- descended instead.  Harmless there, and one more place the two were
-- not the same measure.

-- ⚠ AND IT IS NOT TRUE FOR EVERY `V` — REFUTED as first
-- stated (`Refuted.Depth-Hop`).  `hopDᵉ`'s scan clause is
-- `(2 + pmᵗ V 0 f) ^ V * (…)`, so at `V = 0` the factor is 1 and a scan
-- is charged its step, seed and source with nothing for refolding.  The
-- witness is the CHEAP one — the seven-literal program, whose widening
-- `hopDᵉ` charges 0 for at every `V`, so only the refold factor could
-- ever pay for its depth of 8, and at `V = 0` there is no factor.  It
-- needs twenty units of gas and a program of constant size; the
-- quadratic gadget is not required.  The `V`
-- conditions below are that refutation's repair and not a weakening —
-- the unconditional form is false, so the conditioned one replaces it —
-- and they are the shape every other hop consumer in this tree already
-- uses.  `thruOuter-face-core-go` takes `2 ≤ C` with `sizeᵉ o ≤ C`, and
-- `subscribeE-wet-via-caps` reads `hopDᵉ Ŝ (slotHop Ŝ sl) b` at
-- `Ŝ = sizeCapAt e sl (suc id)`, where `2≤sizeCapAt` and
-- `size≤sizeCapAt` are both PROVEN — which is why the root consumer can
-- discharge both without a new leaf.

-- AND A MID-RUN STATE, REACHED BY RUNNING: the state the root
-- subscribe RETURNS — registry, node table and delivered set all
-- populated by the evaluator — gives 4 against 4, the same answer as
-- `st-init` does.  That is the finding rather than a coincidence: the
-- store the measure is read against does not move the depth.  The
-- state is PROJECTED out of `subscribeE`, never written as a record
-- update, so it is one the evaluator can actually be in.

-- THE REGION THE PROBE SERIES REACHED IS NAMEABLE IN FULL, which is what
-- makes its silence about the two blocks below readable rather than
-- reassuring: every clause of `hopDᵉ`; all
-- four `*All` operators; both `Slot` constructors; a two-slot
-- stratified telescope at stage 1; three of three `Path`
-- constructors; a payload-regrowing scan, which is the shape that
-- refuted the predecessor; and a populated store.  Thirty-seven rows,
-- and TIGHT — nine of them with no margin at all, which is what
-- separates this from a measure that is merely large.  The series is
-- also known to be able to kill this statement, having done it: the
-- ∀ V form died at `V = 0` on a program from the same file.

-- AND THE MIRROR IS `subscribeE-caps` (.Subscribe-Face), PROVEN: a
-- clause-by-clause induction over exactly this `b`, at exactly these
-- indices, which already carries a depth bound as a parameter — so it
-- answers "which clause splits on what, and at which fuel" without
-- any of it being re-decided here.  `sub-charge` is NOT the mirror,
-- despite reading like one at the type: it is a five-line wrapper that
-- instantiates that parameter at `depthE g b κ bid now sched st` and
-- projects.  Diff the ARGUMENTS against it, not the statements.

-- ⚠ AND THE MIRROR DOES NOT MAKE THIS GRINDABLE.  What it settles is
-- the clause skeleton; what it does not settle is the burst arm, where
-- the caps twin spends caps machinery and this side needs an EMITTED
-- payload's hop bounded by its emitter's — a different fact, and the
-- one design decision left in the row.

-- ⚠ WHAT WOULD RAISE THE CLASS AGAIN, and what is still unreached: a state
-- deep inside a CASCADE rather than one subscribe in, since the
-- gadget's mid-run state does not normalise (7.9 GB in six minutes —
-- the boundary is recorded in the probe, do not pay for it twice);
-- `hopDᵗ`'s `caseᵗ` clause, the one place the measure takes a ⊔ of two
-- branches and multiplies by a scrutinee; and a `V` between 2 and the
-- refuted 0, since `2 ≤ V` is the tree's idiom and not a boundary this
-- evidence found.

-- ⚠ AND `pathNestD κ` IS SLACK ON EVERY SUBSCRIBE-SIDE ARM.  The probe
-- noticed it — `depthE` returned 0 at every non-root path tried, so no
-- row needs the term at all — and reading `depthE`'s clauses says why,
-- which is the part that matters for the grind.

-- `depthFrame` has the only two `suc`s in the mirror: a `thru-outer`
-- frame pays one for its walk, and a `concatAll` finish pays one for
-- its drain.  `depthE` only ever hands `depthBurst` THE FRAME IT JUST
-- INSTALLED — `map-f`, `scan-f`, `take-f`, `thru-outer`, never
-- `from-inner` — so the drain arc is not reachable from this side at
-- all, and the walk arc is entered exactly where `hopDᵉ`'s own `*All`
-- clause has already contributed its `suc`.  Every arm therefore
-- closes with `pathNestD κ` untouched on both sides: the `*All` arms
-- against `suc (hopDᵉ b)`, the frame arms against `hopDᵉ`'s
-- multiplier, the connect arm against `slotHop-fix`, and the μ arm
-- against `hopD-unfoldμ`.  What the walk arm needs instead is that an
-- EMITTED inner has hop at most its emitter's, which is the value
-- invariant and not a path fact.

-- ⚠ SO THE TERM STAYS, AND DELIBERATELY.  Dropping it strengthens the
-- statement, and strengthening a FALSITY row is the wrong direction
-- under de-risk: the slack costs nothing to carry (no arm has to
-- discharge it) and it is the one unit of room available if a burst
-- arm turns out to need one.  Revisit only once the burst arm is
-- ground and the room is provably unspent — and note that a
-- path-shaped term IS load-bearing on the DELIVERY side, where
-- `depthFold` walks κ frame by frame and pays `depthFrame` at each,
-- which is why this currency has the term in it at all.

-- ⚠ AND THE CONDITIONS ARE NOT KNOWN TO BE TIGHT — the ∀ V refutation
-- kills `V = 0` and nothing more.  `V = 1` was MEASURED to hold on the same
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





-- THE ARM'S OWN INSTANTIATION, and it needs no arithmetic: `mintNode`
-- writes `nextNode` and `installNode` writes the state's node map, so
-- the slot vector the currency is read at is the caller's own by
-- reduction and the equation is `refl`.  What the specialisation fixes
-- is the path — the outer frame the walk is about — and nothing else.
allBurst-hops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → syncSizeᵉ b ≤ V → slotsSize (Sched.slots sched) ≤ V →
  let nid    = proj₁ (mintNode sched)
      sched₁ = proj₂ (mintNode sched)
      st₀    = installNode nid ns st
      r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
      η      = slotHop V (Sched.slots sched)
  in (burstHopD? V η (hopDᵉ V η b) (proj₁ r) ≡ true)
   × (burstSync? V (proj₁ r) ≡ true)
allBurst-hops V g op ns b κ bid now sched st 2≤V szB slB =
  subscribeE-hops V g b (thru-outer op nid ↠ κ) bid now
    (Sched.slots sched) sched₁ st₀ 2≤V szB slB refl
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st


------------------------------------------------------------------
-- THE TWO MONOTONICITY STEPS THE CHAIN EDGES NEED.  A `mapᵉ` and a
-- `scanᵉ` both recurse into their source at the SAME path depth, so the
-- clause closes as soon as the source's own hop is at most the
-- subject's — which is arithmetic on `hopDᵉ`'s clause and not a fact
-- about the evaluator.  `takeᵉ` needs no step at all: `hopDᵉ` is EQUAL
-- on a take and its source.
------------------------------------------------------------------

hopD-map-mono : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ) (η : Fin n → ℕ)
  (f : Fn Γ Δᵍ Δ Θ s u) (e : Exp Γ Δᵍ Δ Θ s) →
  hopDᵉ V η e ≤ hopDᵉ V η (mapᵉ f e)
hopD-map-mono V η f e =
  ≤-trans
    (subst (_≤ (pmᵗ V 0 f ⊔ 1) * hopDᵉ V η e)
           (*-identityˡ (hopDᵉ V η e))
           (*-monoˡ-≤ (hopDᵉ V η e) (m≤n⊔m (pmᵗ V 0 f) 1)))
    (m≤n+m ((pmᵗ V 0 f ⊔ 1) * hopDᵉ V η e) (hopDᵗ V η f))


hopD-scan-mono : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ) (η : Fin n → ℕ)
  (f : Fn Γ Δᵍ Δ Θ (u ×ᵗ s) u) (z : Tm Γ Δᵍ Δ Θ u) (e : Exp Γ Δᵍ Δ Θ s) →
  hopDᵉ V η e ≤ hopDᵉ V η (scanᵉ f z e)
hopD-scan-mono V η f z e =
  ≤-trans
    (m≤n+m (hopDᵉ V η e) (hopDᵗ V η f + hopDᵗ V η z))
    (subst (_≤ (2 + pmᵗ V 0 f) ^ V * S)
           (*-identityˡ S)
           (*-monoˡ-≤ S (1≤pow (suc (pmᵗ V 0 f)) V)))
  where S = hopDᵗ V η f + hopDᵗ V η z + hopDᵉ V η e

-- every chain constructor charges `syncSizeᵉ` a `suc` over a sum whose
-- RIGHT summand is the source, so one step serves the map, take and scan
-- clauses alike — and it is stated over bare naturals precisely so that
-- `scanᵉ`'s two-summand left half needs no separate case
sync-src : ∀ {a b V} → suc (a + b) ≤ V → b ≤ V
sync-src {a} {b} h = ≤-trans (≤-trans (m≤n+m b a) (n≤1+n (a + b))) h

------------------------------------------------------------------
-- THE HEADS, MUTUALLY.  The split is `depthE`'s own and not an
-- invented decomposition: `input` reaches `depthSlot`, `takeᵉ` reaches
-- `depthTake`, and all four `*All` constructors reach `depthAll`.  Each
-- head recurses back into `depth-hop` at a subject the CALLER made
-- structurally smaller, or — at a share connect and at a `μᵉ` re-entry —
-- at one less gas, which is why the whole block terminates on the pair.
------------------------------------------------------------------

depth-hop-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (V : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize (Sched.slots sched) ≤ V →
  depthE g (input i) κ bid now sched st
    ≤ slotHop V (Sched.slots sched) i + pathNestD κ

-- THE SLOT IS A PARAMETER, WITH ITS EQUATION BESIDE IT, and that is not
-- a convenience: `slotHop V sl i` UNFOLDS through `sl i`, so a `with` on
-- the slot rewrites the bound as well as the subject and the fixpoint no
-- longer applies to what is left.  Taking the slot as an argument keeps
-- the bound in `slotHop` form, which is the form `slotHop-fix` speaks.
--
-- At a shared slot the def is subscribed at `share-sink i`, whose
-- nesting is 0, and the fixpoint says the staged number IS that def's
-- hop — so the arm is an equality transport, with `slotDef-size` paying
-- for the def's own size condition out of the slots width.
depth-hop-slot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (V : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize (Sched.slots sched) ≤ V →
  (w : Slot Γ (toℕ i) (lookup Γ i)) → Sched.slots sched i ≡ w →
  depthSlot g i κ bid now sched st w
    ≤ slotHop V (Sched.slots sched) i + pathNestD κ

-- the count is a `natᵗ` term, so the clause splits on a VALUE the
-- subject cannot see; past that split it is the `scanᵉ` clause exactly,
-- and `hopDᵉ` being EQUAL on a take and its source is what makes the
-- source's own bound land with no monotonicity step
depth-hop-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (k : Val Γ natᵗ) →
  2 ≤ V → syncSizeᵉ b ≤ V → slotsSize (Sched.slots sched) ≤ V →
  depthTake g b κ bid now sched st k
    ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ

-- STATED AT THE `suc`, which is what makes it serve all four `*All`
-- constructors at once: `hopDᵉ` charges every one of them
-- `suc (hopDᵉ V η b)`, so the four clauses below are applications and
-- the operator is a parameter rather than four near-copies.  The outer
-- source's own disjunct is pure arithmetic — the frame charges the PATH
-- a level where the measure charges the SUBJECT one, and `+-suc` is the
-- whole content of moving between them
depth-hop-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → syncSizeᵉ b ≤ V → slotsSize (Sched.slots sched) ≤ V →
  depthAll g op ns b κ bid now sched st
    ≤ suc (hopDᵉ V (slotHop V (Sched.slots sched)) b) + pathNestD κ

depth-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → syncSizeᵉ b ≤ V → slotsSize (Sched.slots sched) ≤ V →
  depthE g b κ bid now sched st
    ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ

------------------------------------------------------------------
-- AND THE WALK'S OWN HEADS, one per layer of the fold.  Each carries
-- the slot vector as a PARAMETER with `Sched.slots sched ≡ sl` beside
-- it, which is what keeps the hop currency still while the schedule
-- moves underneath: the payload predicates are then facts about a fixed
-- `η` and a fixed list, so a tail case projects them instead of
-- re-establishing them.
------------------------------------------------------------------

depth-hop-all-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → syncSizeᵉ b ≤ V → slotsSize (Sched.slots sched) ≤ V →
  allBurst g op ns b κ bid now sched st
    ≤ suc (hopDᵉ V (slotHop V (Sched.slots sched)) b) + pathNestD κ

-- one emission at a time.  The frame charges the burst a level, so this
-- head is the ONLY one stated at `suc d` — the walk under it runs at `d`
depth-hop-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (d : ℕ) (sl : Slots Γ) (strm : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
  burstHopD? V (slotHop V sl) d strm ≡ true → burstSync? V strm ≡ true →
  depthBurst g bid now (thru-outer op nid) κ strm sched st
    ≤ suc d + pathNestD κ

-- one payload at a time, at the state the previous payload's consume
-- left behind
depth-hop-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (d : ℕ) (sl : Slots Γ)
  (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
  all (λ o → hopDᵉ V (slotHop V sl) o ≤ᵇ d) vals ≡ true →
  all (λ o → syncSizeᵉ o ≤ᵇ V) vals ≡ true →
  depthWalk g op nid κ bid now vals sched st ≤ d + pathNestD κ

-- the operator's branch: three of the four subscribe at the incoming
-- state, and switchAll reads its node first
depth-hop-consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (d : ℕ) (sl : Slots Γ) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
  (hopDᵉ V (slotHop V sl) o ≤ᵇ d) ≡ true → (syncSizeᵉ o ≤ᵇ V) ≡ true →
  depthConsume g op nid κ bid now o sched st ≤ d + pathNestD κ

-- THE NODE READ IS A PARAMETER for the reason the slot read is one: the
-- clause splits on a state the subject cannot see, and enumerating the
-- constructors is what lets the mirror's catch-all reduce to zero
depth-hop-consumeS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (nid : NodeId) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (d : ℕ) (sl : Slots Γ) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
  (hopDᵉ V (slotHop V sl) o ≤ᵇ d) ≡ true → (syncSizeᵉ o ≤ᵇ V) ≡ true →
  (nd : Maybe (NodeState Γ)) →
  depthConsumeS g nid κ bid now o sched st nd ≤ d + pathNestD κ

-- the re-entry: one gas peeled, the payload subscribed under a
-- `from-inner` frame whose nesting is the path's own, and `depth-hop`
-- back at the payload
depth-hop-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (V : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (d : ℕ) (sl : Slots Γ) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
  (hopDᵉ V (slotHop V sl) o ≤ᵇ d) ≡ true → (syncSizeᵉ o ≤ᵇ V) ≡ true →
  depthInner g op nid κ bid now o sched st ≤ d + pathNestD κ

depth-hop-input V g i κ bid now sched st 2≤V slB =
  depth-hop-slot V g i κ bid now sched st 2≤V slB (Sched.slots sched i) refl

depth-hop-slot V g  i κ bid now sched st 2≤V slB (scripted _) eq = z≤n
depth-hop-slot V g0  i κ bid now sched st 2≤V slB (shared d)   eq = z≤n
depth-hop-slot V (gs fuel) i κ bid now sched st 2≤V slB (shared d) eq =
  ≤-trans
    (depth-hop V fuel d (share-sink i) bid now sched _ 2≤V
       (≤-trans (syncSize≤sizeᵉ d)
          (≤-trans (slotDef-size (Sched.slots sched) i eq) slB))
       slB)
    (subst (λ X → X + 0 ≤ slotHop V (Sched.slots sched) i + pathNestD κ)
           (slotHop-fix V (Sched.slots sched) i eq)
           (+-monoʳ-≤ (slotHop V (Sched.slots sched) i) z≤n))

depth-hop-take V g b κ bid now sched st zero    2≤V szB slB = z≤n
depth-hop-take V g b κ bid now sched st (suc k) 2≤V szB slB =
  ⊔-lub
    (depth-hop V g b (take-f nid ↠ κ) bid now sched₁ st₀ 2≤V szB slB)
    (≤-trans (burst-takef-zero g bid now nid κ
                (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  r      = subscribeE g b (take-f nid ↠ κ) bid now sched₁ st₀

depth-hop-all V g op ns b κ bid now sched st 2≤V szB slB =
  ⊔-lub
    (≤-trans (depth-hop V g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
                2≤V szB slB)
             (≤-reflexive
                (+-suc (hopDᵉ V (slotHop V (Sched.slots sched)) b)
                       (pathNestD κ))))
    (depth-hop-all-burst V g op ns b κ bid now sched st 2≤V szB slB)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st

depth-hop V g (input i) κ bid now sched st 2≤V szB slB =
  depth-hop-input V g i κ bid now sched st 2≤V slB
-- the one-shots and the two parking constructors reach no subscribe, so
-- `depthE` is 0 there and the bound is free
depth-hop V g (ofᵉ ts)   κ bid now sched st 2≤V szB slB = z≤n
depth-hop V g emptyᵉ     κ bid now sched st 2≤V szB slB = z≤n
depth-hop V g (deferᵉ _) κ bid now sched st 2≤V szB slB = z≤n
depth-hop V g (varᵉ ())  κ bid now sched st 2≤V szB slB
-- a chain edge: the source at ONE MORE FRAME but the same path nesting,
-- so the induction hypothesis lands at `pathNestD κ` unchanged and the
-- only arithmetic owed is that the source's hop is at most the
-- subject's.  The burst disjunct is bounded by zero
depth-hop V g (mapᵉ f b) κ bid now sched st 2≤V szB slB =
  ⊔-lub
    (≤-trans (depth-hop V g b (map-f f ↠ κ) bid now sched st
                2≤V (sync-src szB) slB)
             (+-monoˡ-≤ (pathNestD κ)
                (hopD-map-mono V (slotHop V (Sched.slots sched)) f b)))
    (≤-trans (burst-mapf-zero g bid now f κ
                (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) z≤n)
  where r = subscribeE g b (map-f f ↠ κ) bid now sched st
depth-hop V g (takeᵉ count b) κ bid now sched st 2≤V szB slB =
  depth-hop-take V g b κ bid now sched st (evalTm count)
    2≤V (sync-src szB) slB
-- the mint is a `nextNode` bump, so `Sched.slots sched₁` REDUCES to
-- `Sched.slots sched` and the slots hypothesis crosses unchanged — which
-- is why this clause needs no slots-preservation lemma
depth-hop V g (scanᵉ f seed b) κ bid now sched st 2≤V szB slB =
  ⊔-lub
    (≤-trans (depth-hop V g b (scan-f f nid ↠ κ) bid now sched₁ st₀
                2≤V (sync-src szB) slB)
             (+-monoˡ-≤ (pathNestD κ)
                (hopD-scan-mono V (slotHop V (Sched.slots sched)) f seed b)))
    (≤-trans (burst-scf-zero g bid now f nid κ
                (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (scan-st (evalTm seed)) st
  r      = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁ st₀
-- the four hop edges are APPLICATIONS of one leaf, because `hopDᵉ`
-- charges every one of them `suc (hopDᵉ V η b)` and the operator and the
-- initial node state are the leaf's parameters
depth-hop V g (mergeAllᵉ b)   κ bid now sched st 2≤V szB slB =
  depth-hop-all V g mergeᵒ (merge-st 0 false) b κ bid now sched st
    2≤V (≤-trans (n≤1+n _) szB) slB
depth-hop V g (concatAllᵉ b)  κ bid now sched st 2≤V szB slB =
  depth-hop-all V g concatᵒ (concat-st [] false false) b κ bid now sched st
    2≤V (≤-trans (n≤1+n _) szB) slB
depth-hop V g (switchAllᵉ b)  κ bid now sched st 2≤V szB slB =
  depth-hop-all V g switchᵒ (switch-st nothing false) b κ bid now sched st
    2≤V (≤-trans (n≤1+n _) szB) slB
depth-hop V g (exhaustAllᵉ b) κ bid now sched st 2≤V szB slB =
  depth-hop-all V g exhaustᵒ (exhaust-st false false) b κ bid now sched st
    2≤V (≤-trans (n≤1+n _) szB) slB
depth-hop V g0 (μᵉ body) κ bid now sched st 2≤V szB slB = z≤n
-- the re-entry, and the clause the condition was restated for: the
-- recursion is on the GAS, `hopD-unfoldμ` is an EQUALITY so the bound
-- does not move, and `syncSize-unfoldμ` carries the condition across the
-- very substitution that squares `sizeᵉ`
depth-hop V (gs fuel) (μᵉ body) κ bid now sched st 2≤V szB slB =
  subst (λ X → depthE fuel (unfoldμ body) κ bid now sched st ≤ X + pathNestD κ)
        (hopD-unfoldμ V (slotHop V (Sched.slots sched)) body)
        (depth-hop V fuel (unfoldμ body) κ bid now sched st 2≤V
           (subst (_≤ V) (sym (syncSize-unfoldμ body))
              (≤-trans (n≤1+n _) szB))
           slB)

depth-hop-all-burst V g op ns b κ bid now sched st 2≤V szB slB =
  depth-hop-burst V g op nid κ bid now
    (hopDᵉ V (slotHop V (Sched.slots sched)) b) (Sched.slots sched)
    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) 2≤V slB
    (subscribeE-slots g b (thru-outer op nid ↠ κ) bid now sched₁ st₀)
    (proj₁ hops) (proj₂ hops)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  r      = subscribeE g b (thru-outer op nid ↠ κ) bid now sched₁ st₀
  hops   = allBurst-hops V g op ns b κ bid now sched st 2≤V szB slB

depth-hop-burst V g op nid κ bid now d sl [] sched st 2≤V slB slE hopH syncH = z≤n
depth-hop-burst {Γ = Γ} {u = u} V g op nid κ bid now d sl (em ∷ ems) sched st
                2≤V slB slE hopH syncH =
  ⊔-lub
    (s≤s (depth-hop-walk V g op nid κ bid now d sl (proj₁ sp) sched st
            2≤V slB slE
            (split-hop V (slotHop V sl) d (InstEmit.events em) (∧-trueˡ hopH))
            (split-sync V (InstEmit.events em) (∧-trueˡ syncH))))
    (depth-hop-burst V g op nid κ bid now d sl ems
       (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
       2≤V slB
       (trans (KeepsC.slotsEq (stepFrame-keeps g bid now (thru-outer op nid) κ
                 (proj₁ sp) (proj₂ (proj₂ sp)) sched st)) slE)
       (∧-trueʳ hopH) (∧-trueʳ syncH))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  r  = stepFrame g bid now (thru-outer op nid) κ
         (proj₁ sp) (proj₂ (proj₂ sp)) sched st

depth-hop-walk V g op nid κ bid now d sl [] sched st 2≤V slB slE hopH syncH = z≤n
depth-hop-walk V g op nid κ bid now d sl (o ∷ os) sched st
               2≤V slB slE hopH syncH =
  ⊔-lub
    (depth-hop-consume V g op nid κ bid now d sl o sched st 2≤V slB slE
       (∧-trueˡ hopH) (∧-trueˡ syncH))
    (depth-hop-walk V g op nid κ bid now d sl os
       (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) 2≤V slB
       (trans (KeepsC.slotsEq (thruConsume-keeps g op nid κ bid now o sched st)) slE)
       (∧-trueʳ hopH) (∧-trueʳ syncH))
  where r = thruConsume g op nid κ bid now o sched st

depth-hop-consume V g mergeᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO =
  depth-hop-inner V g mergeᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO
depth-hop-consume V g concatᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO =
  depth-hop-inner V g concatᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO
depth-hop-consume V g exhaustᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO =
  depth-hop-inner V g exhaustᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO
depth-hop-consume V g switchᵒ nid κ bid now d sl o sched st 2≤V slB slE hO sO =
  depth-hop-consumeS V g nid κ bid now d sl o sched st 2≤V slB slE hO sO
    (lookupNode nid (EvalSt.nodes st))

depth-hop-consumeS V g nid κ bid now d sl o sched st 2≤V slB slE hO sO
                   (just (switch-st cur od)) =
  depth-hop-inner V g switchᵒ nid κ bid now d sl o
    (proj₁ (proj₂ (switchKill cur sched st)))
    (proj₂ (proj₂ (switchKill cur sched st))) 2≤V slB
    (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slE) hO sO
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _ nothing = z≤n
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _
                   (just (scan-st _)) = z≤n
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _
                   (just (take-st _)) = z≤n
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _
                   (just (merge-st _ _)) = z≤n
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _
                   (just (concat-st _ _ _)) = z≤n
depth-hop-consumeS V g nid κ bid now d sl o sched st _ _ _ _ _
                   (just (exhaust-st _ _)) = z≤n

depth-hop-inner V g0 op nid κ bid now d sl o sched st _ _ _ _ _ = z≤n
depth-hop-inner V (gs fuel) op nid κ bid now d sl o sched st
                2≤V slB slE hO sO =
  ≤-trans
    (depth-hop V fuel o (from-inner op nid (Sched.nextNode sched) ↠ κ) bid now
       (record sched { nextNode = suc (Sched.nextNode sched) }) st 2≤V
       (≤ᵇ⇒≤ (syncSizeᵉ o) V (T-to sO))
       (subst (λ X → slotsSize X ≤ V) (sym slE) slB))
    (+-monoˡ-≤ (pathNestD κ)
       (subst (λ X → hopDᵉ V (slotHop V X) o ≤ d) (sym slE)
          (≤ᵇ⇒≤ (hopDᵉ V (slotHop V sl) o) d (T-to hO))))
