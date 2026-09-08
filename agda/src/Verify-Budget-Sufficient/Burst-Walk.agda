------------------------------------------------------------------
-- BURST-WALK: the DRY (`nodry`) face over the Delivery-Walk — the arms
-- that CONSUME the per-frame leaves, up to `stepFrame-nodry`.  The
-- third flavour is gas-conditioned through the walk's GOK hook;
-- `stepFrame-nodry`, which carried the last of the anchor chain's risk,
-- is a real definition, and this module's only live postulate is
-- `subscribeE-Ψ`.

-- IT IS ONE THIRD OF WHAT IT WAS, and the reason is cost rather than
-- subject.  A file whose blocks are all acyclic is checked in ONE pass
-- with nothing stubbed, so every body in it is paid for whenever any of
-- it is — which took this module out of the dev loop entirely.  The
-- leaves went to `.Burst-Walk.Leaves` and the frame face and cascade
-- payoff to `.Burst-Walk.Burst-Face`; the cuts are where a handful of
-- names cross, and nothing here calls what left.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; s≤s; z≤n; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m≤m+n; m≤n+m; m≤n⊔m; m≤m⊔n; n≤1+n; ≤-pred)
open import Data.List    using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Nullary using (yes; no)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Prim using (Gas; gs; Id; Tick; gasPad; gasTower; towerℕ)
open import Rx.Exp  using (Ctx; Closed; Val; obs; _≟ᵗ_; sizeᵉ; syncSizeᵉ; inputsBelowᵛ)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; Frame; _↠_; map-f; scan-f; take-f; from-inner; thru-outer; Stream;
  stepFrame; dropSource; shareLatch; shareFinish; hasDry; dryEvent; budgetAt; capsHgo;
  capsBase; fLvlD; opIterD; subscribeInner; subscribeE; sLvlD; sIterD; sIterD-suc; sizeAt;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeId; NodeState; takeDispatch; takeVals; lookupNode;
  innerFinish; mergeAllDrain; aliveThroughᶠ; switchKill; thruConsume; thruWalk; scan-st;
  take-st; hasRoom; mergeAll-st; switch-st; exhaust-st)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk
  using (regP?)
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-zip; dBound; dBound-bound; fcB-live; fcB-nodes; fnCapBounded?; fnCapᵉ;
  hasAtLeast-mono; hasAtLeast-pad-plus; hasAtLeast-tower; hopR; INV?; pathB?; pathB?-widen;
  pathLen; prod≤3pow; regsLen?; slotHop-cap; slotsFnCap; syncSize≤sizeᵉ; unconn; unconn≤slots;
  ∧-true)

open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthWalk; depthConsume; depthInner; depthDrain)

open import Verify-Budget-Sufficient.Caps-Nest using (nest)

-- THE SHARE-LEDGER RING.  `nest` is antitone in the connected set, so a
-- nest bound survives any step that only ENLARGES that set — and the ring
-- proves exactly that, per evaluator step, as a `KeepsC` record.  This is
-- what the walk's two nest-preservation obligations spend.
open import Verify-Budget-Sufficient.Keeps-Ring
  using (KeepsC; subscribeInner-keeps)

-- THE LEVEL DESCENTS, spent by the thru walk's ceiling channel.  The wet
-- walk face already threads an abstract ceiling level and converts it to
-- each callee's budget with these; the nodry face now does the same, which
-- is what took the per-element ceiling off an unstated fLvlD inequality.
open import Verify-Budget-Sufficient.Caps-Chain using (walk-desc; inner-desc)
open import Verify-Budget-Sufficient.Caps using (sIterD-mono; frame-room; fuel-pred; 2≤capsAt-size; 6≤capsAt-size; Caps; capsAt-base-size;
  capsAt-tower; capsH; frameStep; frameStep-mono-j; frameStep-reg≤size; opIterD-infl; tower-3)

-- THE CAPS FACE'S OWN thruConsume STEP, PROVEN.  It carries the level the
-- step lands at and the caps invariant there; the nodry walk's loop
-- invariant is that plus the Ψ half, which this module proves itself.
open import Verify-Budget-Sufficient.Subscribe-Face
  using (thruConsume-caps; subscribeInner-caps)

-- named explicitly: .Caps-Face and .Wet share .Measures names
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; capsOK?-mono; parkStrat?; pathFloor; pathStrat?; pathSz?; pathSz?-widen; slotsCaps?;
  valCaps?)
-- THE PARKED QUEUE'S READING, which no premise of this face carries; the
-- leaf's own header says why it is stated over `capsOK?` rather than read
-- out of it.
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves using
  (frame-parkStrat)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-nodeSz; capsOK?-nodeWid; capsOK?-parts; capsOK?-regs; lookupNode-caps; mList?;
  mList?-head; mList?-keeps; mList?-tail; NodeCaps; pathSz?-len; pathSz?-tail; switchKill-caps;
  valsCaps?; valsCaps?-lvl; valsCaps→mList-strict; valsStrat?)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (frameStep-chain-suc; pathSz?-⊑)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (cSize≤frameStep; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (valsLen; valsOf)

open import Verify-Budget-Sufficient.Wet.Part6 using
  (sizeCapAt)
open import Verify-Budget-Sufficient.Wet.Part1 using
  (INV?-widen; sweepLive-fnCap)
open import Verify-Budget-Sufficient.Burst-Walk.Predicates using
  (OKB; PbB; VbB)
open import Verify-Budget-Sufficient.Walk-Level
  using (subscribeE-walk-level; capsOK⇒regsLen; regsLen?-mono)
open import Verify-Budget-Sufficient.Walk-Level.Statement using
  (WalkLevel)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (any-dry-++; splitBurst-nodry; switchKill-closes-nodry; thruWrap-pass)
open import Verify-Budget-Sufficient.Psi-Split using
  (INV?-of-parts; lookupNode-fnCap; NodeΨ; pathB?-of-parts; pathBΨ?; regsB?-of-parts; valsΨ?;
  valΨ?)
open import Rx.Frame-Width using (pWᵉ; dWᵉ; outWᵛ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Frame-Width using (dWᵉ; pWᵛ; outWᵛ; pWᵉ)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)
open import Verify-Budget-Sufficient.Burst-Walk.Leaves using
  (VbB-head; VbB-tail; nodry-elem-size; thruConsume-nodry-nestRec; switchKill-nest;
  thruWalk-nodry-dep; cutThrough-nodry; subscribeInner-Ψ; regP?-Ψ; regP?-of-parts;
  switchKill-Ψ; thruConsume-Ψ)

------------------------------------------------------------------
-- THE Ψ-STATE FACTS the walk's OK closure needs — all REAL.
-- consᵈ and shareLatch touch only delivered/completedSources/dying,
-- fields fnCapBounded? never reads, so those two are transparent.
-- shareFinish sweeps live and filters the registry: sweepLive-fnCap
-- (.Wet) is exactly the live half, and nodes ride through.
------------------------------------------------------------------

fnCapB-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  fnCapBounded? Ψ sched st ≡ true →
  fnCapBounded? Ψ sched (shareLatch i fin st) ≡ true
fnCapB-latch Ψ i false sched st h = h
fnCapB-latch Ψ i true  sched st h = h

fnCapB-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (i : Fin n) (fin : Bool)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  fnCapBounded? Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) ≡ true →
  fnCapBounded? Ψ (proj₁ (proj₂ (shareFinish i fin out)))
                  (proj₂ (proj₂ (shareFinish i fin out))) ≡ true
fnCapB-finish Ψ i false out h = h
fnCapB-finish Ψ i true  out h =
  ∧-intro
    (sweepLive-fnCap Ψ
      (dropSource (toℕ i) (EvalSt.registry (proj₂ (proj₂ out))))
      (Sched.live (proj₁ (proj₂ out)))
      (fcB-live Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) h))
    (fcB-nodes Ψ (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) h)


------------------------------------------------------------------
-- THE DRY FACE OF ONE FRAME (stepFrame-nodry) — WHERE THE ANCHOR'S RISK USED TO
-- LIVE, and it is now a real definition (the ruling is `cascadeGo-nodry`'s header).

-- One frame of one delivery, run on the WALK'S OWN MINTED GAS, emits
-- no dried close.  This is the ex-anchor (`cascadeGo-nodry`)
-- with everything transport-shaped stripped off: the walk carries
-- dryness through appends and widens mechanically (`EbB`/`BbB`'s third
-- flavour), so the entire dry content of the cascade concentrates in
-- this one per-frame face.

-- THE GAS HYPOTHESIS IS THE POINT.  `sf ≡ budgetAt e sl id` — the one
-- gas `chainStep` mints (Rx.Evaluator), carried to the frame by
-- the walk's GOK/g-mint hook (.Delivery-Walk, built for exactly this).
-- Without it the statement is FALSE: `subscribeInner g0` emits a
-- dried close and the depth premise does not exclude g0 (depth
-- measures nesting demand, not supply).

-- THE GRIND ROUTE, per frame constructor:
--   · map-f / take-f / scan-f — event inspection: these frames emit
--     no events of their own (the map/take/scan leaves' proofs enumerate the outputs);
--     their nodry halves are refl-shaped.
--   · from-inner / thru-outer (the risky region, and the reason the
--     anchor was FALSITY class) — the interior `subscribeE`, consumed
--     through the COLLAPSED WALK FACE (`subscribeE-walk-level`,
--     .Walk-Level), whose hasDry conjunct is `hasDry ≡ false` and whose
--     hypotheses are LEVEL-indexed at an arbitrary (c , j) — i.e.
--     stated to be satisfiable MID-DELIVERY, which the retired outer
--     face (fixed at capsAt e sl id / id-entry B) was not.  At the
--     frame's own J, the walk supplies: capsOK? (frameStep J c) and
--     fnCapBounded? Ψ from OKB; the path facts from PbB; the value
--     size from VbB.  The two pieces to manufacture, each named the
--     moment the grind reaches it:
--       (i) INV? Ψ (cSize (frameStep J c)) mid-delivery — assembled
--           conjunct-by-conjunct from capsOK? + fnCapBounded? + the
--           regP? ledger, the SAME move as cascade-wet-via-caps' INV? recombination
--           (.Caps-Bridge) makes one stratum up.  Needs
--           cReg (frameStep J c) ≤ cSize (frameStep J c) — B2's
--           frameStep analogue — for the registry-length conjunct.
--           ARITHMETIC CHECKED TRUE (hand derivation, not
--           yet machine): with F j := cSize (frameStep j c), R ≤ S,
--           2 ≤ S, induct on j: F 0 = S ≥ R; F (suc j) = S + 2S·F j
--           (frameStep-size-suc) ≥ S·F j + S·F j ≥ F j + R·S, and
--           R·(1+(1+j)·S) = R·(1+jS) + RS ≤ F j + RS.  Uses only
--           R ≤ S ≤ F j (iterSize-infl) — no new machinery needed.
--      (ii) the fuel: `budgetAt e sl id hasAtLeast suc G` for a demand
--           G measured at Ŝ := sizeCapAt e sl (suc id) — the
--           general-id crib of `caps-fuel-root` (.Wet/Part6, PROVEN,
--           id = 0).  SHAPE CHECKED: `budgetAt e sl id`
--           unfolds to gasPad (2^(sz·suc id·suc id)) (gasTower
--           (3 + capsHgo m (suc id))) — the EXACT gas
--           `budget-hasAtLeast sz m id` (.Measures, PROVEN, general
--           id) is stated at — and the demand side's chain
--           (dBound-bound → prod≤3pow → tower-3 → capsAt-tower) is
--           general in id throughout; only the 6≤V and size-fits
--           facts change instantiation.  The inner value's size fits
--           under Ŝ by the walk's own landing arithmetic (lvl-fits +
--           capsAt-suc-full, `cascadeGo-burst-nodry`'s payoff arithmetic).

-- THIS FACE WAS THE ANCHOR'S RISKY REGION (a from-inner subscribe
-- mid-delivery), carried as FALSITY until it was ground.  The receipt
-- that still matters: it CANNOT BE PROBED, same as the anchor — the gas
-- family is abstract and `budgetAt` is a tower the checker will not
-- normalise — so the discharge is a proof, and never could have been a probe.
--
-- ═══ THE FIVE-FRAME CENSUS — ALL FIVE ARE NOW REAL ═══

-- `stepFrame-nodry` is an assembly over the frame constructors, and the risk
-- did NOT spread evenly across them.  The census is kept because it is what
-- located the consolidation below; the column says where each frame's dryness
-- CAME FROM, not what is still owed:
--
--   map-f    — events are literally `[]`.                    PROVEN, refl
--   scan-f   — every `dispatch` arm emits `[]`.              PROVEN, refl
--   take-f   — `takeDispatch`: `[]`, or `cutThrough`'s
--              closes, and CUTTHROUGH NEVER MINTS `dried`
--              (`cutThrough-nodry` — every close it
--              makes is `cut`/`cutPending`).                 PROVEN
--   from-inner — `innerReact` → `innerFinish`, whose only
--              emitting arm is mergeAllᵒ's `mergeAllDrain`.     via SiNodry
--   thru-outer — `thruWrap`/`thruWalk`/`thruConsume`, whose
--              events are `switchKill`'s closes (cutThrough
--              again, free) plus `subscribeInner`'s.         via SiNodry
--
-- ═══ THE CONSOLIDATION THAT FALLS OUT, and it is the finding ═══

-- Chase those two frames to their leaves and they MEET:
-- `mergeAllDrain` (Rx.Evaluator) emits nothing of its own — its `bs`
-- is `subscribeInner`'s, appended down the queue.  `switchKill` is
-- cutThrough.  So after the three proven frames, EVERY remaining
-- dried-close risk in the whole cascade is `subscribeInner`, whose two
-- clauses are:
--   · `g0`      — emits `close drySource dried` (Rx.Evaluator).
--                 THE one dry mint in the evaluator.  Excluded by the
--                 gas hypothesis: `budgetAt` is a `gasPad` of a
--                 `gasTower`, never `g0`.
--   · `gs fuel` — `subscribeE fuel …`, i.e. `subscribeE-walk-level`'s
--                 hasDry conjunct, at `fuel` — and the walk face asks for
--                 `g hasAtLeast suc G`, an INEQUALITY, not a pin to
--                 `budgetAt`, so the `gs`-peel goes straight through.
--                 Checked; had the walk pinned its gas the
--                 descent would not have typed.
--
-- ═══ THE LOOP QUESTION, RULED ═══

-- The two remaining frames are NOT one-step: `mergeAllDrain` and
-- `thruWalk` LOOP, calling `subscribeInner` at a state that has
-- already moved.  So the leaf's hypotheses (capsOK? and friends, all
-- state-dependent) must be RE-ESTABLISHED per iteration — which is
-- what the caps route's Σ-witness does and what a bare `≡ false`
-- conclusion cannot.  The gas hypothesis is the one part that threads
-- for FREE: `fuel` is passed unchanged by every one of innerReact,
-- innerFinish, mergeAllDrain, thruWalk, thruConsume and thruWrap
-- (checked), so the `g0` exclusion never has to be re-won.

-- TWO ROUTES WERE ON THE TABLE.  (A) take the already-proven caps
-- faces (siC/ifc) as extra parameters and re-establish `capsOK?` at
-- the moved state from their Σ-witness, mirroring what `stepFrame-burst-face` already
-- does one level up.  (B) widen SiCFace/IfcFace's own conclusions
-- with a nodry conjunct, so the re-establishment comes for free.

-- RULED: (A).  (B) is tidier to read and strictly worse to build —
-- its suppliers (`subscribeInner-caps`, `innerFinish-caps`) are
-- PROVEN inside Subscribe-Face, so widening their conclusions
-- re-grinds finished work in the most expensive module in the repo
-- (timings: typecheck-performance-numbers.md), and buys no strength that threading the same witness does not.
-- (A) also has a working precedent in this file rather than a
-- hypothetical one.

-- WHAT THAT MAKES THE TWO FRAMES: transport over ONE leaf, named
-- below as `SiNodry` and — at the time of the ruling — postulated once,
-- since PROVEN as `subscribeInner-nodry`.  The `-core` pair keeps
-- that structural rather than prose — each frame is a real definition
-- applying its core to the single leaf, so `subscribeInner-nodry` has
-- a consumer from the minute it is stated and the census above is
-- checkable by grep instead of by reading this header.
------------------------------------------------------------------

-- THE ONE LEAF.  Everything dry in the cascade reduces to this, and
-- its own two clauses are the g0 mint (excluded by `gk`) and
-- `subscribeE fuel …` (= `subscribeE-walk-level`'s hasDry conjunct).
SiNodry : Set
SiNodry = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  -- the Ψ-side twin of the line above; see subscribeE-inner-nodry-inv's
  -- header for why it is threaded (INV?'s slotsFnCap conjunct)
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  -- THE PATH-LENGTH HYPOTHESIS, IN THE CAPS FACE'S OWN SHAPE.
  -- This is `lC` verbatim from subscribeE-caps / subscribeInner-caps, and
  -- that is the point: WalkStmt's hypotheses ARE the caps face's, so the wet
  -- inner call has no business asking for a different one.
  --
  -- It previously asked for `suc (suc (pathLen κ))` at level J — one unit
  -- more than any caller could produce.  The unit had nowhere to come from
  -- because the wet core was subscribing the inner at level J while the
  -- PROVEN twin `subscribeInner-caps` (.Subscribe-Face) subscribes at
  -- `suc j`: "the inner is subscribed under one more frame, at the same
  -- instant, and at ONE MORE j".  Extending a path without paying the frame
  -- is what made the bound unreachable; paying it makes `frameStep-chain-suc`
  -- deliver the extra unit exactly where the walk face wants it.
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling: the walk face's pins force
  -- the honest instantiation Ŝ := sizeCapAt e sl (suc id), and this is
  -- the c-to-entry anchoring the caller owns (c is free here; the
  -- caller knows it is capsAt-rooted).  The face's budget at this
  -- call's arguments stays under the next instant's size cap.
  -- AT suc J, matching the level the inner is now subscribed at (see the
  -- path-length hypothesis above).  L̂ is opIterD's value at the level the
  -- walk face is actually applied at, so bumping the call bumps this too.
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
    ≤ sizeCapAt e sl (suc id) →
  g ≡ budgetAt e sl id →
  any dryEvent (proj₁ (proj₂ (proj₂
    (subscribeInner g op allNid κ id now o sched st))))
    ≡ false

-- THE MINTED BUDGET IS NEVER EMPTY, and this is what excludes the
-- evaluator's ONE dry mint.  `budgetAt` unfolds to
-- `gasPad (2 ^ N) (gasTower H)`, and `2 ^ N` is positive whatever N is,
-- so the gas the machine mints always carries a `gs` head.  Hence
-- `subscribeInner g0` — the sole site that emits `close _ dried`
-- (Rx.Evaluator) — is UNREACHABLE under the gas hypothesis, as a
-- theorem rather than as an appeal to the tower's size.
2^-pos : ∀ (m : ℕ) → Σ ℕ (λ k → 2 ^ m ≡ suc k)
2^-pos zero    = 0 , refl
2^-pos (suc m) with 2^-pos m
... | k , eq rewrite eq = k + suc (k + 0) , refl

budgetAt-gs : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id) →
  Σ Gas (λ g′ → budgetAt e sl id ≡ gs g′)
budgetAt-gs e sl id
  with 2^-pos ((sizeᵉ e + slotsSize sl) * suc id * suc id)
... | k , eq rewrite eq =
      gasPad k (gasTower (3 + capsHgo (capsBase e sl) (suc id))) , refl

-- THE SAME FACT WITH THE PAD COUNT KEPT.  budgetAt-gs
-- existentially quantifies the GAS, which is all its own consumers need —
-- but a caller that wants a hasAtLeast bound needs the ℕ pad, since
-- hasAtLeast-pad-plus is indexed by it.  The body above already computes
-- that number and then discards it behind `Σ Gas`, so the strengthening is
-- free: same `with`, return the ℕ instead of the gas built from it.
--
-- This exists because subscribeE-inner-nodry-fuel was written against
-- budgetAt-gs as though its witness were the pad count.  It is not, and the
-- mismatch does not surface as a missing hypothesis — it surfaces as
-- `Gas !=< ℕ` deep inside an arithmetic chain, which is why the assembly
-- read as complete until a real check ran.
budgetAt-gs-pad : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id) →
  Σ ℕ (λ k → budgetAt e sl id
               ≡ gs (gasPad k (gasTower (3 + capsHgo (capsBase e sl) (suc id)))))
budgetAt-gs-pad e sl id
  with 2^-pos ((sizeᵉ e + slotsSize sl) * suc id * suc id)
... | k , eq rewrite eq = k , refl

-- splitEvents-nodry / splitBurst-nodry MOVED DOWN to .Walk-Level
-- , with any-dry-++: the ground subscribeInner-walk
-- consumes the split there.  Imported back through the module import.

-- EX-RESIDUE, PROVEN.  It was postulated on the grounds
-- that `outWᵛ` sits outside this module's import scope — a missing
-- import, not a mathematical obstacle, and the wrong reason for a
-- postulate.  `dWᵛ` at an `obs` type IS `dWᵉ` (Rx.Frame-Width,
-- definitional) and `valCaps?` already carries
-- `pWᵛ n sl (obs u) o ≤ᵇ cWid` with `pWᵛ = outWᵛ ⊔ dWᵛ`, so the bound
-- is ⊔'s right injection.
--
-- WHAT ACTUALLY BLOCKED IT, recorded because the error message points
-- somewhere else: `valsCaps?` is NOT just `all valCaps?` — it carries
-- a second conjunct bounding the LIST LENGTH by `suc (cWid c)`
-- (Caps-Face/.Part5).  A hand-peel that assumes the `all` shape
-- fails with a mismatch reported against `sizeᵉ o ≤ᵇ …`, which reads
-- like an `∧`-association problem and is not one.  `valsCaps?-parts`
-- is the lemma that splits it; use it rather than peeling by hand.
inner-dWO : ∀ {n} {Γ : Ctx n} {u}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (o : Val Γ (obs u)) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  dWᵉ n sl o ≤ Caps.cWid (frameStep J c)
inner-dWO {n = n} {u = u} c sl Ψ J o vb =
  ≤-trans (m≤n⊔m (outWᵛ n sl (obs u) o) (dWᵉ n sl o))
          (≤ᵇ⇒≤ (pWᵛ n sl (obs u) o) W (T-to wOK))
  where
  B = Caps.cSize (frameStep J c)
  W = Caps.cWid (frameStep J c)

  vcs : valsCaps? (frameStep J c) sl (o ∷ []) ≡ true
  vcs = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ []))
                      (valsΨ? Ψ (o ∷ [])) vb)

  allv : all (valCaps? (frameStep J c) sl (obs u)) (o ∷ []) ≡ true
  allv = proj₁ (valsCaps?-parts (frameStep J c) sl (o ∷ []) vcs)

  vc : ((sizeᵉ o ≤ᵇ B) ∧ (pWᵛ n sl (obs u) o ≤ᵇ W)) ≡ true
  vc = proj₁ (∧-true ((sizeᵉ o ≤ᵇ B) ∧ (pWᵛ n sl (obs u) o ≤ᵇ W)) true allv)

  wOK : (pWᵛ n sl (obs u) o ≤ᵇ W) ≡ true
  wOK = proj₂ (∧-true (sizeᵉ o ≤ᵇ B) (pWᵛ n sl (obs u) o ≤ᵇ W) vc)

-- Residue postulates for subscribeE-inner-nodry-core.
-- Each names one manufacturing obligation; all seven are consumed by
-- the assembly below.
-- subscribeE-inner-nodry-pSz and -pLen are BOTH GONE, and they
-- fell to the same one-line change: the inner call now subscribes at `suc J`,
-- matching the PROVEN twin subscribeInner-caps.
--   · -pLen was an identity returning a bound nothing could supply.  With the
--     level bump, `frameStep-chain-suc` DERIVES it from the caps face's own lC.
--   · -pSz manufactured pathSz? at the extended path.  It existed only because
--     at level J its length conjunct was unreachable; at suc J the core builds
--     it inline as `pC′`, exactly as subscribeInner-caps builds its own.
-- The lesson is worth more than the two rows: a postulate whose hypotheses
-- cannot supply its conclusion is often not a hard lemma but a MISPLACED CALL,
-- and the proven twin is where to look for the placement.
--   RECOVERY: git show 4a76fff restores the identity form and the analysis
--   that led here, if the level bump ever has to be undone.

-- INV? AT THE INNER FRAME'S LEVEL, assembled from OKB + the regP? ledger
-- + the two slot bounds + the ladder's registration/size side condition.
-- Conjunct by conjunct: stBounded? is capsOK?'s own first; fnCapBounded?
-- is OKB's second; the registry CARDINALITY is capsOK?'s last conjunct
-- carried across `cReg ≤ cSize` at the level the conclusion is stated at;
-- regsB? recombines capsOK?'s regsSz? with regP?'s pathBΨ? half
-- (`regsB?-of-parts` — in .Psi-Split, beside the Ψ predicates it consumes;
-- it previously sat in .Caps-Bridge, downstream, and that placement was
-- this row's only blocker.  Nothing had to move DOWN and no all-zip
-- inlining is needed: .Caps-Bridge was downstream of all three ingredient
-- families, so the lemmas were simply left behind when the Ψ predicates
-- themselves were relocated); and the two slot conjuncts are hypotheses,
-- transported across walkOK's `Sched.slots sched ≡ sl`.

-- ⚠ SHAPE DEFECT FOUND AND REPAIRED — the SAME anti-pattern as `-pLen`
-- above ("a conclusion needing information that appears in NONE of its
-- hypotheses"), caught by reading the definitions rather than by a failed
-- grind.  INV?'s last two conjuncts are `slotsSize (Sched.slots sched) ≤ᵇ
-- B` and `slotsFnCap … ≤ᵇ Ψ`, and the ORIGINAL hypothesis list could reach
-- NEITHER: OKB is `walkOK × fnCapBounded?`, `walkOK` is
-- `slots-eq × capsOK?`, and capsOK? bounds live/nodes/registry/widths — it
-- never bounds the SLOT STORE's size or fn-weight, and fnCapBounded? reads
-- only live/nodes.  `PbB`/`VbB` are about the path and the value.  So the
-- statement was UNDERDETERMINED, not hard.

-- The repair MIRRORS a hypothesis already threaded at every level of this
-- stack: `slotsSize sl ≤ cSize c` was present all the way down (so that
-- conjunct was always reachable and only the transport was unstated); its
-- Ψ-side twin `slotsFnCap sl ≤ Ψ` was simply missing, and is now threaded
-- beside it through -core, subscribeE-inner-nodry and SiNodry.  At the true
-- instantiation Ψ := ΨAt e sl is `fnCapᵉ e + slotsFnCap sl`, so the new
-- hypothesis is `m≤n+m` — the same way `caps-fuel-root` (.Wet/Part6)
-- already discharges it.

-- ⚠ AND THE SAME DEFECT AGAIN, ONE CONJUNCT OVER — REFUTED,
-- machine-checked: `inner-nodry-inv-regLen-absurd` (agda/evidence/refuted,
-- Refuted.Inner-Nodry).  INV?'s THIRD conjunct is the registry CARDINALITY
-- against the SIZE cap, and the only hypothesis mentioning that length is
-- capsOK?'s last, which bounds it against the REGISTRATION cap.  The two
-- caps dimensions are independent, so a caps with `cReg > cSize` satisfies
-- every hypothesis and breaks the conclusion — the witness holds four root
-- chains under cReg 4 and cSize 3, with every other conjunct clear by a
-- margin.

-- THE LESSON, and it is why the row was misclassified: this row was called
-- GRINDABLE on the grounds that "every conjunct has a named source IN
-- SCOPE", and `frameStep-reg≤size` was one of the names.  A lemma being
-- PROVEN and in scope says NOTHING about its own hypotheses being
-- available where it is applied — that lemma needs `1 ≤ cSize c` and
-- `cReg c ≤ cSize c`, neither of which the statement carried.  So the
-- premise is now stated at the level the conclusion is stated at, where
-- the consumer discharges it from its own `2≤S` and `hCR`.

-- AND THE SLOT PREMISE IS RE-INDEXED RATHER THAN CONDITIONED.  It reads
-- `slotsSize sl ≤ Caps.cSize (frameStep J c)`, which is the WEAKER
-- hypothesis and therefore the STRONGER statement: the inflation transport
-- belongs at the call site, which owns the `2≤S` that `cSize≤frameStep`
-- needs.  No hypothesis was added for it.
subscribeE-inner-nodry-inv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  slotsSize sl ≤ Caps.cSize (frameStep J c) →
  slotsFnCap sl ≤ Ψ →
  Caps.cReg (frameStep J c) ≤ Caps.cSize (frameStep J c) →
  OKB {e = e} c sl Ψ J sched st →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  INV? Ψ (Caps.cSize (frameStep J c)) sched st ≡ true
subscribeE-inner-nodry-inv c sl Ψ J sched st slSz slFc rgSz ((slEq , cOK) , fcb) rp
  with capsOK?-parts (frameStep J c) sched st cOK
... | stB , rgSzP , _ , _ , rLen , _ =
  INV?-of-parts Ψ (Caps.cSize (frameStep J c)) sched st stB fcb
    (T⇒≡true (length (EvalSt.registry st) ≤ᵇ Caps.cSize (frameStep J c))
      (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (length (EvalSt.registry st))
                            (Caps.cReg (frameStep J c)) (T-to rLen))
                     rgSz)))
    (regsB?-of-parts (EvalSt.registry st) rgSzP
      (regP?-Ψ c Ψ J (EvalSt.registry st) rp))
    (subst (λ x → (slotsSize x ≤ᵇ Caps.cSize (frameStep J c)) ≡ true) (sym slEq)
      (T⇒≡true (slotsSize sl ≤ᵇ Caps.cSize (frameStep J c)) (≤⇒≤ᵇ slSz)))
    (subst (λ x → (slotsFnCap x ≤ᵇ Ψ) ≡ true) (sym slEq)
      (T⇒≡true (slotsFnCap sl ≤ᵇ Ψ) (≤⇒≤ᵇ slFc)))

-- pathB? FOR THE EXTENDED PATH — a real body, and it is
-- three lines.  `frameB? B Ψ (from-inner _ _ _) = true` (.Measures) gives the
-- head by `refl`, and `pathB?-of-parts` — PROVEN above in this module since
-- the relocation that moved it out of downstream .Caps-Bridge — recombines
-- PbB's `pathSz?` and `pathBΨ?` halves into the real `pathB?` that INV?
-- reads.  `pathB?` carries no length conjunct, which is what keeps it cheap.
--
-- ∧-true's Bool arguments are EXPLICIT here on purpose: `PbB` reduces to a
-- conjunction Agda cannot recover from the equation alone, the same reason
-- the from-inner strip in .Caps-Bridge spells them out.
subscribeE-inner-nodry-pBO : ∀ {n} {Γ : Ctx n} {t u}
  (c : Caps) (Ψ J : ℕ) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ u t) →
  PbB c Ψ J κ ≡ true →
  pathB? (Caps.cSize (frameStep J c)) Ψ (from-inner op allNid inst ↠ κ) ≡ true
subscribeE-inner-nodry-pBO c Ψ J op allNid inst κ pb =
  ∧-intro refl
    (pathB?-of-parts κ
      (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb))
      (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)))

-- Gas bound at the inner call: fuel hasAtLeast suc G.
-- THE ROUTE: gk via budgetAt-gs (gs-peel) and the demand chain
-- dBound-bound → prod≤3pow → tower-3 → m≤n+m.  The `sizeᵉ o ≤ Ŝr`
-- hypothesis derives at the call site from szO via frameStep-mono-j +
-- opIterD-infl + the caller's cl ceiling.
--
-- IT IS STATED AT THE RESET CAPS Ŝ := sizeCapAt e sl (suc id), not at a
-- level cap: the walk face's reset-anchor pins reject the level-cap
-- instantiation (frameStep J c cannot ceiling a walk that climbs past J),
-- and the reset caps are where budget-hasAtLeast lives — budgetAt e sl id
-- is minted from e's entry measures, so this form is the MORE provable one.
--
-- SEALED, AND THE SEAL MAY NOT COME OFF.  A transparent body here reaches
-- Verify-Well-Formed, which is the exact transition that OOMs a full build
-- (`Killed: 9` in VWF/Part13; the trap's instances are in
-- typecheck-performance-numbers.md).  No consumer needs more than the type.  private-impl + abstract-alias rather
-- than a plain `abstract` block, because the body has a with-abstraction
-- and untyped where-bindings, both of which `abstract` rejects.
-- The type is NAMED rather than written twice: private-impl + abstract-alias
-- needs the signature at both sites, and duplicating a type this size made
-- Agda elaborate it twice.  Measured on the Walk-Level twin the same night,
-- that cost more memory than the seal saved.  Same idiom as SiNodry above.
InnerNodryFuel : Set
InnerNodryFuel = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (fuel : Gas)
  (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id) (now : Tick)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  gs fuel ≡ budgetAt e sl id →
  sizeᵉ o ≤ sizeCapAt e sl (suc id) →
  fuel hasAtLeast suc (dBound (sizeCapAt e sl (suc id))
                              (hopR (sizeCapAt e sl (suc id)))
                              (unconn sl (EvalSt.connectedShares st))
                              (hopDᵉ (sizeCapAt e sl (suc id)) (slotHop (sizeCapAt e sl (suc id)) sl) o)
                              (syncSizeᵉ o))

private
  subscribeE-inner-nodry-fuel-go : InnerNodryFuel
  subscribeE-inner-nodry-fuel-go {e = e} c sl Ψ dep bud J fuel op allNid κ id now o sched st
      ok nB hD gk sz≤Ŝr
    with budgetAt-gs-pad e sl id
  ... | k , eq =
    hasAtLeast-mono demand fuelH
    where
    Ŝr      = sizeCapAt e sl (suc id)
    H       = 3 + capsHgo (capsBase e sl) (suc id)
    U       = unconn sl (EvalSt.connectedShares st)
    6≤V     : 6 ≤ Ŝr
    -- 6≤capsAt-size is the ONE lemma in this family whose CONCLUSION
    -- already carries the suc (`6 ≤ cSize (capsAt e sl (suc id))`), unlike
    -- 2≤capsAt-size / capsAt-base-size / capsAt-tower, which conclude at
    -- the id they are given.  Passing `suc id` here lands a level too high
    -- and the mismatch surfaces as an iterSize term, not as an index error.
    6≤V     = 6≤capsAt-size e sl id
    slots≤V : slotsSize sl ≤ Ŝr
    slots≤V = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl (suc id))
    U≤V     : U ≤ Ŝr
    U≤V     = ≤-trans (unconn≤slots sl (EvalSt.connectedShares st)) slots≤V
    s≤V     : syncSizeᵉ o ≤ Ŝr
    s≤V     = ≤-trans (syncSize≤sizeᵉ o) sz≤Ŝr
    r≤R     : hopDᵉ Ŝr (slotHop Ŝr sl) o ≤ hopR Ŝr
    r≤R     = slotHop-cap Ŝr sl (2≤capsAt-size e sl (suc id)) slots≤V o sz≤Ŝr
    gs-inj  : ∀ {a b : Gas} → gs a ≡ gs b → a ≡ b
    gs-inj refl = refl
    fuelIs  : fuel ≡ gasPad k (gasTower H)
    fuelIs  = gs-inj (trans gk eq)
    -- PARENTHESISED ON PURPOSE: _hasAtLeast_ binds tighter than _+_, so
    -- `g hasAtLeast k + towerℕ H` parses as `(g hasAtLeast k) + towerℕ H`
    -- — a Set added to a ℕ, reported as "ℕ should be a sort" rather than
    -- as a precedence problem.
    fuelH   : fuel hasAtLeast (k + towerℕ H)
    fuelH   = subst (λ g → g hasAtLeast (k + towerℕ H)) (sym fuelIs)
                    (hasAtLeast-pad-plus k (hasAtLeast-tower H))
    D       = dBound Ŝr (hopR Ŝr) U (hopDᵉ Ŝr (slotHop Ŝr sl) o) (syncSizeᵉ o)
    demand  : suc D ≤ k + towerℕ H
    demand  =
      ≤-trans (s≤s (dBound-bound s≤V r≤R))
      (≤-trans (prod≤3pow Ŝr U 6≤V U≤V)
      (≤-trans (tower-3 (capsH e sl (suc id)) Ŝr (proj₁ (capsAt-tower e sl (suc id))))
               (m≤n+m (towerℕ H) k)))


abstract
  subscribeE-inner-nodry-fuel : InnerNodryFuel
  subscribeE-inner-nodry-fuel = subscribeE-inner-nodry-fuel-go

-- THE ASSEMBLY.  Applies the walk face at the inner frame's (c , J),
-- manufacturing the walk face's hypotheses from the existing context.
-- The hasDry conjunct (conjunct 8 of the 9-conjunct Σ, 0-indexed) is
-- extracted by the p2…p9 projection chain, exactly as in
-- subscribeE-wet-core.  The ℓ degeneracy bites: dBound degenerates at
-- zero hops/shares; fix is ℓ = B + (suc (pathLen κ) + G) (mirrors the
-- B + (pathLen κ + G) fix in subscribeE-wet-core).
subscribeE-inner-nodry-core : WalkLevel → ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
    ≤ sizeCapAt e sl (suc id) →
  gs fuel ≡ budgetAt e sl id →
  hasDry (proj₁ (subscribeE fuel o
           (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st))
    ≡ false
subscribeE-inner-nodry-core wl {n} {Γ} {t} {e} {u}
    c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
    J fuel op allNid κ id now o sched st ok pb sspLen vb rg nB hD cl gk =
  dry
  where
  inst   = Sched.nextNode sched
  sched' = record sched { nextNode = suc inst }
  B      = Caps.cSize (frameStep J c)
  -- the demand at the RESET caps (the pins' Ŝ), not the level cap:
  -- the level cap cannot ceiling the climb, and cl anchors it
  Ŝr     = sizeCapAt e sl (suc id)
  L̂      = opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J)
  G      = dBound Ŝr (hopR Ŝr) (unconn sl (EvalSt.connectedShares st))
                  (hopDᵉ Ŝr (slotHop Ŝr sl) o) (syncSizeᵉ o)
  ℓ      = B + (suc (pathLen κ) + G)

  -- slots unchanged by nextNode bump (definitional)
  slEq : Sched.slots sched' ≡ sl
  slEq = proj₁ (proj₁ ok)

  -- capsOK? definitionally ignores nextNode
  cOK : capsOK? (frameStep J c) sched' st ≡ true
  cOK = proj₂ (proj₁ ok)

  -- size of o: VbB → valsCaps? → all → valCaps? → sizeᵛ (obs u) o ≤ B
  vcaps : valsCaps? (frameStep J c) sl (o ∷ []) ≡ true
  vcaps = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ [])) (valsΨ? Ψ (o ∷ [])) vb)
  vcall : all (valCaps? (frameStep J c) sl (obs u)) (o ∷ []) ≡ true
  vcall = proj₁ (∧-true _ (length (o ∷ []) ≤ᵇ suc (Caps.cWid (frameStep J c))) vcaps)
  vc : valCaps? (frameStep J c) sl (obs u) o ≡ true
  vc = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs u) o) _ vcall)
  szO : sizeᵉ o ≤ B
  szO = ≤ᵇ⇒≤ (sizeᵉ o) B (T-to (proj₁ (∧-true _ _ vc)))

  -- fnCap of o: VbB → valsΨ? → valΨ? → fnCapᵛ (obs u) o ≤ Ψ
  vΨ : valsΨ? Ψ (o ∷ []) ≡ true
  vΨ = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ [])) (valsΨ? Ψ (o ∷ [])) vb)
  vΨ-hd : valΨ? Ψ (obs u) o ≡ true
  vΨ-hd = proj₁ (∧-true (valΨ? Ψ (obs u) o) _ vΨ)
  fnO : fnCapᵉ o ≤ Ψ
  fnO = ≤ᵇ⇒≤ (fnCapᵉ o) Ψ (T-to vΨ-hd)

  -- sizeᵉ o ≤ Ŝr: from szO (sizeᵉ o ≤ B) via the monotone J ≤ L̂ step
  sz≤Ŝr : sizeᵉ o ≤ Ŝr
  -- J ≤ opIterD … (suc J): one step up to suc J, then opIterD's own
  -- inflation at that level.  The cl ceiling now anchors at suc J, so the
  -- old `opIterD-infl … J` no longer meets it.
  sz≤Ŝr = ≤-trans szO
            (≤-trans (proj₁ (frameStep-mono-j c 2≤S
                               (≤-trans (n≤1+n J)
                                        (opIterD-infl (Caps.cSize c) (Caps.cWid c)
                                                      dep bud (suc (sizeᵉ o)) (suc J)))))
                     cl)

  -- THE PATH-LENGTH BOUND, DERIVED — cribbed from
  -- subscribeInner-caps, which pays the same unit the same way: extend the
  -- path by a frame, subscribe at one more j, and the chain bound carries.
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n J)
  B′     = Caps.cSize (frameStep (suc J) c)
  -- every caps-indexed hypothesis the walk face wants must move up with the
  -- level, exactly as subscribeInner-caps widens its own
  cOK′   : capsOK? (frameStep (suc J) c) sched' st ≡ true
  cOK′   = capsOK?-mono (frameStep J c) (frameStep (suc J) c) sched' st step⊑ cOK

  -- pathSz? AT THE EXTENDED PATH, BUILT rather than postulated.  This is
  -- subscribeInner-caps' `pC′` verbatim: the head frame is free (refl), the
  -- new length conjunct is the widened lC, and κ's own chain rides
  -- pathSz?-⊑ up the step.  Building it is what retires
  -- subscribeE-inner-nodry-pSz — the postulate existed only because the
  -- inner call sat at J, where the length conjunct was unreachable.
  pC     : pathSz? (Caps.cSize (frameStep J c)) κ ≡ true
  pC     = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                         (pathBΨ? Ψ κ) pb)
  pC′    : pathSz? B′ (from-inner op allNid inst ↠ κ) ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                        (≤⇒≤ᵇ (≤-trans sspLen (proj₁ step⊑))))
                      (pathSz?-⊑ κ step⊑ pC))
  pLen'  : suc (suc (pathLen κ)) ≤ B′
  pLen'  = frameStep-chain-suc c J (pathLen κ) 2≤S sspLen

  -- regsLen? ℓ via capsOK⇒regsLen + regsLen?-mono
  regsO : regsLen? ℓ (EvalSt.registry st) ≡ true
  regsO = regsLen?-mono B ℓ (EvalSt.registry st) (m≤m+n B _)
            (capsOK⇒regsLen (frameStep J c) sched st (proj₂ (proj₁ ok)))

  W = wl o c Ψ Ŝr Ŝr (hopR Ŝr) G ℓ L̂ dep bud (suc (sizeᵉ o)) (suc J)
         fuel (from-inner op allNid inst ↠ κ) id now sl sched' st
         2≤S 1≤R hCR slEq slC slSz cOK′ (≤-trans szO (proj₁ step⊑))
         (≤-trans (inner-dWO c sl Ψ J o vb) (proj₁ (proj₂ step⊑)))
         pC′
         pLen' nB ≤-refl
         hD
         (INV?-widen sched' st (proj₁ step⊑)
            (subscribeE-inner-nodry-inv c sl Ψ J sched st
               (≤-trans slSz (cSize≤frameStep c J 2≤S)) slFc
               (frameStep-reg≤size c J (≤-trans (s≤s z≤n) 2≤S) hCR)
               ok rg))
         fnO
         (pathB?-widen (from-inner op allNid inst ↠ κ) (proj₁ step⊑)
            (subscribeE-inner-nodry-pBO c Ψ J op allNid inst κ pb))
         -- the reset-anchor pins: floor from the entry lemma, F/R̂ by
         -- construction, ceiling from the caller's cl, budget ≤-refl
         (2≤capsAt-size e sl (suc id)) refl refl cl ≤-refl
         ≤-refl
         (subscribeE-inner-nodry-fuel c sl Ψ dep bud J fuel op allNid κ id now o sched st
                                      ok nB hD gk sz≤Ŝr)
         (m≤n+m (suc (pathLen κ) + G) B)
         regsO

  j′  = proj₁ W
  p2  = proj₂ W
  p3  = proj₂ p2
  p4  = proj₂ p3
  p5  = proj₂ p4
  p6  = proj₂ p5
  p7  = proj₂ p6
  p8  = proj₂ p7
  p9  = proj₂ p8
  dry = proj₁ p9

subscribeE-inner-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ []) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner (gs fuel) op allNid κ id now o sched st ≤ dep →
  -- the reset-anchor ceiling; see SiNodry
  Caps.cSize (frameStep (opIterD (Caps.cSize c) (Caps.cWid c) dep bud
                                 (suc (sizeᵉ o)) (suc J)) c)
    ≤ sizeCapAt e sl (suc id) →
  gs fuel ≡ budgetAt e sl id →
  hasDry (proj₁ (subscribeE fuel o
           (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
           (record sched { nextNode = suc (Sched.nextNode sched) }) st))
    ≡ false
subscribeE-inner-nodry = subscribeE-inner-nodry-core subscribeE-walk-level

-- EX-POSTULATE.  Two clauses, and the dry one is now impossible by
-- construction rather than by hypothesis.
subscribeInner-nodry : SiNodry
subscribeInner-nodry {e = e} c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc J g op allNid
                     κ id now o sched st ok pb sspLen vb rg nB hD cl gk
  with budgetAt-gs e sl id
... | g′ , eq
      rewrite trans gk eq =
      splitBurst-nodry
        (proj₁ (subscribeE g′ o
                 (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
                 (record sched { nextNode = suc (Sched.nextNode sched) }) st))
        (subscribeE-inner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc J g′ op allNid
           κ id now o sched st ok pb sspLen vb rg nB hD cl (sym eq))

-- THE CONCAT NODE'S STORED QUEUE IS VbB-BOUNDED, and this is a real body: the
-- leaves it stands on are all proven, so nothing here is postulated.  It is the
-- receipt `mergeAllDrain-nodry` drains against, and the whole reason that drain is
-- allowed to take one: the queue it is handed is not an arbitrary list but the
-- `q` of a `mergeAll-st` READ OUT OF THE NODE TABLE, which `capsOK?` bounds.
-- `innerReact-nodry` is the single site that performs the lookup, so the receipt
-- is minted there once and projected per element afterwards (`VbB-head` for the
-- element, `VbB-tail` for the recursive call).
--
-- ⚠ THIS REPLACES `mergeAllDrain-nodry-vb`, WHICH WAS REFUTABLE AS WRITTEN.  That
-- statement concluded `VbB c sl Ψ J (o ∷ [])` for an ARBITRARY `o : Closed Γ s`
-- from a hypothesis mentioning only `sched` and `st`, so it quantified over
-- expressions far larger than `cSize c` — a conclusion needing information no
-- hypothesis carried.  Adding a premise is licensed here precisely because the
-- unconditional form is FALSE, and because the premise is a genuine
-- precondition of the operation rather than a convenience of today's call site.
-- Note also what the repair is NOT: `o ∈ q` does not work, since `q` is itself a
-- free parameter of the drain — that relates one unconstrained thing to another.
-- The link has to reach the STATE, which is what makes `allNid` and this
-- equation load-bearing.
--
-- THE CENSUS, one proven source per conjunct of `VbB`, and `capsOK?` reaches
-- `nodes` three times to supply them:
--
--   all (valCaps? …) q     ← boundedNode's `all` (the sizeᵉ half, via
--                             capsOK?-nodeSz) zipped with widNode's first
--                             conjunct (the pWᵉ half, via capsOK?-nodeWid).
--                             `valCaps? C sl (obs s) o` IS that conjunction.
--   length q ≤ᵇ suc (cWid C) ← widNode's SECOND conjunct, `length q ≤ᵇ cWid C`,
--                             widened by one.
--   all (valΨ? …) q        ← fnCapNode's `all`, via OKB's fnCapBounded?
--                             conjunct.  `fnCapᵛ (obs s) o` IS `fnCapᵉ o`.
--
-- ⚠ AND THE LENGTH CONJUNCT IS THE CORRECTION WORTH KEEPING.  Two successive
-- readings of `capsOK?` got this census wrong in opposite directions.  The
-- first found only widNode, concluded the size and fn-cap halves had no source,
-- and proposed a new FIELD on widNode cascading through every producer and
-- consumer of capsOK?.  The second found those two and concluded the LENGTH had
-- no source above it, guessing the bound would have to come from an arrival-
-- ledger induction over the pushes.  Both were false, and for the same reason:
-- the reading stopped early.  `widNode`'s mergeAll clause COUNTS the queue
-- outright.  Read the whole record before concluding a conjunct is unreachable.
--
-- Sealed per the budget-sufficient-spine rule; the `with` on the slots equation
-- is why it is private-impl + abstract-alias rather than a plain block.
private
  mergeAllNode-vb-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    VbB c sl Ψ J q ≡ true
  mergeAllNode-vb-go {n = n} c sl Ψ J allNid lim act q od sched st ok eqN
    with proj₁ (proj₁ ok)
  ... | refl =
    let C   = frameStep J c
        cok = proj₂ (proj₁ ok)
        nc  = subst (NodeCaps C (Sched.slots sched)) eqN
                (lookupNode-caps C (Sched.slots sched) allNid (EvalSt.nodes st)
                   (capsOK?-nodeSz C sched st cok)
                   (capsOK?-nodeWid C sched st cok))
        nf  = subst (NodeΨ Ψ) eqN
                (lookupNode-fnCap Ψ allNid (EvalSt.nodes st)
                   (fcB-nodes Ψ sched st (proj₂ ok)))
        hwq = ∧-true (all (λ o → pWᵉ n (Sched.slots sched) o ≤ᵇ Caps.cWid C) q)
                     (length q ≤ᵇ Caps.cWid C) (proj₂ nc)
    in ∧-intro
         (∧-intro
            (all-zip (λ o → sizeᵉ o ≤ᵇ Caps.cSize C)
                     (λ o → pWᵉ n (Sched.slots sched) o ≤ᵇ Caps.cWid C)
                     _
                     (λ o hsz hwd → ∧-intro hsz hwd)
                     q (proj₁ nc) (proj₁ hwq))
            (≤ᵇ-widen (length q) (n≤1+n (Caps.cWid C)) (proj₂ hwq)))
         nf

abstract
  mergeAllNode-vb : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (Ψ J : ℕ) (allNid : NodeId)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    OKB {e = e} c sl Ψ J sched st →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    VbB c sl Ψ J q ≡ true
  mergeAllNode-vb = mergeAllNode-vb-go

-- ─────────────────────────────────────────────────────────────────
-- THE NODRY RESIDUE, NOW EMPTY.  `innerReact-nodry` / `thruOuter-nodry` are
-- real bodies that case-split the evaluator's dispatch and APPLY
-- `subscribeInner-nodry` at each arm calling `subscribeInner`; what those
-- bodies could not pay used to be postulated here.  Nothing is: the one
-- surviving member is `switchKill-context`, a real body, and the four NOTEs
-- below are what it and its neighbours THREAD rather than assert.

-- NOTE ON slFc: slotsFnCap sl ≤ Ψ is THREADED, not postulated.  It is a
-- static capsule invariant that OKB cannot reach — `walkOK` is
-- slots-eq × capsOK?, and capsOK? bounds live/nodes/registry/widths but
-- never the slot store's fn-weight; `fnCapBounded?` reads only
-- live/nodes.  So it rides beside its already-threaded size-side twin
-- `slotsSize sl ≤ cSize c`, all the way down through stepFrame-nodry,
-- innerReact-nodry/thruOuter-nodry and SiNodry, and is a PARAMETER of
-- module BurstWalk.  It costs nothing: at the true instantiation
-- Ψ := ΨAt e sl is `fnCapᵉ e + slotsFnCap sl`, so the whole chain is
-- discharged by `m≤n+m` at cascadeGo-burst-nodry — the same way
-- `caps-fuel-root` (.Wet/Part6) already discharges it.

-- NOTE ON ceiling, RESOLVED: the per-element ceiling is no
-- longer paid from the frame's fused `fLvlD` by an unstated inequality.
-- The thru walk threads an ABSTRACT ceiling level L̂ — `CL`'s own idiom,
-- one flavour down — and converts it to each element's budget with the
-- PROVEN Caps-Chain descents `inner-desc` then `walk-desc`.  The bud then
-- sits in the SAME `k` position on both sides of every step, so the
-- tension the *-nestBud rows were stuck on (one conjunct wants bud large,
-- the other wants it small) leaves the level algebra entirely; what
-- survives is a nest bound with no ceiling coupled to it, and one
-- k-and-index fit at the frame boundary.

-- NOTE ON loop invariants, RESOLVED: OKB/regP? after a
-- subscribeInner / thruConsume step are no longer leaves.  Each is the caps
-- face's own step (.Subscribe-Face) tensored with this module's Ψ face, with
-- `capsOK?-regs` and `regP?-of-parts` recombining the registry halves at the
-- level the step reports — so the level the walk re-reads its ledgers at is
-- CARRIED rather than asserted, which is what the refuted same-level form
-- (Refuted.Thru-Loop) got wrong.
-- OKB + regP? after switchKill; needed by the switch arm's
-- subscribeInner-nodry call.  A REAL BODY, and the whole of it is a
-- three-way split of the conjunction along the faces that already own the
-- pieces — nothing about `switchKill` is re-derived here.

-- WHY THIS ONE IS AT THE SAME LEVEL, where the thru side's same-level form
-- is REFUTED (Refuted.Thru-Loop): `switchKill` only ever DROPS.  It filters
-- the registry through `cutThrough`, sweeps `live` against the survivors and
-- grows `cancelled` — and `capsOK?` reads none of the last.  `thruConsume`'s
-- the mergeAll park GROWS a node's queue, which is what `capsOK?`'s width conjunct
-- bounds, so there a post-state need not satisfy the invariant at the level
-- its pre-state did.  Dropping cannot break an upper bound; appending can.

-- THE SPLIT.  `walkOK` is slots-eq × `capsOK?`, and the Ψ half is
-- `fnCapBounded?`, so the three pieces land on three faces:

--   Sched.slots ≡ sl    ← switchKill-Ψ's first conjunct (the record update
--                          touches `live`, never `slots`, so this is the
--                          hypothesis itself — but read it off the face that
--                          states it, not off record eta)
--   capsOK?             ← switchKill-caps (.Caps-Face/Part4), at frameStep J c
--   fnCapBounded?       ← switchKill-Ψ's second conjunct
--
-- and the registry ledger recombines entrywise: `regP?-Ψ` peels the Ψ half of
-- `PbB` to feed switchKill-Ψ, which hands the Ψ half back at the new state,
-- while the SIZE half comes out of the new `capsOK?` by `capsOK?-regs` —
-- `regsSz?` IS `regP?` of that half.  `regP?-of-parts` glues them.  Neither
-- face hands back the conjunction, which is why the peel-and-glue pair exists.
switchKill-context : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ J : ℕ)
  (cur : Maybe NodeId)
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  OKB {e = e} c sl Ψ J sched₀ st₀ →
  regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
  let sched₁ = proj₁ (proj₂ (switchKill cur sched₀ st₀))
      st₁    = proj₂ (proj₂ (switchKill cur sched₀ st₀))
  in OKB {e = e} c sl Ψ J sched₁ st₁
     × regP? (PbB c Ψ J) (EvalSt.registry st₁) ≡ true
switchKill-context c sl Ψ J cur sched₀ st₀ ((slEq , cOK) , fcb) rp =
  ((proj₁ Ψr , cOK₁) , proj₁ (proj₂ Ψr))
  , regP?-of-parts c Ψ J (EvalSt.registry st₁)
      (capsOK?-regs (frameStep J c) sched₁ st₁ cOK₁)
      (proj₁ (proj₂ (proj₂ Ψr)))
  where
  sched₁ = proj₁ (proj₂ (switchKill cur sched₀ st₀))
  st₁    = proj₂ (proj₂ (switchKill cur sched₀ st₀))
  cOK₁   = switchKill-caps (frameStep J c) cur sched₀ st₀ cOK
  Ψr     = switchKill-Ψ sl Ψ cur sched₀ st₀ slEq fcb
             (regP?-Ψ c Ψ J (EvalSt.registry st₀) rp)

-- THE DRAIN'S LOOP INVARIANT, at the level the step LANDS at.  Exact twin of
-- `thruConsume-nodry-loop`: the caps half is the caps face's own
-- `subscribeInner-caps`, the Ψ half is this module's `subscribeInner-Ψ`, and
-- the registry's two halves are recombined by `capsOK?-regs` (the size half,
-- read at the NEW level out of the invariant the step reports) and
-- `regP?-of-parts`.
--
-- THE LEVEL IS REPORTED AND NOT ASSUMED, for the reason the thru side's
-- same-level form was refuted (Refuted.Thru-Loop): the park clause GROWS
-- the node's queue, and `capsOK?`'s width conjunct bounds that queue's length,
-- so a step's post-state need not satisfy the invariant at the level its
-- pre-state did.  `subscribeInner-caps` reports STRICTLY (`suc (j + j′) ≤ …`);
-- one `n≤1+n` relaxes it to the form the drain's own descent consumes.
mergeAllDrain-nodry-loop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (sf : Gas)
  (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (q : List (Closed Γ s))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  OKB {e = e} c sl Ψ J sched₀ st₀ →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ q) ≡ true →
  nest o sl (EvalSt.connectedShares st₀) ≤ bud →
  depthInner sf mergeAllᵒ allNid κ id now o sched₀ st₀ ≤ dep →
  regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
  pathStrat? κ ≡ true →
  valsStrat? (pathFloor κ) (o ∷ q) ≡ true →
  let r      = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  in Σ ℕ (λ j′ →
          OKB {e = e} c sl Ψ (J + j′) sched₁ st₁
        × regP? (PbB c Ψ (J + j′)) (EvalSt.registry st₁) ≡ true
        × (J + j′ ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc J)))
mergeAllDrain-nodry-loop {s = s} c sl Ψ dep bud J sf allNid κ id now o q sched₀ st₀
                       2≤S 1≤R slC slSz ok pb sspLen vb nst hD rg stP stV =
  j′
  , ((slEq₁ , inv₁) , fc₁)
  , regP?-of-parts c Ψ (J + j′) (EvalSt.registry st₁)
      (capsOK?-regs (frameStep (J + j′) c) sched₁ st₁ inv₁) rg₁
  , ≤-trans (n≤1+n (J + j′)) lvl
  where
  slEq  = proj₁ (proj₁ ok) ; inv = proj₂ (proj₁ ok) ; fc = proj₂ ok
  pb-sz = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  pb-bΨ = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  vb-c  = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ q)) (valsΨ? Ψ (o ∷ q)) vb)
  vb-Ψ  = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ q)) (valsΨ? Ψ (o ∷ q)) vb)
  oC    = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs s) o)
                        (all (valCaps? (frameStep J c) sl (obs s)) q)
                        (valsOf (frameStep J c) sl (o ∷ q) vb-c))
  oΨ    = proj₁ (∧-true (valΨ? Ψ (obs s) o) (all (valΨ? Ψ (obs s)) q) vb-Ψ)
  oS    = proj₁ (∧-true (inputsBelowᵛ (pathFloor κ) (obs s) o)
                        (all (inputsBelowᵛ (pathFloor κ) (obs s)) q) stV)
  SI    = subscribeInner-caps c dep bud J sf mergeAllᵒ allNid κ id now o sl sched₀ st₀
            2≤S 1≤R slEq slC slSz inv oC pb-sz sspLen nst hD stP oS
  j′ = proj₁ SI ; inv₁ = proj₁ (proj₂ SI)
  lvl = proj₂ (proj₂ (proj₂ (proj₂ SI)))
  SΨ    = subscribeInner-Ψ sl Ψ sf mergeAllᵒ allNid κ id now o sched₀ st₀
            slEq fc (regP?-Ψ c Ψ J (EvalSt.registry st₀) rg) oΨ pb-bΨ
  slEq₁ = proj₁ SΨ ; fc₁ = proj₁ (proj₂ SΨ) ; rg₁ = proj₁ (proj₂ (proj₂ SΨ))
  r = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))

-- THE REMAINING QUEUE'S NEST LEDGER, ACROSS ONE STEP.  `nest` is antitone in
-- the connected set and `subscribeInner` only ever enlarges it, which is
-- exactly what the share-ledger ring proves per step; `mList?-keeps` lifts it
-- over the whole queue.  Nothing about the step's own element is needed.
mergeAllDrain-nodry-nestRec : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (bud : ℕ) (sf : Gas)
  (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (q : List (Closed Γ s))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  mList? bud sl (EvalSt.connectedShares st₀) q ≡ true →
  let st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂
              (subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀)))))
  in mList? bud sl (EvalSt.connectedShares st₁) q ≡ true
mergeAllDrain-nodry-nestRec sl bud sf allNid κ id now o q sched₀ st₀ h =
  mList?-keeps bud sl (EvalSt.connectedShares st₀)
    (EvalSt.connectedShares
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀)))))))
    q (KeepsC.connMono (subscribeInner-keeps sf mergeAllᵒ allNid κ id now o sched₀ st₀)) h

------------------------------------------------------------------
-- mergeAllDrain-nodry — structural recursion over the mergeAll queue.
-- Applies subscribeInner-nodry at each element (THE FIT TEST).
--
-- slFc is taken as a direct parameter, threaded from module BurstWalk.
mergeAllDrain-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  -- THE QUEUE'S RECEIPT, minted once by `mergeAllNode-vb` at the node lookup in
  -- `innerReact-nodry` and projected per element here.  A genuine
  -- precondition and not a convenience of the call site: the unconditional
  -- per-element form (the retired `mergeAllDrain-nodry-vb`, git history) is
  -- refutable,
  -- because nothing ties a free `Closed Γ s` to this state.
  VbB c sl Ψ J q ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthDrain sf allNid κ id now q sched st ≤ dep →
  -- THE DRAIN'S THREE CHANNELS, and all three arrive from the caller — which
  -- is a RESTATEMENT and not a convenience.  The bud-and-ceiling pair used to
  -- be manufactured out of `ok` alone by `mergeAllDrain-nodry-nestBud`, and both
  -- of its conjuncts are refutable that way
  -- (`Refuted.MergeAll-Drain.mergeAllDrain-nodry-nestBud-absurd`): a free
  -- `Closed Γ s` has no nest bound, and OKB relates a `c`-derived cap to
  -- `sizeCapAt e sl` not at all.  What the refutation also showed is that the
  -- two must be DECOUPLED — one conjunct wanted the bud large, the other small
  -- — so the ceiling is now an abstract level L̂ and the bud rides beside it,
  -- meeting only through the proven Caps-Chain descents.
  --
  -- `sIterD … (length q) J` is the level this drain climbs to, one `sLvlD` per
  -- queue element, which is exactly what the caps face's `mergeAllDrain-caps`
  -- (.Subscribe-Face) already measures the same drain against.
  mList? bud sl (EvalSt.connectedShares st) q ≡ true →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length q) J ≤ L̂ →
  -- THE QUEUE'S OWN READING, and it arrives from the caller for the same
  -- reason `VbB c sl Ψ J q` does: a parked payload is state, so the fact
  -- is minted once at the node lookup and projected per element here
  pathStrat? κ ≡ true →
  valsStrat? (pathFloor κ) q ≡ true →
  any dryEvent (proj₁ (proj₂ (mergeAllDrain sf allNid κ id now lim act q sched st))) ≡ false

mergeAllDrain-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  lim act [] sched st _ _ _ _ _ _ _ _ _ _ _ _ = refl

mergeAllDrain-nodry {e = e} {s = s} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf allNid κ id now
                  lim act (o ∷ q) sched₀ st₀ ok pb sspLen vbq rg gk hD nst clL̂ dsc stP stV
  -- THE ONLY SCRUTINY IS THE GATE.  An inner that stays open no longer
  -- ends the walk — it spends a lane — so `done` never branches the
  -- drain, and is read only as the counter the tail is called at
  with hasRoom lim act
-- the gate is shut: the drain emits nothing at all
... | false = refl
--
-- The head's outputs are LET-BOUND PROJECTIONS, never `with`-scrutinised —
-- the same reason as `thruWalk-nodry`'s cons arm: abstracting the tuple
-- rebinds `sched₁`/`st₁` as fresh variables while `ok₁`/`rg₁` keep mentioning
-- a `proj… (subscribeInner …)` the abstraction never touched.
... | true =
  let step   = subscribeInner sf mergeAllᵒ allNid κ id now o sched₀ st₀
      bs     = proj₁ (proj₂ (proj₂ step))
      done   = proj₁ (proj₂ (proj₂ (proj₂ step)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ step))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ step))))
      S      = Caps.cSize c
      W      = Caps.cWid  c
      -- the nest ledger, split at the head by the ring's own projections
      nBst   = mList?-head bud sl (EvalSt.connectedShares st₀) o q nst
      nstT   = mList?-tail bud sl (EvalSt.connectedShares st₀) o q nst
      -- THE HEAD'S CEILING, by the two proven descents: this element's inner
      -- subscribe sits inside the drain's own step (`inner-desc`, on the
      -- element's SIZE and not on bud), and that step inside the drain
      -- (`walk-desc`).  Neither move mentions the ceiling, which is what
      -- decoupled the bud from it.
      dsc₀   = ≤-trans (inner-desc S W dep bud J (sizeᵉ o) 2≤S
                          (nodry-elem-size c sl Ψ J o q 2≤S vbq))
                       (≤-trans (walk-desc S W dep (suc bud) (length q) J) dsc)
      hDo    = ≤-trans (m≤m⊔n _ _) hD
      h-head = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                 J sf mergeAllᵒ allNid κ id now o sched₀ st₀
                 ok pb sspLen (VbB-head c sl Ψ J o q vbq) rg nBst hDo
                 (≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc₀)) clL̂) gk
      loop   = mergeAllDrain-nodry-loop c sl Ψ dep bud J sf allNid κ id now o q sched₀ st₀
                 2≤S 1≤R slC slSz ok pb sspLen vbq nBst hDo rg stP stV
      stVT   = proj₂ (∧-true (inputsBelowᵛ (pathFloor κ) (obs s) o)
                             (all (inputsBelowᵛ (pathFloor κ) (obs s)) q) stV)
      j₁     = proj₁ loop
      ok₁    = proj₁ (proj₂ loop)
      rg₁    = proj₁ (proj₂ (proj₂ loop))
      hj₁    = proj₂ (proj₂ (proj₂ loop))
      -- every OTHER ledger is read again at the level the step landed at, and
      -- every one of them WIDENS upward; the ceiling is the only conjunct that
      -- gets harder, and `dsc₁` is where it is paid
      le₁    = m≤m+n J j₁
      mono₁  = frameStep-mono-j c 2≤S le₁
      pb₁    = ∧-intro (pathSz?-widen κ (proj₁ mono₁)
                          (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                         (pathBΨ? Ψ κ) pb)))
                       (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                      (pathBΨ? Ψ κ) pb))
      sspL₁  = ≤-trans sspLen (proj₁ mono₁)
      vbT    = VbB-tail c sl Ψ J o q vbq
      vb₁    = ∧-intro (valsCaps?-lvl _ _ sl q mono₁
                          (proj₁ (∧-true (valsCaps? (frameStep J c) sl q)
                                         (valsΨ? Ψ q) vbT)))
                       (proj₂ (∧-true (valsCaps? (frameStep J c) sl q)
                                      (valsΨ? Ψ q) vbT))
      nst₁   = mergeAllDrain-nodry-nestRec sl bud sf allNid κ id now o q sched₀ st₀ nstT
      dsc₁   = ≤-trans (sIterD-mono (length q) (length q) dep dep (suc bud) (suc bud)
                          2≤S ≤-refl ≤-refl hj₁ ≤-refl ≤-refl ≤-refl)
                       (≤-trans (≤-reflexive (sym (sIterD-suc S W dep (suc bud) (length q) J)))
                                dsc)
      h-tail = mergeAllDrain-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc (J + j₁) sf
                 allNid κ id now lim (if done then act else suc act)
                 q sched₁ st₁ ok₁ pb₁ sspL₁ vb₁ rg₁ gk
                 (≤-trans (m≤n⊔m _ _) hD) nst₁ clL̂ dsc₁ stP stVT
  in any-dry-++ bs _ h-head h-tail

-- Loop invariant after one thruConsume step: OKB + regP? at the level
-- the step LANDS at, with that level reported.
--
--
-- WHY.  The park clause is a pure GROWTH step: with the node's lanes
-- all taken, `thruConsume` appends the element to the node's
-- queue and emits nothing — which is exactly why the nodry conclusion
-- is `refl` there, and why nothing else in this block notices.  And
-- `capsOK?`'s width conjunct bounds that queue's LENGTH
-- (`widNode`'s `length q ≤ᵇ W`).  A queue sitting AT the cap is one
-- park from breaching it, and the same-level telescope said nothing about
-- the queue at all: CLAUDE.md's first almost-always-wrong shape.
--
-- IT IS NOT A ZERO-CAP ARTIFACT: the witness's caps are read off the
-- value (cSize 3, cWid 2, both pinned by `refl`), every other conjunct
-- held with margin, and the only tight one was the length.  Threading
-- `vb : VbB c sl Ψ J vals` would NOT have repaired it either: VbB bounds
-- each element, never the queue's length.
--
-- THE REPAIR IS A REPORTED LEVEL, NOT A HYPOTHESIS — conditioning on the
-- queue would be the "call site happens to supply it" trade, since the
-- walk's SECOND element cannot supply it: the FIRST is what filled the
-- queue.  So the step reports the level it lands at, and the walk above
-- re-reads its ledgers there.
--
-- AND THE REPORTED CEILING IS `sLvlD`, NOT `fIterD`.  The first reading of
-- this defect took `pushThru-walk` for the mirror and so wrote the walk's
-- index as `fIterD` over `length str` — one whole FRAME per payload, which
-- is the wrong granularity and does not fit under the frame's own charge
-- (`fLvlD` is inflationary, so k frames cannot sit inside one).  The
-- mirror is `stepThru-walk`, which measures THIS traversal — a value list
-- inside one frame — against `sIterD S W dep (suc bud) (length vals) j`,
-- one `sLvlD` per payload.  Diffing the two mirrors' ARGUMENTS is what
-- separated them; their statements read alike.
--
-- IT WAS CLASSED GRINDABLE on the grounds that it is pure preservation,
-- hypothesis P at state₀ and conclusion P at state₁.  That reading is
-- the trap: preservation is only cheap when the step cannot grow the
-- thing preserved, and this step exists to grow it.  Shape-checking a
-- statement against `hypothesis ⇒ conclusion` says nothing about the
-- STEP in between.
--
-- ⚠ REFUTED IN THE SAME-LEVEL FORM — `Refuted.Thru-Loop`,
--   and the witness computes: `capsOK?` on the post-state evaluates to
--   `false` while the conclusion demanded `true`.

-- IT IS NO LONGER A POSTULATE.  `thruConsume-caps` (.Subscribe-Face) is this
-- step's caps face, PROVEN, and it already reports the landing level in the
-- `sLvlD` shape above; this module's own `thruConsume-Ψ` is the other half.
-- What the postulate was missing was not a proof but the hypotheses the
-- report actually needs: a level report cannot come out of OKB and regP?
-- alone, since neither mentions the element, the bud or the depth fuel it is
-- measured against.  Those arrive here, and the postulate goes away entirely
-- rather than trading tracked debt for a signature.
thruConsume-nodry-loop : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud J : ℕ) (sf : Gas)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) (os : List (Val Γ (obs u)))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  OKB {e = e} c sl Ψ J sched₀ st₀ →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  nest o sl (EvalSt.connectedShares st₀) ≤ bud →
  depthConsume sf op nid κ id now o sched₀ st₀ ≤ dep →
  regP? (PbB c Ψ J) (EvalSt.registry st₀) ≡ true →
  pathStrat? κ ≡ true →
  valsStrat? (pathFloor κ) (o ∷ os) ≡ true →
  let r      = thruConsume sf op nid κ id now o sched₀ st₀
      sched₁ = proj₁ (proj₂ (proj₂ r))
      st₁    = proj₂ (proj₂ (proj₂ r))
  in Σ ℕ (λ j′ →
          OKB {e = e} c sl Ψ (J + j′) sched₁ st₁
        × regP? (PbB c Ψ (J + j′)) (EvalSt.registry st₁) ≡ true
        × (J + j′ ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc J)))
thruConsume-nodry-loop {u = u} c sl Ψ dep bud J sf op nid κ id now o os sched₀ st₀
                       2≤S 1≤R slC slSz ok pb sspLen vb nst hD rg stP stV =
  j′
  , ((slEq₁ , inv₁) , fc₁)
  , regP?-of-parts c Ψ (J + j′) (EvalSt.registry st₁)
      (capsOK?-regs (frameStep (J + j′) c) sched₁ st₁ inv₁) rg₁
  , ≤-trans (n≤1+n (J + j′)) lvl
  where
  slEq  = proj₁ (proj₁ ok)
  inv   = proj₂ (proj₁ ok)
  fc    = proj₂ ok
  -- ∧-true's two Bool sides are given EXPLICITLY throughout, per this
  -- module's standing note: PbB, VbB and `all` on a cons all reduce to
  -- conjunctions the unifier will not recover from the equation alone.
  pb-sz = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  pb-bΨ = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ) (pathBΨ? Ψ κ) pb)
  vb-c  = proj₁ (∧-true (valsCaps? (frameStep J c) sl (o ∷ os))
                        (valsΨ? Ψ (o ∷ os)) vb)
  vb-Ψ  = proj₂ (∧-true (valsCaps? (frameStep J c) sl (o ∷ os))
                        (valsΨ? Ψ (o ∷ os)) vb)
  oC    = proj₁ (∧-true (valCaps? (frameStep J c) sl (obs u) o)
                        (all (valCaps? (frameStep J c) sl (obs u)) os)
                        (valsOf (frameStep J c) sl (o ∷ os) vb-c))
  oΨ    = proj₁ (∧-true (valΨ? Ψ (obs u) o) (all (valΨ? Ψ (obs u)) os) vb-Ψ)
  oS    = proj₁ (∧-true (inputsBelowᵛ (pathFloor κ) (obs u) o)
                        (all (inputsBelowᵛ (pathFloor κ) (obs u)) os) stV)
  TC    = thruConsume-caps c dep bud J sf op nid κ id now o sl sched₀ st₀
            2≤S 1≤R slEq slC slSz inv oC pb-sz sspLen nst hD stP oS
  j′    = proj₁ TC
  inv₁  = proj₁ (proj₂ TC)
  lvl   = proj₂ (proj₂ (proj₂ (proj₂ TC)))
  TΨ    = thruConsume-Ψ sl Ψ sf op nid κ id now o sched₀ st₀
            slEq fc (regP?-Ψ c Ψ J (EvalSt.registry st₀) rg) oΨ pb-bΨ
  slEq₁ = proj₁ TΨ
  fc₁   = proj₁ (proj₂ TΨ)
  rg₁   = proj₁ (proj₂ (proj₂ TΨ))
  r      = thruConsume sf op nid κ id now o sched₀ st₀
  sched₁ = proj₁ (proj₂ (proj₂ r))
  st₁    = proj₂ (proj₂ (proj₂ r))

------------------------------------------------------------------
-- thruConsume-nodry — per-element nodry proof for one thruConsume step.
-- Applies subscribeInner-nodry in each arm that calls subscribeInner.
thruConsume-nodry : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (os : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  -- THE WALK'S DEPTH, NOT THE FRAME'S.  `depthFrame`'s thru-outer clause is
  -- `suc (depthWalk …)` — the frame is the one arc of the cycle that re-reads
  -- the budget — so the walk and everything under it is stated one fuel
  -- below the frame, exactly as `fLvlD S W (suc d) J` unfolds to its payload
  -- walk at `d`.  `thruOuter-nodry` pays the `suc` once, where it is minted.
  depthWalk sf op nid κ id now (o ∷ os) sched st ≤ dep →
  -- THE CEILING, at an ABSTRACT LEVEL.  The walk cannot hand every element
  -- the frame's own `fLvlD`: that level is one whole frame's climb, and
  -- `fLvlD` being inflationary, k of them do not fit inside one.  So the
  -- ceiling arrives at a level L̂ the walk owns, and this element's own
  -- operator sweep is placed under it.
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J) ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (thruConsume sf op nid κ id now o sched st))) ≡ false

-- helper: apply subscribeInner-nodry for one thruConsume call.
--
-- The depth premise (`depthFrame … ≤ dep`) and the size-cap premise are
-- DELIBERATELY ABSENT: the body derives both element-level facts from
-- `ok` via thruConsume-nodry-dep / -nestBud, so neither was ever an
-- ingredient.  Carrying them was not merely redundant — `depthFrame`
-- unfolds through `thruConsume`, so in the mergeAll/exhaust arms (whose
-- clauses sit under a `with` on `lookupNode`) the premise's type is
-- stated against the ABSTRACTED scrutinee while the caller's `hD` is
-- stated against the unabstracted one, and the two are compared at
-- `Sched Γ` and differ.  Dropping the dead premises removes the
-- comparison entirely.  This STRENGTHENS the helper (fewer hypotheses).
thruConsume-nodry-apply : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (os : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J (o ∷ os) ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthInner sf op nid κ id now o sched st ≤ dep →
  -- THE CEILING, threaded rather than conjured, and now at an abstract
  -- level: the *-nestBud form that manufactured a bud AND a ceiling out of
  -- `ok` alone was refutable in both halves (`Refuted.MergeAll-Drain`), so both
  -- arrive from the caller and the level descent does the rest.
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc (sizeᵉ o)) (suc J) ≤ L̂ →
  any dryEvent (proj₁ (proj₂ (proj₂ (subscribeInner sf op nid κ id now o sched st)))) ≡ false
thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now o os sched st ok pb sspLen vb rg gk hD-elem nBst clL̂ dsc =
  subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
    J sf op nid κ id now o sched st
    ok pb sspLen (VbB-head c sl Ψ J o os vb) rg nBst hD-elem
    (≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc)) clL̂) gk

-- FLATTEN: dispatch on node state.
-- The scrutinee and the clause ORDER both mirror Rx.Evaluator's own
-- `with w ≟ᵗ u` exactly.  Writing `w ≟ᵗ _` here does not abstract the
-- goal's occurrence (the metavariable is not syntactically the
-- evaluator's `u`), leaving the with-function stuck and `refl` red.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _     = refl
...   | yes refl with hasRoom lim act
-- a lane is free: one subscribeInner call, events = bs
...     | true  =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) hD) nBst clL̂ dsc
-- the gate is shut: the element is parked and nothing is emitted
...     | false = refl
-- other node shapes: thruConsume's own catch-all emits [].  These are
-- enumerated rather than written `| _`, because a VARIABLE scrutinee
-- leaves the evaluator's with-function stuck — its catch-all only fires
-- once Agda knows the shape is none of the mergeAll cases.
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | nothing = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (scan-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (take-st _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (switch-st _ _) = refl
thruConsume-nodry {u = u} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf mergeAllᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
    | just (exhaust-st _ _) = refl

-- SWITCH: switchKill (closes only, nodry by switchKill-closes-nodry)
--         + subscribeInner (bs, nodry by SiNodry), combined by any-dry-++
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf switchᵒ nid κ id now o os sched₀ st₀ ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st₀)
-- NO `with subscribeInner …` here.  Scrutinising the tuple rebinds its
-- third component as a FRESH variable `bs`, which no longer unifies with
-- the `proj₁ (proj₂ (proj₂ (subscribeInner …)))` that both the goal and
-- `subscribeInner-nodry`'s conclusion mention.  Leaving the projection
-- standing keeps the two syntactically equal, and `any-dry-++`'s second
-- argument is then inferred from `h-bs`.
... | just (switch-st cur od) =
  let sched₁    = proj₁ (proj₂ (switchKill cur sched₀ st₀))
      st₁        = proj₂ (proj₂ (switchKill cur sched₀ st₀))
      h-closes   = switchKill-closes-nodry cur sched₀ st₀
      ctx₁       = switchKill-context c sl Ψ J cur sched₀ st₀ ok rg
      ok₁        = proj₁ ctx₁
      rg₁        = proj₂ ctx₁
      -- VbB is state-independent (valsCaps? ∧ valsΨ? depend only on vals and caps)
      vb-elem    = VbB-head c sl Ψ J o os vb
      -- the nest bound arrives at st₀ and is spent at st₁; the CEILING is
      -- state-free, so only the nest half needs carrying across the kill
      nB         = switchKill-nest sl bud cur o sched₀ st₀ nBst
      cl-elem    = ≤-trans (proj₁ (frameStep-mono-j c 2≤S dsc)) clL̂
      -- depthConsume switchᵒ routes through depthConsumeS, which on a
      -- switch-st node IS depthInner at the POST-switchKill state — exactly
      -- sched₁/st₁ above.  So the same ⊔/suc projection serves here.
      hD-elem    = ≤-trans (m≤m⊔n _ _) hD
      h-bs       = subscribeInner-nodry c sl Ψ dep bud 2≤S 1≤R hCR slC slSz slFc
                     J sf switchᵒ nid κ id now o sched₁ st₁
                     ok₁ pb sspLen vb-elem rg₁ nB hD-elem cl-elem gk
  in any-dry-++ (proj₁ (switchKill cur sched₀ st₀)) _ h-closes h-bs
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (exhaust-st _ _) = refl

-- EXHAUST active=true: drops the payload, emits []
thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk hD nBst clL̂ dsc
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = refl
-- EXHAUST active=false: subscribes, emits bs
... | just (exhaust-st false od) =
  thruConsume-nodry-apply c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf exhaustᵒ nid κ id now o os sched st ok pb sspLen vb rg gk
    (≤-trans (m≤m⊔n _ _) hD) nBst clL̂ dsc
... | nothing = refl
... | just (scan-st _) = refl
... | just (take-st _) = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _) = refl

------------------------------------------------------------------
-- thruWalk-nodry — structural recursion over vals.
thruWalk-nodry : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ dep bud L̂ : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) (sf : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep J c) →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  depthWalk sf op nid κ id now vals sched st ≤ dep →
  -- THE WALK'S CEILING CHANNEL.  `sIterD … (length vals) J` is the level
  -- this traversal climbs to — one `sLvlD` per payload, which is what
  -- `stepThru-walk` (.Walk-Level) already measures the same `thruWalk`
  -- against — and L̂ is any level that covers it.
  mList? bud sl (EvalSt.connectedShares st) vals ≡ true →
  Caps.cSize (frameStep L̂ c) ≤ sizeCapAt e sl (suc id) →
  sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) J ≤ L̂ →
  pathStrat? κ ≡ true →
  valsStrat? (pathFloor κ) vals ≡ true →
  any dryEvent (proj₁ (proj₂ (thruWalk sf op nid κ id now vals sched st))) ≡ false

thruWalk-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now
               [] sched st _ _ _ _ _ _ _ _ _ _ _ _ = refl

-- The head's outputs are LET-BOUND PROJECTIONS, never `with`-scrutinised.
-- Abstracting the tuple rebinds `sched₁`/`st₁` as fresh variables, but the
-- types of everything introduced afterwards (`ok₁`, `rg₁` from
-- thruConsume-nodry-loop) still mention `proj… (thruConsume …)` — a fresh
-- instance the abstraction never touched — so the recursive call's OKB
-- argument is compared at `Sched Γ` against a variable and fails.
thruWalk-nodry {u = u} {e = e} c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now
               (o ∷ os) sched₀ st₀ ok pb sspLen vb rg gk hD nst clL̂ dsc stP stV =
  let step   = thruConsume sf op nid κ id now o sched₀ st₀
      bs     = proj₁ (proj₂ step)
      sched₁ = proj₁ (proj₂ (proj₂ step))
      st₁    = proj₂ (proj₂ (proj₂ step))
      S      = Caps.cSize c
      W      = Caps.cWid  c
      -- the nest ledger, split at the head by the ring's own projections
      nBst   = mList?-head bud sl (EvalSt.connectedShares st₀) o os nst
      nstT   = mList?-tail bud sl (EvalSt.connectedShares st₀) o os nst
      -- THE HEAD'S CEILING, by the two proven descents: this element's
      -- operator sweep sits inside the walk's own step (`inner-desc`, on
      -- the element's SIZE and not on bud), and that step inside the walk
      -- (`walk-desc`).  Neither move mentions the ceiling, which is what
      -- decoupled the bud from it.
      dsc₀   = ≤-trans (inner-desc S W dep bud J (sizeᵉ o) 2≤S
                          (nodry-elem-size c sl Ψ J o os 2≤S vb))
                       (≤-trans (walk-desc S W dep (suc bud) (length os) J) dsc)
      h-head = thruConsume-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc J sf op nid κ id now o os
                 sched₀ st₀ ok pb sspLen vb rg gk hD nBst clL̂ dsc₀
      loop   = thruConsume-nodry-loop c sl Ψ dep bud J sf op nid κ id now o os sched₀ st₀
                 2≤S 1≤R slC slSz ok pb sspLen vb nBst (≤-trans (m≤m⊔n _ _) hD) rg
                 stP stV
      j₁     = proj₁ loop
      ok₁    = proj₁ (proj₂ loop)
      rg₁    = proj₁ (proj₂ (proj₂ loop))
      hj₁    = proj₂ (proj₂ (proj₂ loop))
      -- every OTHER ledger is read again at the level the step landed at,
      -- and every one of them WIDENS upward; the ceiling is the only
      -- conjunct that gets harder, and `dsc₁` is where it is paid
      le₁    = m≤m+n J j₁
      mono₁  = frameStep-mono-j c 2≤S le₁
      pb₁    = ∧-intro (pathSz?-widen κ (proj₁ mono₁)
                          (proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                         (pathBΨ? Ψ κ) pb)))
                       (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) κ)
                                      (pathBΨ? Ψ κ) pb))
      sspL₁  = ≤-trans sspLen (proj₁ mono₁)
      -- {e} is a PHANTOM on VbB-tail: VbB does not mention e, so nothing
      -- in the explicit arguments or the conclusion can solve it.
      vbT    = VbB-tail c sl Ψ J o os vb
      vb₁    = ∧-intro (valsCaps?-lvl _ _ sl os mono₁
                          (proj₁ (∧-true (valsCaps? (frameStep J c) sl os)
                                         (valsΨ? Ψ os) vbT)))
                       (proj₂ (∧-true (valsCaps? (frameStep J c) sl os)
                                      (valsΨ? Ψ os) vbT))
      nst₁   = thruConsume-nodry-nestRec sl bud sf op nid κ id now o os sched₀ st₀ nstT
      hD₁    = thruWalk-nodry-dep dep sf op nid κ id now o os sched₀ st₀ hD
      dsc₁   = ≤-trans (sIterD-mono (length os) (length os) dep dep (suc bud) (suc bud)
                          2≤S ≤-refl ≤-refl hj₁ ≤-refl ≤-refl ≤-refl)
                       (≤-trans (≤-reflexive (sym (sIterD-suc S W dep (suc bud) (length os) J)))
                                dsc)
      stVT   = proj₂ (∧-true (inputsBelowᵛ (pathFloor κ) (obs u) o)
                             (all (inputsBelowᵛ (pathFloor κ) (obs u)) os) stV)
      h-tail = thruWalk-nodry c sl Ψ dep bud L̂ 2≤S 1≤R hCR slC slSz slFc (J + j₁) sf op nid κ id now
                 os sched₁ st₁ ok₁ pb₁ sspL₁ vb₁ rg₁ gk hD₁ nst₁ clL̂ dsc₁ stP stVT
  -- the tail's event list is NAMED rather than left as `_`: with the head's
  -- outputs let-bound (see above) there is no with-pattern to fix it.
  in any-dry-++ bs (proj₁ (proj₂ (thruWalk sf op nid κ id now os sched₁ st₁)))
                h-head h-tail

------------------------------------------------------------------
-- innerReact-nodry — from-inner frame; real body applying mergeAllDrain-nodry.
-- All arms except mergeAllᵒ + (just (mergeAll-st lim act q od)) + yes refl
-- emit [].
innerReact-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {s} (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId)
  (path′ : Path Γ s t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (from-inner op allNid inst ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now (from-inner op allNid inst) path′ vals fin sched st ≤ d →
  -- THE FRAME'S OWN READING.  Only the chain half is forwarded — the
  -- payload half here is about `vals`, and what the drain subscribes is
  -- the NODE's queue, which `frame-parkStrat` supplies at the lookup
  pathStrat? path′ ≡ true →
  valsStrat? (pathFloor path′) vals ≡ true →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                               path′ vals fin sched st)))
    ≡ false

-- switch's innerFinish arm, lifted OUT of innerReact-nodry.  Agda cannot
-- return to an outer `with` level with `...` once a nested `with` has been
-- opened, so innerReact-nodry is allowed exactly ONE nested `with` (mergeAll's
-- `w ≟ᵗ s`) and it must be the LAST clause.  switch's `c₀ ≡ᵇ inst` test lives
-- here instead; both of its branches emit [].
innerFinish-switch-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (allNid inst c₀ : NodeId) (path′ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s)) (od : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  any dryEvent
      (proj₁ (proj₂ (innerFinish sf switchᵒ allNid inst path′ id now vals sched st
                                 (just (switch-st (just c₀) od)))))
    ≡ false
innerFinish-switch-nodry sf allNid inst c₀ path′ id now vals od sched st
  with c₀ ≡ᵇ inst
... | true  = refl
... | false = refl

-- fin = false: innerReact emits []
innerReact-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J {s} sf id now op allNid inst path′ vals fin sched st
                 ok pb vb rg gk cl hD hps hvs
  with fin
... | false = refl
-- fin = true, alive-through check passes: emits []
... | true  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
...   | true  = refl
-- fin = true, alive-through fails: dispatch to innerFinish
-- The node shapes are ENUMERATED for every op rather than closed with
-- `| _`.  innerFinish's own catch-all clause only fires once Agda can
-- rule out its four specific (op, node) clauses, which a variable
-- scrutinee never does — it stays stuck and `refl` is red.
-- `in eqN` CAPTURES THE LOOKUP EQUATION, which is what `mergeAllNode-vb` needs
-- in the mergeAll arm below and what a plain `with` discards.  It costs no
-- clause changes anywhere in this 30-arm block: `in` NAMES the proof, it does
-- not add a pattern position — nor a `with` nesting level, which this
-- function has no room for (see the note above).
...   | false with op | lookupNode allNid (EvalSt.nodes st) in eqN
-- FLATTEN: every arm EXCEPT the type-matching one emits []
...     | mergeAllᵒ | nothing                      = refl
...     | mergeAllᵒ | just (scan-st _)             = refl
...     | mergeAllᵒ | just (take-st _)             = refl
...     | mergeAllᵒ | just (switch-st _ _)         = refl
...     | mergeAllᵒ | just (exhaust-st _ _)        = refl
-- SWITCH: innerFinish emits []
...     | switchᵒ | just (switch-st (just c₀) od) =
            innerFinish-switch-nodry sf allNid inst c₀ path′ id now vals od sched st
...     | switchᵒ | just (switch-st nothing od)   = refl
...     | switchᵒ | nothing                       = refl
...     | switchᵒ | just (scan-st _)              = refl
...     | switchᵒ | just (take-st _)              = refl
...     | switchᵒ | just (mergeAll-st _ _ _ _)           = refl
...     | switchᵒ | just (exhaust-st _ _)         = refl
-- EXHAUST: innerFinish emits []
...     | exhaustᵒ | just (exhaust-st act od)     = refl
...     | exhaustᵒ | nothing                      = refl
...     | exhaustᵒ | just (scan-st _)             = refl
...     | exhaustᵒ | just (take-st _)             = refl
...     | exhaustᵒ | just (mergeAll-st _ _ _ _)          = refl
...     | exhaustᵒ | just (switch-st _ _)         = refl
-- FLATTEN, type-matching: THE ONLY arm that calls mergeAllDrain →
-- subscribeInner, and so the only one where subscribeInner-nodry is
-- APPLIED.  It opens the function's single nested `with` and therefore
-- must be the LAST clause — nothing may follow it.
...     | mergeAllᵒ | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...       | no _    = refl
...       | yes refl =
              let -- Strip the from-inner frame from pb to get PbB for path′.
                  -- ∧-true's Bool arguments are EXPLICIT: PbB reduces to a
                  -- conjunction Agda cannot recover from the equation alone.
                  pb-sz   = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′))
                                          (pathBΨ? Ψ (from-inner op allNid inst ↠ path′)) pb)
                  pb-bΨ   = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′))
                                          (pathBΨ? Ψ (from-inner op allNid inst ↠ path′)) pb)
                  -- frameBΨ? Ψ (from-inner _ _ _) = true, so
                  -- pathBΨ? Ψ (from-inner … ↠ path′) reduces DEFINITIONALLY
                  -- to pathBΨ? Ψ path′ — pb-bΨ is already the tail fact and
                  -- needs no ∧-true (which only reintroduced an ambiguous
                  -- `{s}` on the bare frame).
                  pb′     = ∧-intro
                              (pathSz?-tail (Caps.cSize (frameStep J c)) (from-inner op allNid inst) path′ pb-sz)
                              pb-bΨ
                  sspLen  = pathSz?-len (Caps.cSize (frameStep J c)) (from-inner op allNid inst ↠ path′) pb-sz
                  S       = Caps.cSize c
                  W       = Caps.cWid  c
                  vbq     = mergeAllNode-vb c sl Ψ J allNid lim act q od sched st ok eqN
                  vbq-c   = proj₁ (∧-true (valsCaps? (frameStep J c) sl q)
                                          (valsΨ? Ψ q) vbq)
                  -- THE DRAIN'S BUD IS THE FRAME'S REFRESH, exactly as at the
                  -- thru-outer boundary: `valsCaps→mList-strict` bounds every
                  -- queued payload's nesting by `sizeAt S (suc J)` at EVERY
                  -- share ledger, out of the per-element size half and the
                  -- threaded `slotsSize sl ≤ S`.  At that pin the ROOM
                  -- conjunct is `fLvlD`'s own `k`, so `frame-room` closes it
                  -- on the queue's LENGTH alone.
                  nst     = valsCaps→mList-strict c J sl (EvalSt.connectedShares st) q
                              (≤-trans (s≤s z≤n) 2≤S) slSz
                              (valsOf (frameStep J c) sl q vbq-c)
                  -- THE QUEUE'S READING, at the node the frame names.
                  -- `framePark?` on a `from-inner` IS `parkStrat?` of the
                  -- lookup, and `parkStrat?` on a mergeAll node IS the
                  -- queue's `valsStrat?` — so the leaf lands on `eqN` and
                  -- nothing else is owed
                  stq     = subst (λ z → parkStrat? (pathFloor path′) z ≡ true) eqN
                              (frame-parkStrat (frameStep J c)
                                 (from-inner op allNid inst) path′ sched st
                                 (proj₂ (proj₁ ok)) hps)
              -- hD reduces HERE and only here: the `with` above scrutinises
              -- `lookupNode allNid (nodes st)` and `w ≟ᵗ s`, so
              -- depthFrame → depthReact → depthFin → depthFinC has unfolded to
              -- `suc (depthDrain … q …) ≤ d`.  THE FRAME'S OWN ARC IS THE FUEL
              -- THE DRAIN RUNS ONE BELOW: `fuel-pred` hands the drain `pred d`
              -- and `frame-room` opens `fLvlD S W d J` at that same `pred d`,
              -- which is the only depth pairing the two sides can agree on —
              -- `fLvlD S W (suc d′) J` IS an `sIterD` at `d′`.  Relaxing the
              -- `suc` away instead (the earlier `n≤1+n`) left the drain at the
              -- frame's own fuel and made the room conjunct unprovable.
              in mergeAllDrain-nodry c sl Ψ (pred d) (sizeAt S (suc J)) (fLvlD S W d J)
                   2≤S 1≤R hCR slC slSz slFc J sf allNid path′ id now
                   lim (pred act) q sched st ok pb′ sspLen vbq rg gk
                   (fuel-pred hD) nst cl
                   (frame-room S W d (length q) J 2≤S (≤-trans (s≤s z≤n) hD)
                      (valsLen (frameStep J c) sl q vbq-c))
                   hps stq

------------------------------------------------------------------
-- thruOuter-nodry — thru-outer frame; uses thruWrap-pass + thruWalk-nodry.
thruOuter-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {u} (sf : Gas) (id : Id) (now : Tick)
  (op : AllOp) (nid : NodeId)
  (path′ : Path Γ u t) (vals : List (Val Γ (obs u)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (thru-outer op nid ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now (thru-outer op nid) path′ vals fin sched st ≤ d →
  pathStrat? path′ ≡ true →
  valsStrat? (pathFloor path′) vals ≡ true →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now (thru-outer op nid)
                               path′ vals fin sched st)))
    ≡ false

-- THE DEPTH FUEL SPLITS HERE, and only here.  `depthFrame`'s thru-outer
-- clause is `suc (depthWalk …)`: a frame is the one arc of the cycle that
-- RE-READS the budget, which is the same fact as `fLvlD S W (suc d) J`
-- unfolding to its payload walk at `d`.  So at zero the clause is
-- unreachable — a walk that subscribes cannot fit under no fuel at all —
-- and at suc the walk runs one level lower, at the REFRESHED budget.  This
-- is `stepThru-walk`'s (.Walk-Level) own shape; the two faces split their
-- fuel at the same place because it is the evaluator that decides where.
thruOuter-nodry c sl Ψ zero 2≤S 1≤R hCR slC slSz slFc J sf id now op nid path′ vals fin sched st ok pb vb rg gk cl ()
thruOuter-nodry c sl Ψ (suc d′) 2≤S 1≤R hCR slC slSz slFc J sf id now op nid path′ vals fin sched st ok pb vb rg gk cl hD hps hvs =
  let TW    = thruWalk sf op nid path′ id now vals sched st
      eq    = proj₁ (thruWrap-pass op nid fin TW)
      -- strip thru-outer frame from pb.  ∧-true's two Bool arguments are
      -- given EXPLICITLY: PbB reduces to a conjunction whose sides Agda
      -- cannot recover from the equation alone, so `∧-true _ _` leaves
      -- unsolved metas here.
      pb-sz   = proj₁ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′))
                              (pathBΨ? Ψ (thru-outer op nid ↠ path′)) pb)
      pb-bΨ   = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′))
                              (pathBΨ? Ψ (thru-outer op nid ↠ path′)) pb)
      -- frameBΨ? Ψ (thru-outer _ _) = true, so pb-bΨ is already
      -- pathBΨ? Ψ path′ ≡ true definitionally.
      pb′     = ∧-intro
                  (pathSz?-tail (Caps.cSize (frameStep J c)) (thru-outer op nid) path′ pb-sz)
                  pb-bΨ
      sspLen  = pathSz?-len (Caps.cSize (frameStep J c)) (thru-outer op nid ↠ path′) pb-sz
      S       = Caps.cSize c
      W       = Caps.cWid  c
      -- the value ledger's caps half, read once and spent twice below
      vb-c    = proj₁ (∧-true (valsCaps? (frameStep J c) sl vals) (valsΨ? Ψ vals) vb)
      -- THE WALK'S BUD IS THE FRAME'S REFRESH, and nothing here guesses it:
      -- `valsCaps→mList-strict` bounds every admitted payload's nesting by
      -- `sizeAt S (suc J)` at EVERY share ledger, out of the per-element size
      -- half and the threaded `slotsSize sl ≤ S`.  At that pin the ROOM
      -- conjunct is `fLvlD`'s own `k` — `suc (sizeAt S (suc J))` — so the fit
      -- is `≤-refl` in the k slot, and all that is left is the payload count
      -- against `suc (widAt S W J)` (the same `valsCaps?` receipt) and the
      -- index against `fLvl S W J` (inflationary).
      nst     = valsCaps→mList-strict c J sl (EvalSt.connectedShares st) vals
                  (≤-trans (s≤s z≤n) 2≤S) slSz (valsOf (frameStep J c) sl vals vb-c)
      room    = frame-room S W (suc d′) (length vals) J 2≤S (s≤s z≤n)
                  (valsLen (frameStep J c) sl vals vb-c)
  in subst (λ x → any dryEvent x ≡ false) (sym eq)
           (thruWalk-nodry c sl Ψ d′ (sizeAt S (suc J)) (fLvlD S W (suc d′) J)
              2≤S 1≤R hCR slC slSz slFc J sf op nid path′ id now vals sched st
              ok pb′ sspLen vb rg gk (≤-pred hD) nst cl room hps hvs)

-- take's dispatch: the non-cut arm emits nothing, the cutting arm
-- emits cutThrough's closes.  Unconditional — no gas, no caps, no level
takeDispatch-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  any dryEvent (proj₁ (proj₂ (takeDispatch {t = t} nid vals fin sched st ns)))
    ≡ false
takeDispatch-nodry nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = cutThrough-nodry nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                               (EvalSt.dying st) (EvalSt.registry st)
... | false = refl
takeDispatch-nodry nid vals fin sched st nothing                  = refl
takeDispatch-nodry nid vals fin sched st (just (scan-st _))       = refl
takeDispatch-nodry nid vals fin sched st (just (mergeAll-st _ _ _ _))    = refl
takeDispatch-nodry nid vals fin sched st (just (switch-st _ _))   = refl
takeDispatch-nodry nid vals fin sched st (just (exhaust-st _ _))  = refl

stepFrame-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (Ψ d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  slotsFnCap sl ≤ Ψ →
  ∀ (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (path′ : Path Γ u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  OKB {e = e} c sl Ψ J sched st →
  PbB c Ψ J (f ↠ path′) ≡ true →
  VbB c sl Ψ J vals ≡ true →
  regP? (PbB c Ψ J) (EvalSt.registry st) ≡ true →
  sf ≡ budgetAt e sl id →
  -- the fused per-frame ceiling, delivered by the walk's CL channel
  Caps.cSize (frameStep (fLvlD (Caps.cSize c) (Caps.cWid c) d J) c)
    ≤ sizeCapAt e sl (suc id) →
  depthFrame sf id now f path′ vals fin sched st ≤ d →
  -- THE ENTRY READING, FORWARDED AND NOT USED HERE.  Only the two *All
  -- edges consume it: they are the arms that subscribe, and a mint's side
  -- condition is stated against the payload's own path and reading.  Both
  -- reduce at a concrete frame — `frameStrat?` is `true` on every frame
  -- that dispatches, and `pathFloor` ignores the head — so a caller's
  -- `f ↠ path′` form and a callee's `path′` form are the same premise.
  pathStrat? (f ↠ path′) ≡ true →
  valsStrat? (pathFloor path′) vals ≡ true →
  any dryEvent
      (proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    ≡ false

-- MAP: the frame emits nothing at all
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (map-f fn) path′ vals fin sched st _ _ _ _ _ _ _ _ _ = refl

-- SCAN: every arm of the node-state dispatch emits `[]`
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J {u = u} sf id now
                (scan-f fn nid) path′ vals fin sched st _ _ _ _ _ _ _ _ _
  with lookupNode nid (EvalSt.nodes st)
... | nothing                  = refl
... | just (take-st _)         = refl
... | just (mergeAll-st _ _ _ _)      = refl
... | just (switch-st _ _)     = refl
... | just (exhaust-st _ _)    = refl
... | just (scan-st {w} acc) with w ≟ᵗ u
...   | yes refl = refl
...   | no  _    = refl

-- TAKE: the one severing frame, and it is free (cutThrough-nodry)
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (take-f nid) path′ vals fin sched st _ _ _ _ _ _ _ _ _ =
  takeDispatch-nodry nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

-- the two *All edges: real definitions, subscribeInner-nodry is APPLIED inside
stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (from-inner op allNid inst) path′ vals fin sched st
                ok pb vb rg gk cl hD hps hvs =
  innerReact-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now op allNid inst
                   path′ vals fin sched st ok pb vb rg gk cl hD hps hvs

stepFrame-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now
                (thru-outer op nid) path′ vals fin sched st
                ok pb vb rg gk cl hD hps hvs =
  thruOuter-nodry c sl Ψ d 2≤S 1≤R hCR slC slSz slFc J sf id now op nid
                  path′ vals fin sched st ok pb vb rg gk cl hD hps hvs
