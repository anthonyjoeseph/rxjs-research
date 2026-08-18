-- Verify-Budget-Sufficient.Caps-Face.Part4
-- DELIVERY CLIQUE SLOTS (HEAVY block) … obsList-nodeWid
-- (lines 3664–5199 of the original Caps-Face.agda)
module Verify-Budget-Sufficient.Caps-Face.Part4 where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _∸_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ⊔-mono-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-distribˡ-+; *-identityʳ; <⇒≤;
                                       ^-monoˡ-≤; ^-*-assoc;
                                       ^-distribˡ-+-*; *-mono-≤;
                                       +-monoʳ-≤; *-comm;
                                       m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ; *-identityˡ;
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; concat; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++; length-map)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted; delivery;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                subΘExp; subΘTm; subΘTms;
                                varIx;
                                renExp; renTm; renTms; Ren∈; ext∈; ++Ren;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms;
                                elimDExp; elimDTm; elimDTms;
                                compare∈; _⊟_; ⊟-++ˡ; ⊟-++ʳ; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Frame-Width using (pWᵉ; pWᵛ; dWᵉ; dWᵗ; dWᵗˢ; dWᵛ; outWᵛ;
                                outWᵉ; innWᵉ; innWᵗ; innWᵗˢ;
                                pmOᵉ; pmOᵗ; pmIᵉ; pmIᵗ; pmIᵗˢ;
                                _∈ᵇ_; outWⱽ; innWⱽ; innWᵗⱽ; innWᵗˢⱽ;
                                pmOⱽ; pmOᵗⱽ; pmIⱽ; pmIᵗⱽ; pmIᵗˢⱽ;
                                dWⱽ; dWᵗⱽ; dWᵗˢⱽ;
                                slotPW; slotsPW; slotsPWgo;
                                slotIW; slotsIW; slotsIWgo;
                                slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; setNode; lookupNode;
                                NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                takeVals; takeDispatch; cutThrough; pathHasNode;
                                dropSource; arrSource; chainsOf; chainsGo; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sizeAt;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                dryBurst;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize; fCharge; regAt;
                                sizeStep; iterSize; foldStep; iterFold;
                                fLvl; fLvlD; iterL; dLvl; lvls;
                                sIterD; sLvlD)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted 2026-08-01 so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Delivery-Walk public
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
open import Verify-Budget-Sufficient.Caps-Nest public
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFrame; depthReact; depthFin; depthWalk; depthCascade;
         depthConsume)
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers
open import Verify-Budget-Sufficient.Caps-Chain
  using (walk-nil; inner-nil; walk-index; frame-step; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd using (walk-step-suc)

open import Verify-Budget-Sufficient.Caps-Face.Part3 public

------------------------------------------------------------------
-- THE DELIVERY CLIQUE'S SLOTS COROLLARIES.
--
-- .Keeps-Ring covers the subscribe side.  foldPath / dispatchShare /
-- shareGo are the DELIVERY side, and the caps clauses below need
-- exactly their slotsEq: an in-flight bound established before a
-- sub-call is stated at the entry telescope, and the clause has to
-- report it after the sub-call has moved the Sched.
--
-- Only the slots half is proven.  The connected-shares half of KeepsC
-- is the wet ledger's business (sharedConnect-unconn); nothing on the
-- caps side reads it, and half a record is not worth carrying.
--
-- The recursion mirrors the evaluator's own, which is why it
-- terminates: foldPath descends the chain, hands off to dispatchShare
-- at a share sink, which spends one dispatch gas into shareGo, which
-- folds each admitted registration back through foldPath.  shareLatch,
-- shareAdmit and shareFinish move the registry, the live set and the
-- dying/completed ledgers and never the telescope, so they cost a refl.
------------------------------------------------------------------

foldPath-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≡ Sched.slots sched

dispatchShare-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
    ≡ Sched.slots sched

shareGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
    ≡ Sched.slots sched

foldPath-slots sf gas id now envSrc root vals evs fin sched st = refl
foldPath-slots sf gas id now envSrc (share-sink i) vals evs fin sched st =
  dispatchShare-slots sf gas id now i vals fin sched st
foldPath-slots sf gas id now envSrc (f ↠ p) vals evs fin sched st =
  trans (foldPath-slots sf gas id now envSrc p
           (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step)))
           (proj₁ (proj₂ (proj₂ (proj₂ step))))
           (proj₂ (proj₂ (proj₂ (proj₂ step)))))
        (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))
  where
  step = stepFrame sf id now f p vals fin sched st

dispatchShare-slots sf zero    id now i vals fin   sched st = refl
dispatchShare-slots sf (suc gas) id now i vals false sched st =
  shareGo-slots sf gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sched st
dispatchShare-slots sf (suc gas) id now i vals true  sched st =
  shareGo-slots sf gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st)

shareGo-slots sf gas id now i vals fin []              sched st = refl
shareGo-slots sf gas id now i vals fin ((rid , p) ∷ ps) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-slots sf gas id now i vals fin ps sched st
... | false =
  trans (shareGo-slots sf gas id now i vals fin ps
           (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)))
        (foldPath-slots sf gas id now (toℕ i) p vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  FP  = foldPath sf gas id now (toℕ i) p vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀

------------------------------------------------------------------
-- (b) THE CASCADE COMPANION, AND THE BUDGET CLAIM, AS AN ASSEMBLY.
--
-- This is the most refutation-scarred statement in the file: three
-- counts have failed it — `cWid * cReg` (tickFits-absurd), then
-- `cWid * cReg * cSize` (nested shares beat it exponentially), then
-- `2 ^ cReg * cSize`, whose middle step Mint-Loop-Probe measured false.
-- Each time the failure was at ROUTE level and each time it was found by
-- running something rather than by proving something.  So the conjunct is
-- not stated as one opaque claim here; it is DECOMPOSED first, with the
-- pieces postulated, so that the next failure lands on a named statement
-- instead of three clauses into a grind.
--
-- THE THREE PIECES.  Write `D` for the deliveries a cascade makes — one
-- per registration it folds into, which is exactly what its own ledger
-- counts, since every delivering clause of `cascadeGo` and `shareGo`
-- conses one `rid` onto `delivered`.  Then
--
--   (i)  cascadeGo-level       j ≤ lvls cSize cWid d 0 D
--   (ii) cascadeGo-deliveries  D ≤ cDel c d, the delivery RECURSION
--
-- and `cascadeGo-caps` below is (i) with (ii) widened into it by one
-- `lvls-mono` — the count `sizeCount` spends IS `lvls cSize cWid d 0
-- (cDel c d)`, so no arithmetic joins them.  (i) is the per-delivery
-- charge as the walk actually proves it: every fold is a frame on some
-- delivery's chain, a chain is shorter than cSize by pathSz?'s own
-- length conjunct, and each frame is charged at the level the one
-- before it LEFT.  Both are theorems; (ii) is where all the difficulty
-- was.
--
-- (ii) HAS NOW BEEN WRONG THREE TIMES, and the third correction is the
-- only one that was PREDICTED before it was measured.  The history:
--
--   · `2 ^ cReg` — refuted, because `shareAdmit` reads the registry as
--     of the dispatch, so the DAG the paths run through is the END
--     registry.  Mint-Loop-Probe's three-level lean ladder at k = 2
--     delivers 176 out of an entry registry of 7.
--   · `2 ^ cReg * 2 ^ cReg` — the pair story (pre-state registrations
--     visited × an index for the minted ones gone through).  Both
--     decompositions of the second coordinate were measured false
--     (fibreCap ≤ cSize: 4 against 3; fibreCap ≤ 2 ^ cReg: 576 against
--     512), so the conjunct was stated whole and gated on
--     Mint-Loop-Probe's rows and nothing else.
--   · AND THE WHOLE SQUARE IS FALSE.  Delivery-Law-Prediction.md
--     derived the delivery recurrence from the evaluator's structure
--     and committed the L = 5 rows BEFORE measuring them; every
--     checkable row then matched EXACTLY (3 D values, 2 increments, 3
--     fire vectors, 3 delivery splits, 6 generation counts, 3 cReg, 3
--     cSize, 2 mPre).  The law puts D(5,5) at 4514934 against
--     `4 ^ cReg = 4194304`.
--
-- AND THE 2-TOWER `2 ^ (2 ^ cReg)` IS GONE TOO, not because a row
-- breached it — none does — but because NOTHING CAN PROVE IT, and the
-- reason is arithmetic rather than route-finding.  Every route to a
-- bound reading cReg alone rests on the same two facts,
--
--     R ≤ cReg + Q · D          D ≤ (1 + R) ^ (1 + n)
--
-- i.e. `D ≤ (1 + cReg + Q · D) ^ (1 + n)`, whose right-hand side
-- outgrows its left at EVERY D.  The pair bounds nothing, and no
-- CLOSED F repairs it: F would have to satisfy
-- `F ≥ (1 + cReg + Q · F) ^ (1 + n)`, and no natural number does.  So
-- the delivery bound stops being a formula and becomes a RECURSION,
-- `cDel` (.Caps), read off the same two facts SEQUENTIALLY — the walk
-- is one chain at a time, and the registry a chain sees is the entry
-- registry plus the mints of the deliveries ALREADY MADE.  That is the
-- ordering fact the mint loop natively obeys, and recursion on
-- (dispatch gas, walk position) is well-founded exactly where the
-- closed form was circular.
--
-- THE PROOF ROUTE IS THE HOLE, and the one that was named here — the
-- generation-ancestry injection into subsets of the fire schedule — is
-- REFUTED, by rows that are now in the repo rather than by a failed
-- grind.  The amplifier family it was gated on has since been measured
-- (Mint-Loop-Shapes MEASUREMENT 9): a minting scan INSIDE a shared def
-- makes mints beget FIRES, and pB's slot 0 fires 3 / 7 / 11 / 12 times
-- where the pure share DAG dispatches it 2.  Fires are not
-- entry-computable, so they cannot carry the exponent, and the subset
-- half is dead for the reason MEASUREMENT 8(d) already gives for every
-- subset injection.  The full refutation, the closed delivery
-- recurrence that survives it, and the two closed forms that DO follow
-- from that recurrence (neither of which closes against a bound reading
-- cReg alone) are written at the postulate itself, below.
--
-- THE FEEDBACK LOOP BEHIND ALL OF THIS IS MEASURED AND DOES NOT TOWER
-- IN THE NESTING DEPTH.  Mint-Loop-Probe: deliveries SATURATE in k (5
-- flat at one shared level; 20, 26, 27, 27 at two; 50 … 269 at three)
-- because a minted registration is only reachable by dispatches that
-- come after it and how many remain is fixed by the PRE-STATE DAG.  j
-- saturates too, but LATER — 58, 226, 548, 912, 1164, 1268, 1291 —
-- because nesting keeps lengthening the chains after it has stopped
-- widening them.  The mid-cascade subscription that drives the loop is
-- real rxjs, not an evaluator artifact: a subscriber added mid-cascade
-- misses the in-flight emission and receives the cascade's later ones,
-- checked against rxjs 7.8 at the probe's head.
--
-- AND (i) WAS THE SUSPECT ONE, not (ii) — until it stopped being a
-- product.  `j ≤ D * cSize` charged cSize per delivery, but the receipt
-- scanFrame-caps actually pays is `suc (length vals * suc (sizeᵗ fn))`
-- — one fold per node of the step function PER PAYLOAD — and
-- `length vals` is a BURST WIDTH, which nothing entry-readable bounds
-- (Charge-Probe: progW breaches at 47 against 40).  Widening the
-- product to `D * cSize * suc (suc cWid * suc cSize)` fitted every
-- measured row but had no ROUTE: the walk proves an iteration, each
-- frame charged where it runs, and a product charges them all at the
-- cascade's entry — the entry-charging error Entry-Caps-Refuted kills
-- one stratum down.  So the count became the iteration itself
-- (`sizeCount`, .Caps) and (i) is `cascadeGo-level`, a theorem.  The
-- width factor is paid inside `fCharge`, at the level the frame runs
-- at, which is where Width-Count-Probe's objection to reading cWid
-- stops applying: the height is a recurrence, not a closed form.
--
-- caps-tick is then a COROLLARY rather than a sibling face: widen the
-- reported level to the endpoint by frameStep-mono-j, and the endpoint
-- IS capsAt (suc id) by capsAt-suc-full
------------------------------------------------------------------

------------------------------------------------------------------
-- WHAT THE WALK READS OFF THE CAPS: three tiny lemmas and one new
-- ledger, all of them plumbing for the instantiation below.
--
-- `valsCaps?` is `valCaps?` lifted to a burst: every payload under the
-- caps, AND the burst no wider than the width cap.  The width conjunct
-- is not decoration — it is the one thing that makes a per-frame mint
-- budget finite at all, because a `thru-outer` frame subscribes once
-- per payload (thruWalk) and so mints in proportion to its burst
-- width.  Without it the frame budget is false rather than unproven,
-- for any fixed budget whatsoever.  It is the same width factor
-- `fCharge` pays per frame, read in the same place: at the level the
-- frame RUNS at, `widAt S W J` being `cWid (frameStep J c)` by refl.
------------------------------------------------------------------

valsCaps? : ∀ {n} {Γ : Ctx n} {s} → Caps → Slots Γ → List (Val Γ s) → Bool
valsCaps? {s = s} c sl vs =
  all (valCaps? c sl s) vs ∧ (length vs ≤ᵇ suc (Caps.cWid c))

------------------------------------------------------------------
-- THE NESTING HYPOTHESIS, AS THE CLIQUE CARRIES IT.
--
-- A frame installs its own budget — that is what the refresh means, and
-- `fLvlD`'s `suc d` clause is where it is read — so the number every
-- head under one frame descends on is this one, named once:
------------------------------------------------------------------

frameBud : Caps → ℕ → ℕ
frameBud c j = suc (sizeAt (Caps.cSize c) (suc j))

-- ONE payload, and one LIST of them.  `Val Γ (obs u)` is `Closed Γ u`
-- definitionally, so a single predicate serves both the payload walk and
-- the concat queue
mOK? : ∀ {n} {Γ : Ctx n} {s} → ℕ → Slots Γ → List Source → Closed Γ s → Bool
mOK? bud sl cs o = nest o sl cs ≤ᵇ bud

mList? : ∀ {n} {Γ : Ctx n} {s} →
  ℕ → Slots Γ → List Source → List (Closed Γ s) → Bool
mList? bud sl cs os = all (mOK? bud sl cs) os

-- DERIVED, NOT PREMISED: a payload admitted at a frame's own level has
-- its nesting under the budget that frame installs, because `valCaps?`
-- bounds `sizeᵛ (obs u) o` — which IS `sizeᵉ o` — by
-- `Caps.cSize (frameStep j c)`, which IS `sizeAt S j`, and that is
-- exactly the left summand `refresh-supplies-nest` consumes.  The right
-- summand is the `slotsSize sl ≤ Caps.cSize c` every head already carries
valCaps→nest : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Val Γ (obs u)) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  nest o sl cs ≤ frameBud c j
valCaps→nest {u = u} c j sl cs o 1≤S hsl hv =
  refresh-supplies-nest (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (valCaps?-size (frameStep j c) sl (obs u) o hv)))
    hsl

obsCaps→nest : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Closed Γ s) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  obsCaps? (frameStep j c) sl o ≡ true →
  nest o sl cs ≤ frameBud c j
obsCaps→nest {n = n} c j sl cs o 1≤S hsl ho =
  refresh-supplies-nest (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (proj₁ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize (frameStep j c)) _ ho))))
    hsl

-- the same, over a whole payload list / queue
valsCaps→mList : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (vs : List (Val Γ (obs u))) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  all (valCaps? (frameStep j c) sl (obs u)) vs ≡ true →
  mList? (frameBud c j) sl cs vs ≡ true
valsCaps→mList c j sl cs []       1≤S hsl h = refl
valsCaps→mList {u = u} c j sl cs (o ∷ vs) 1≤S hsl h
  with ∧-true (valCaps? (frameStep j c) sl (obs u) o)
              (all (valCaps? (frameStep j c) sl (obs u)) vs) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs ≤ᵇ frameBud c j)
            (≤⇒≤ᵇ (valCaps→nest c j sl cs o 1≤S hsl h₁)))
          (valsCaps→mList c j sl cs vs 1≤S hsl h₂)

obsList→mList : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (q : List (Closed Γ s)) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  all (obsCaps? (frameStep j c) sl) q ≡ true →
  mList? (frameBud c j) sl cs q ≡ true
obsList→mList c j sl cs []      1≤S hsl h = refl
obsList→mList c j sl cs (o ∷ q) 1≤S hsl h
  with ∧-true (obsCaps? (frameStep j c) sl o)
              (all (obsCaps? (frameStep j c) sl) q) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs ≤ᵇ frameBud c j)
            (≤⇒≤ᵇ (obsCaps→nest c j sl cs o 1≤S hsl h₁)))
          (obsList→mList c j sl cs q 1≤S hsl h₂)

-- THE STRICT ROW, and it is the whole content of the refresh.  A payload
-- subscribe IS a nesting level and spends one, so the walk is handed the
-- PREDECESSOR of the budget it reports at — `frameBud c j` is
-- `suc (sizeAt (cSize c) (suc j))` by plain definition, so that
-- predecessor is `sizeAt (cSize c) (suc j)` and the two meet by refl
-- wherever the walk's conjunct is consumed.  `refresh-supplies-nest
-- -strict` is what makes the row land there rather than one above
valCaps→nest-strict : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Val Γ (obs u)) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  nest o sl cs ≤ sizeAt (Caps.cSize c) (suc j)
valCaps→nest-strict {u = u} c j sl cs o 1≤S hsl hv =
  refresh-supplies-nest-strict (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (valCaps?-size (frameStep j c) sl (obs u) o hv)))
    hsl

valsCaps→mList-strict : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (vs : List (Val Γ (obs u))) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  all (valCaps? (frameStep j c) sl (obs u)) vs ≡ true →
  mList? (sizeAt (Caps.cSize c) (suc j)) sl cs vs ≡ true
valsCaps→mList-strict c j sl cs []       1≤S hsl h = refl
valsCaps→mList-strict {u = u} c j sl cs (o ∷ vs) 1≤S hsl h
  with ∧-true (valCaps? (frameStep j c) sl (obs u) o)
              (all (valCaps? (frameStep j c) sl (obs u)) vs) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs ≤ᵇ sizeAt (Caps.cSize c) (suc j))
            (≤⇒≤ᵇ (valCaps→nest-strict c j sl cs o 1≤S hsl h₁)))
          (valsCaps→mList-strict c j sl cs vs 1≤S hsl h₂)

-- and THE SAME ROW OVER A PARKED QUEUE, for the concat FINISH.  A drain
-- is a walk exactly as a thru-outer's payload sweep is, so it too is
-- handed the predecessor of the budget it reports at, and its queue's
-- bound has to land there rather than one above
obsCaps→nest-strict : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (o : Closed Γ s) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  obsCaps? (frameStep j c) sl o ≡ true →
  nest o sl cs ≤ sizeAt (Caps.cSize c) (suc j)
obsCaps→nest-strict {n = n} c j sl cs o 1≤S hsl ho =
  refresh-supplies-nest-strict (Caps.cSize c) j o sl cs 1≤S
    (≤ᵇ⇒≤ (sizeᵉ o) (sizeAt (Caps.cSize c) j)
          (T-to (proj₁ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize (frameStep j c)) _ ho))))
    hsl

obsList→mList-strict : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (cs : List Source) (q : List (Closed Γ s)) →
  1 ≤ Caps.cSize c →
  slotsSize sl ≤ Caps.cSize c →
  all (obsCaps? (frameStep j c) sl) q ≡ true →
  mList? (sizeAt (Caps.cSize c) (suc j)) sl cs q ≡ true
obsList→mList-strict c j sl cs []      1≤S hsl h = refl
obsList→mList-strict c j sl cs (o ∷ q) 1≤S hsl h
  with ∧-true (obsCaps? (frameStep j c) sl o)
              (all (obsCaps? (frameStep j c) sl) q) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs ≤ᵇ sizeAt (Caps.cSize c) (suc j))
            (≤⇒≤ᵇ (obsCaps→nest-strict c j sl cs o 1≤S hsl h₁)))
          (obsList→mList-strict c j sl cs q 1≤S hsl h₂)

-- AND CARRIED, not re-derived: the walk widens its tail's caps receipt,
-- so re-deriving per payload would hand each one a LARGER budget while
-- the walk transformer has exactly one.  The bound at a fixed budget
-- travels untouched; the only thing that drifts under it is the
-- connected set, and it drifts the harmless way
mList?-cons : ∀ {n} {Γ : Ctx n} {s} (bud : ℕ) (sl : Slots Γ) (cs : List Source)
  (src : Source) (os : List (Closed Γ s)) →
  mList? bud sl cs os ≡ true → mList? bud sl (src ∷ cs) os ≡ true
mList?-cons bud sl cs src []       h = refl
mList?-cons bud sl cs src (o ∷ os) h
  with ∧-true (mOK? bud sl cs o) (mList? bud sl cs os) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl (src ∷ cs) ≤ᵇ bud)
            (≤⇒≤ᵇ (nest-cons o sl cs src bud (≤ᵇ⇒≤ (nest o sl cs) bud (T-to h₁)))))
          (mList?-cons bud sl cs src os h₂)

-- one head off the front, which is what a walk hands its own recursion
mList?-tail : ∀ {n} {Γ : Ctx n} {s} (bud : ℕ) (sl : Slots Γ) (cs : List Source)
  (o : Closed Γ s) (os : List (Closed Γ s)) →
  mList? bud sl cs (o ∷ os) ≡ true → mList? bud sl cs os ≡ true
mList?-tail bud sl cs o os h = proj₂ (∧-true (mOK? bud sl cs o) (mList? bud sl cs os) h)

mList?-head : ∀ {n} {Γ : Ctx n} {s} (bud : ℕ) (sl : Slots Γ) (cs : List Source)
  (o : Closed Γ s) (os : List (Closed Γ s)) →
  mList? bud sl cs (o ∷ os) ≡ true → nest o sl cs ≤ bud
mList?-head bud sl cs o os h =
  ≤ᵇ⇒≤ (nest o sl cs) bud
    (T-to (proj₁ (∧-true (mOK? bud sl cs o) (mList? bud sl cs os) h)))

-- a bigger budget still covers it, which is how a frame's own bound
-- reaches a callee that was handed a larger one
mList?-widen : ∀ {n} {Γ : Ctx n} {s} {bud bud′ : ℕ} (sl : Slots Γ)
  (cs : List Source) (os : List (Closed Γ s)) → bud ≤ bud′ →
  mList? bud sl cs os ≡ true → mList? bud′ sl cs os ≡ true
mList?-widen sl cs []       le h = refl
mList?-widen {bud = bud} {bud′ = bud′} sl cs (o ∷ os) le h
  with ∧-true (mOK? bud sl cs o) (mList? bud sl cs os) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs ≤ᵇ bud′)
            (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (nest o sl cs) bud (T-to h₁)) le)))
          (mList?-widen sl cs os le h₂)

-- and it survives a whole evaluator step, on the same KeepsC hypothesis
-- the single-payload version spends
mList?-keeps : ∀ {n} {Γ : Ctx n} {s} (bud : ℕ) (sl : Slots Γ)
  (cs cs′ : List Source) (os : List (Closed Γ s)) →
  (∀ src → memberSource src cs ≡ true → memberSource src cs′ ≡ true) →
  mList? bud sl cs os ≡ true → mList? bud sl cs′ os ≡ true
mList?-keeps bud sl cs cs′ []       mono h = refl
mList?-keeps bud sl cs cs′ (o ∷ os) mono h
  with ∧-true (mOK? bud sl cs o) (mList? bud sl cs os) h
... | h₁ , h₂ =
  ∧-intro (T⇒≡true (nest o sl cs′ ≤ᵇ bud)
            (≤⇒≤ᵇ (nest-keeps o sl cs cs′ bud mono
                     (≤ᵇ⇒≤ (nest o sl cs) bud (T-to h₁)))))
          (mList?-keeps bud sl cs cs′ os mono h₂)

-- pathSz?'s length conjunct, read back out: the OUTERMOST one bounds
-- the whole chain, and root / share-sink have no length at all
pathSz?-len : ∀ {n} {Γ : Ctx n} {u t} (B : ℕ) (p : Path Γ u t) →
  pathSz? B p ≡ true → pathLen p ≤ B
pathSz?-len B root           h = z≤n
pathSz?-len B (share-sink i) h = z≤n
pathSz?-len B (f ↠ p)        h =
  ≤ᵇ⇒≤ (suc (pathLen p)) B
    (T-to (proj₁ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                   (proj₂ (∧-true (frameSz? B f)
                                  ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h)))))

pathSz?-tail : ∀ {n} {Γ : Ctx n} {s u t} (B : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t) →
  pathSz? B (f ↠ p) ≡ true → pathSz? B p ≡ true
pathSz?-tail B f p h =
  proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
          (proj₂ (∧-true (frameSz? B f)
                         ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h)))

-- (i) IS NO LONGER A POSTULATE, AND IT IS NOT A PRODUCT EITHER.  The
-- per-delivery charge used to be stated as
-- `j ≤ D * cSize * suc (suc cWid * suc cSize)` — a whole cascade's
-- frames charged at the level the CASCADE entered at — and the walk
-- proves something of a different shape: `cascadeGo-level` (below) says
-- one cascade LANDS at `lvls cSize cWid 0 D`, which iterates `dLvl` once
-- per delivery and `fLvl` once per frame, each read at the level the one
-- before it LEFT.  Entry-charging is machine-refuted one stratum down
-- (Entry-Caps-Refuted), so the iteration is the honest currency and the
-- product had no route through this walk.  `sizeCount` (.Caps) is
-- therefore the LANDING LEVEL — it dominates the product it replaces
-- (a linearity step at J = 0, measured by a probe module since DELETED), so no measured
-- row moves — and this conjunct is `cascadeGo-level` composed with
-- `cascadeGo-deliveries`, at the end of the section below.

-- (ii) THE DELIVERY BOUND, WHOLE, AND AS A RECURSION.  One cascade's
-- deliveries against `cDel c = dCapᶜ cSize cWid cReg (suc cSize) 0` —
-- the gas-indexed walk of .Caps, not a closed form.  Both closed
-- forms it replaces are dead: the squared-subset `4 ^ cReg` is FALSE
-- (the delivery law, committed before the L = 5 rows were measured
-- and then matching every checkable one exactly, puts D(5,5) at
-- 4514934 against 4 ^ 11 = 4194304), and the 2-tower
-- `2 ^ (2 ^ cReg)` that replaced it is UNPROVABLE — see the
-- self-reference above, which is a property of the two facts and not
-- of any route through them.
--
-- THE ROUTE THAT WAS NAMED HERE IS REFUTED BY ROWS ALREADY IN THE
-- REPO, and it is refuted before any clause of it was ground.  It
-- read: a minted registration's mint-edge ancestry is a SUBSET of the
-- fire schedule (generation g ↦ g-subsets, which is what the binomial
-- counts are), and the fires are bounded by the PRE-STATE DAG.  Both
-- halves fail:
--
--   · THE SUBSET HALF.  Mint-Loop-Shapes' MEASUREMENT 8(d) ruling —
--     "every subset-injection route is dead for the delivery bound,
--     whether or not the bound is true" — applies to this injection
--     too, since it is one.  The surviving inverted-pair leg proves
--     `D ≤ 2 ^ R_end`, and R_end is 261 against an entry cReg of 7
--     (254 mints on a 269-delivery cascade), so it proves 2 ^ 261
--     against a demand of 2 ^ 128.
--   · THE FIRES HALF.  "Fires are bounded by the pre-state DAG" was
--     the lean ladders' property, and MEASUREMENT 9 — the amplifier
--     family, `pB` / `insB`, a minting scan INSIDE a shared def — is
--     the family where it stops holding.  pB's slot 0 fires 3 times
--     at cascade 0 and 7, 11, 12 times at cascade 1 for k = 0, 1, 2,
--     where the share DAG alone dispatches it 2 times.  Mints beget
--     fires; the fire count is not entry-computable, so it cannot
--     carry the exponent.
--
-- WHAT IS ESTABLISHED, AND IS ROUTE-INDEPENDENT: the delivery ledger
-- obeys a CLOSED RECURSION with exactly one unbounded input.
-- `EvalSt.delivered` is consed at exactly two sites in the evaluator
-- — shareGo's uncancelled clause and cascadeGo's — and dispatchShare
-- is called from exactly one, foldPath's `share-sink` clause.  So,
-- writing Dfp for one foldPath's deliveries at dispatch gas g,
--
--     D(cascadeGo)     = Σ over uncancelled chains of (1 + Dfp n)
--     Dfp g root       = 0
--     Dfp g (f ↠ p)    = Dfp g p            -- stepFrame delivers nothing
--     Dfp g (sink i)   = Dds g
--     Dds 0            = 0
--     Dds (suc g)      = Σ over shareAdmit i (registry AS OF NOW)
--                          of (1 + Dfp g)
--
-- THAT RECURSION IS NO LONGER A READING OF THE SOURCE: it is proven,
-- line for line, in .Deliveries § D — foldPath-root-N / foldPath-frame-N
-- / foldPath-sink-N / dispatchShare-zero-N / dispatchShare-suc-N /
-- shareGo-skip-N / shareGo-cons-N / cascadeGo-skip-N /
-- cascadeGo-cons-N, over the ledger order `_⊑ᵈ_` and its composition
-- laws (delivN-split, delivN-cons).  The `↠` line is an equality and
-- not an inequality because the WHOLE stepFrame clique preserves
-- `EvalSt.delivered` (.Deliveries § B, fifteen mutually recursive
-- functions, no postulate); Mint-Loop-Frames' refl pins of `mJdel`
-- against `mFolds` at 5, 20 and 50 were the measured evidence for that
-- and are now a redundant cross-check.  Two closed forms follow, and
-- NEITHER closes against a bound that reads cReg alone:
--
--   (α) the depth form.  The share telescope orders the shares along
--       any fire path strictly, and dispatch gas caps the depth at n,
--       so D ≤ cReg * (1 + Rmax) ^ n with Rmax the registry length at
--       its peak.  Needs n * log Rmax ≤ 2 ^ cReg.
--   (β) the subset form.  D ≤ 2 ^ Rmax.  Needs Rmax ≤ 2 ^ cReg, which
--       is the 261-against-128 row above.
--
-- and Rmax ≤ cReg + (mints), mints ≈ D, so (α) READ AS A CLOSED FORM
-- is the self-referential `D ≤ cReg * (1 + cReg + Q · D) ^ n` and
-- bounds nothing — for any Q, any n, and any bound in its place.
--
-- AND THAT IS WHY THE STATEMENT ITSELF MOVED.  The damper is the
-- ORDERING fact Mint-Loop-Shapes names — a minted registration is
-- reachable only by dispatches that come AFTER it — so the bound is
-- written as the walk that fact describes rather than as a number the
-- walk is compared against.  `cDel c` is (α) done SEQUENTIALLY: the
-- top walk is as long as the registry, each subtree runs at one
-- dispatch gas less, and what a later chain sees is what the deliveries
-- ALREADY MADE left behind — carried as the caps LEVEL, so the registry
-- is `regAt S R J` and the per-frame receipt is `fCharge S W J`, both
-- read where the walk has climbed to.  The proof is then a
-- schedule-indexed induction on the same two indices the definition
-- recurses on, with .Deliveries' § D equations supplying the delivery
-- counting.
--
-- THE ROWS ALL FIT WITH ENORMOUS MARGIN, which is the least
-- interesting thing about it: `cDel` at pL⁴'s entry caps
-- (cReg 9, cSize 3, gas 6) already exceeds every D in the repo, and
-- the deepest lean rung is D = 41510 at cReg = 11.  The margin was
-- never the problem; the self-reference was
--
-- AND THE WALK IS NOW PROVEN — the whole of it except ONE FRAME.
-- .Delivery-Walk maps the clique onto the recursion, with no postulate
-- of its own:
--
--   foldPath      ↦ dCapᶜ  S W R gas J   (the gas IS the dispatch gas)
--   dispatchShare ↦ dCapᶜ  S W R gas J
--   shareGo       ↦ dWalkᶜ S W R gas J (length ps)
--   cascadeGo     ↦ dWalkᶜ S W R n   J (length chains)
--
-- over .Deliveries' § D equations, `dWalkᶜ-front` (the walk decomposes
-- from the FRONT exactly as it does from the back — an equality, so
-- the change of direction the head-first evaluator forces costs
-- nothing), and one frame's face at the level it runs at.  Started at
-- level 0 — `frameStep 0 c ≡ c` — it gives exactly this conjunct, since
-- `n ≤ cSize` (the hypothesis above) lifts the evaluator's dispatch gas
-- to cDel's index and `length chains ≤ cReg` is `regAt S R 0`.
--
-- AND THE ONE FACT IT IS STILL RELATIVE TO IS A PER-FRAME FACE — at a
-- level the frame can honestly be charged at.  That fact is
-- `stepFrame-face` (below), and this conjunct is now a THEOREM off it:
-- see the instantiation at the end of the share-bookkeeping section.
--
-- CHARGING THAT FACE AT THE ENTRY CAPS IS REFUTED (2026-08-02).  Two
-- axioms — `stepFrame-entry-caps` and `stepFrame-entry-mint` — briefly
-- stood here and made this conjunct a theorem; both asserted SAME-LEVEL
-- preservation (post-state and output burst back under the entry `c`
-- the frame started from), and the entry-caps refutation
-- (make entry-caps-refuted, seconds) is a machine-checked
-- `Entry-Caps → ⊥`.  It falls on the cheapest frame there is, a
-- `map-f`, which touches no state at all: a map frame's output is
-- `map (applyFn fn) vals` and `applyFn` GROWS a value — `pairᵗ x x`
-- has size 3 and takes a payload of size 3 to one of size 7 — so at
-- `c = caps 3 1 1` every hypothesis holds by `refl` and the conclusion
-- computes to `false`.  That is `frameStep`'s own header ("same-level
-- preservation is false, so the face must report growth"),
-- `caps-frame-boundary-absurd`, and the cascade fold-threading
-- note, all saying one thing: a frame may not be charged at the level
-- it started from.
--
-- SO THE WALK CARRIES THE LEVEL.  `cDel c` is `dCapᶜ` at level 0 (.Caps):
-- a frame costs the receipt read at the level it RUNS at, a delivery
-- ITERATES that over its chain, and the registry a dispatch fans out
-- over is `capsOK?`'s own fifth conjunct read at the level.  The
-- delivery bound then follows from ONE per-frame face in the shape the
-- ground `stepFrame-caps` already reports in



------------------------------------------------------------------
-- THE SUBSCRIBE-SIDE COMPANION TREE, transcribed from subscribeE-walkS's
-- clique one for one.  That walk already solved the structural problem —
-- which companions exist, what each threads, how their results compose —
-- so the caps induction inherits the same tree with (INV?, E′-receipt)
-- swapped for (capsOK?, j-receipt): the pre-state and every input bound
-- read at `frameStep j c`, the post-state and every output bound at
-- `frameStep (j + j′) c`, composed ADDITIVELY by +-assoc where the wet
-- side composes by ≤-trans, and widened by capsOK?-mono ∘ frameStep-mono-j
-- wherever two sub-results meet at different levels.
--
-- Stated all at once, before any clause is ground, so that a change to
-- the shape changes it HERE — cheaply — rather than invalidating a pile
-- of finished clause proofs.
------------------------------------------------------------------

slotsCaps?-capsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  slotsCaps? (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) sl ≡ true
slotsCaps?-capsAt {n = n} e sl id =
  slotsCaps?-bound (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) sl
    (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id))
    (≤-trans (≤-trans (slotsPW≤entryCeil n sl e) (n≤1+n _))
             (capsAt-base-wid e sl id))
    (≤-trans (≤-trans (slotsIW≤entryCeil n sl e) (n≤1+n _))
             (capsAt-base-wid e sl id))

------------------------------------------------------------------
-- caps-tick, DERIVED.  This is the joint the whole round was about, and
-- it is now three lines of assembly over the companions rather than a
-- face of its own: latch, fold the snapshot chains (which reports a j
-- and, crucially, that the j FITS), widen that level to the endpoint,
-- and the endpoint is capsAt (suc id) by definition.
--
-- The arrival's own bounds are a hypothesis rather than a derivation:
-- `a` is handed in by the scheduler, and the per-instant induction that
-- consumes this reads it off sched-next's live source, which capsOK?'s
-- widLive/stBounded? conjuncts already bound
------------------------------------------------------------------

-- the two conjuncts caps-tick reads back out of capsOK?, extracted with
-- their result types pinned so ∧-true's booleans are determined
capsOK?-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
    (stBounded? (Caps.cSize c) sched st ≡ true)
  × (regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true)
  × (all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched) ≡ true)
  × (all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
         (EvalSt.nodes st) ≡ true)
  × ((length (EvalSt.registry st) ≤ᵇ Caps.cReg c) ≡ true)
capsOK?-parts c sched st h with ∧-true _ _ h
... | h0 , r1 with ∧-true _ _ r1
... | h1 , r2 with ∧-true _ _ r2
... | h2 , r3 with ∧-true _ _ r3
... | h3 , h4 = h0 , h1 , h2 , h3 , h4

capsOK?-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true
capsOK?-regs c sched st h = proj₁ (proj₂ (capsOK?-parts c sched st h))

capsOK?-count : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → length (EvalSt.registry st) ≤ Caps.cReg c
capsOK?-count c sched st h =
  ≤ᵇ⇒≤ (length (EvalSt.registry st)) (Caps.cReg c)
       (T-to (proj₂ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st h))))))

------------------------------------------------------------------
-- THE SHARE BOOKKEEPING, caps side — three leaves the dispatch clause
-- consumes and nothing else does.  Two are refl-level (capsOK? reads
-- Sched.live, Sched.slots, EvalSt.nodes and EvalSt.registry, and
-- neither the latch nor the delivered ledger touches any of them);
-- shareFinish is the one with content, because it drops a source's
-- registrations and sweeps its live entry, and both have to be shown
-- to only SHRINK what capsOK? bounds.
------------------------------------------------------------------

-- latching a completing share records it in completedSources/dying,
-- which capsOK? does not read
shareLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → capsOK? c sched (shareLatch i fin st) ≡ true
shareLatch-caps c i false sched st h = h
shareLatch-caps c i true  sched st h = h

-- and marking a registration delivered is the same kind of nothing
capsOK?-delivered : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true
capsOK?-delivered c rid sched st h = h

-- THE FINISH FILTER, shared by the share's and the cascade's.  Both
-- ends of a completing source do the same two things — drop its
-- registrations, sweep its live entry — and every one of capsOK?'s five
-- conjuncts survives by the two generic filter lemmas: the registry
-- shrinks (regsSz? by dropSource-all, the count by dropSource-len), the
-- live list shrinks (stBounded?'s live half and widLive by
-- sweepLive-all), the nodes and the slots are untouched
dropSweep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { live = sweepLive (dropSource src (EvalSt.registry st))
                                             (Sched.live sched) })
            (record st { registry = dropSource src (EvalSt.registry st) }) ≡ true
dropSweep-caps c src sched st inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ (∧-true _ _ h0)))
                     (proj₂ (∧-true _ _ h0)))
    (∧-intro (dropSource-all (λ en → pathSz? (Caps.cSize c)
                                       (proj₂ (proj₂ (proj₂ en))))
                src (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = dropSource src (EvalSt.registry st)
  P    = capsOK?-parts c sched st inv
  h0   = proj₁ P
  h1   = proj₁ (proj₂ P)
  h2   = proj₁ (proj₂ (proj₂ P))
  h3   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4   = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- the admitted snapshot is a SUBLIST of the registry — its own filter
-- rather than dropSource's, because it also has to match the chain's
-- element type against the share's — so its chains inherit the
-- registry's size bound
shareAdmit-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (i : Fin n)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  all (λ rp → pathSz? B (proj₂ rp)) (shareAdmit i rs) ≡ true
shareAdmit-caps B i [] h = refl
shareAdmit-caps {Γ = Γ} B i ((rid , s , (u , p)) ∷ r) h
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-caps B i r (proj₂ (∧-true _ _ h))
... | true  | no  _    = shareAdmit-caps B i r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (shareAdmit-caps B i r (proj₂ (∧-true _ _ h)))

-- finishing a completing share drops the source's registrations and
-- sweeps its live entry.  Both are the generic filters, so all five of
-- capsOK?'s conjuncts survive by the same two lemmas: the registry
-- shrinks (regsSz? by dropSource-all, the count by dropSource-len) and
-- the live list shrinks (stBounded?'s live half and widLive by
-- sweepLive-all).  The nodes and the burst are untouched
shareFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (i : Fin n) (fin : Bool) (sl : Slots Γ)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  capsOK? c (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) ≡ true →
  burstCaps? c sl (proj₁ out) ≡ true →
  let r = shareFinish i fin out
  in (capsOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? c sl (proj₁ r) ≡ true)
shareFinish-caps c i false sl out inv bc = inv , bc
shareFinish-caps c i true sl (emits , sched′ , st′) inv bc =
  dropSweep-caps c (toℕ i) sched′ st′ inv , bc

------------------------------------------------------------------
-- THE DELIVERY BOUND, GROUND — on ONE per-frame face, at the level the
-- frame RUNS at.
--
-- .Delivery-Walk proves the whole mapping of the delivery clique onto
-- `dCapᶜ` / `dWalkᶜ` relative to `Walk-Hyps`; this is that record,
-- instantiated, plus three lines of arithmetic.
--
--   OK J = the slot telescope is fixed, and capsOK? at `frameStep J c`
--   Pb J = pathSz? (cSize (frameStep J c)) — whose registry ledger IS
--          capsOK?'s regsSz? conjunct, so the walk's ledger costs the
--          caller nothing, and whose length conjunct (pathSz?-len) is
--          the chain cap the delivery charge iterates over
--   Vb J = valsCaps? (frameStep J c) sl, the burst ledger
--   S, W, R = the entry caps' three fields, and every reading the walk
--          makes of them — sizeAt / widAt / regAt / fCharge — is
--          `frameStep J c`'s own field, by refl
--
-- The closure facts are the share bookkeeping just above; the two
-- widenings are pathSz?-widen and valsCaps?-widen along ⊑ᶜ, at
-- frameStep-mono-j; the registry reading is capsOK?-count.  What is left
-- is ONE frame, and it is the postulate below.
------------------------------------------------------------------

-- the OK predicate the walk threads: capsOK? at the CURRENT level, plus
-- the slot telescope the burst ledger is written against
walkOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) → ℕ → Sched Γ → EvalSt e → Set
walkOK c sl J sched st =
  (Sched.slots sched ≡ sl) × (capsOK? (frameStep J c) sched st ≡ true)

-- the one closure fact with content: the finish drops a source's
-- registrations and sweeps its live entry, and neither touches slots
walkOK-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (J : ℕ) (i : Fin n) (fin : Bool)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  walkOK c sl J (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) →
  walkOK c sl J (proj₁ (proj₂ (shareFinish i fin out)))
                (proj₂ (proj₂ (shareFinish i fin out)))
walkOK-finish c sl J i false out                    h = h
walkOK-finish c sl J i true  (emits , sched′ , st′) h =
  proj₁ h , dropSweep-caps (frameStep J c) (toℕ i) sched′ st′ (proj₂ h)

-- the burst ledger widens with the level: the payloads by
-- valsCaps?-widen, the width conjunct because cWid grows
valsCaps?-lvl : ∀ {n} {Γ : Ctx n} {s} (c c′ : Caps) (sl : Slots Γ)
  (vs : List (Val Γ s)) → c ⊑ᶜ c′ →
  valsCaps? c sl vs ≡ true → valsCaps? c′ sl vs ≡ true
valsCaps?-lvl {s = s} c c′ sl vs le h =
  ∧-intro (valsCaps?-widen sl s vs le
             (proj₁ (∧-true (all (valCaps? c sl s) vs)
                            (length vs ≤ᵇ suc (Caps.cWid c)) h)))
          (≤ᵇ-widen (length vs) (s≤s (proj₁ (proj₂ le)))
             (proj₂ (∧-true (all (valCaps? c sl s) vs)
                            (length vs ≤ᵇ suc (Caps.cWid c)) h)))

------------------------------------------------------------------
-- THE FRAME FACE, SPLIT (2026-08-02) — FORWARD-DECLARED HERE, GROUND
-- AT THE END OF THE FILE ON FIVE CLAUSE PIECES, THREE OF THEM PROVEN.
--
-- WHAT IT IS, against the ground companion.  `stepFrame-caps` (end of
-- file, ground, five clauses over the whole frame clique) reports the
-- post-state at `capsOK? (frameStep (j + j′) c)` and the output values
-- at `all (valCaps? (frameStep (j + j′) c) sl u)`.  The face adds the
-- two conjuncts the LEVEL WALK reads and the companion does not report:
--
--   (a) THE RECEIPT BOUND, AND IT IS NOW STATED IN THE LANDING FORM
--       (2026-08-03): `j + j′ ≤ fLvlD (cSize c) (cWid c) d j`, the level
--       the frame LEAVES, rather than `j′ ≤ fCharge (cSize c) (cWid c) j`,
--       one frame's receipt.  The face gains the depth fuel `d` for it.
--       Every GROUND clause below still pays `fCharge` — `fLvl S W j` IS
--       `j + fCharge S W j` by refl, so `face-lift` (below the face)
--       carries each of the five receipts into the landing form in one
--       `fLvl≤fLvlD`, and no assembly composes two faces additively, so
--       each construction site takes exactly one lift.  What the
--       relaxation BUYS is the two *All edges: their receipt is a sum of
--       `subscribeE-caps`'s growth indices, which does NOT fit inside one
--       `fCharge` (Sub-Charge-Probe (DELETED; git history) § 0/§ 1, measured) and
--       does fit inside one refreshed frame level, which is what `fLvlD`
--       spends and what `Walk-Hyps.sf-step` already consumes.
--   (b) THE OUTPUT WIDTH — `valsCaps?` rather than `all valCaps?`, i.e.
--       `length out ≤ suc (cWid (frameStep (j + j′) c))`.  The walk's
--       Vb is valsCaps? because the NEXT frame's receipt reads it: a
--       scan-f frame costs `suc (length vals * suc (sizeᵗ fn))`, so
--       without the width the chain's second frame has no bound at all.
--
-- AND THE FACE IS NOT A STRENGTHENING OF `stepFrame-caps`, which was
-- tried first and does not fit: (a) needs the INPUT width, and the
-- companion's two callers — foldPath-caps and pushBurst-caps — have
-- none to give (pushBurst splits one emit's events, and how MANY values
-- an emit carries is not what `burstCaps?` bounds).  So the face keeps
-- the stronger hypothesis `valsCaps? (frameStep j c) sl vals`, which is
-- exactly the walk's own Vb, and is its own clause split.
--
-- THE RECEIPT TABLE, clause by clause, and it is the number the frame
-- lemmas were already building:
--
--   map-f        j′ = suc (sizeᵗ fn)                    out = |vals|
--   scan-f       j′ = suc (length vals * suc (sizeᵗ fn)) out = |vals|
--   take-f       j′ = 0                                 out ≤ |vals|
--   from-inner   0 on every clause but concat's drain
--   thru-outer   one subscribe per payload
--
-- and fCharge admits the first three with the scan row EXACT: `cWid
-- (frameStep j c)` IS `widAt` and `cSize (frameStep j c)` IS `sizeAt`,
-- both by refl (frameStep's fields are `iterFold` / `iterSize` at the
-- same S), so `suc (length vals * suc (sizeᵗ fn)) ≤ fCharge` is ONE
-- `*-mono-≤` over valsCaps?'s width conjunct and frameSz?'s size one.
--
-- WHAT IS LEFT IS BOTH CONJUNCTS ON THE TWO *All EDGES, and (a) is the
-- harder one, which is the opposite of what was written here before.
-- `concatDrain` and `thruWalk` CONCATENATE the bursts of the inners
-- they subscribe, so (b), the output width, is a SUM over payloads of
-- one subscribeE burst's VALUE COUNT — no caps-side companion reports
-- one (`burstCaps?` bounds each event, never how many there are),
-- though `valCaps?`'s own `pWᵛ` conjunct already bounds each payload's
-- `outWᵛ`, which is that count's entry measure.  (a), the RECEIPT, now
-- HAS a target it can hit — the landing form above — but no SUPPLIER
-- yet: `subscribeE-caps` still bounds its own j′ by nothing at all, the
-- same hole .Wet's GAP note names from the wet side, and the signature
-- pass that surfaces it is what the two postulates now wait on alone.
--
-- WHY IT IS NOT THE REFUTED AXIOM.  `stepFrame-entry-caps` asserted
-- the post-state and the output burst were back under the caps the
-- frame STARTED at; this reports them at `frameStep (j + j′) c`, the
-- level the frame's own folds grew to, which is exactly what
-- `stepFrame-caps` proves.  The refuting witness satisfies this face
-- with room: at `c = caps 3 1 1` the map-f frame's receipt is
-- `suc (sizeᵗ dup) = 4`, inside `fCharge 3 1 0 = 9`, its output value
-- has size 7 inside `cSize (frameStep 4 c) = 4665`, and its one
-- payload is inside `suc cWid`.
--
-- WHAT WOULD REFUTE IT: one frame, run under `capsOK? (frameStep j c)`
-- with a chain inside `pathSz? (cSize (frameStep j c))` and a burst
-- inside `valsCaps? (frameStep j c) sl`, whose smallest admissible
-- growth index leaves the frame above `fLvlD S W d j`, or whose output
-- burst is wider than
-- `suc (cWid (frameStep (j + j′) c))` for every admissible j′.  The
-- corner to aim at is `thru-outer`, which subscribes once per payload:
-- Frame-Work-Probe measures its per-frame payload count climbing 6 ↦
-- 120 across arrivals, against a cWid that `wid-dominates-120` puts at
-- ≥ 1024 one cascade in
------------------------------------------------------------------

-- the tuple the face reports, named once so the assembly and its five
-- clause pieces read the same five conjuncts.
--
-- THE EVENTS CONJUNCT WAS MOVED HERE FROM THE WET FACE (2026-08-10),
-- and the move is load-bearing, not cosmetic: stated on the wet side at
-- a UNIVERSAL j′ whose only witnesses are state/vals receipts, the
-- conjunct had no supplier — an emitted root delivery is pinned by no
-- hypothesis, so a program whose inner delivers one large root value
-- while its post-state stays small satisfies every hypothesis at j′ = 0
-- and fails the conclusion.  The suppliers that DO carry it —
-- `innerFinish-caps` and `subscribeInner-caps` (Subscribe-Face, PROVEN)
-- — report it at the SAME j′ they mint for the state receipts, and this
-- face is the only route that witness travels; dropping the conjunct
-- here is what stranded the wet side with an unprovable statement.
FrameFace : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (d j : ℕ) (sl : Slots Γ) →
  List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e → Set
FrameFace c d j sl r =
  Σ ℕ λ j′ →
     (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d j)
     × (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)

-- EVERY GROUND CLAUSE STILL PAYS `fCharge`, and this is the one lift
-- that carries it to the landing form.  `fLvl S W j` IS `j + fCharge
-- S W j` by refl, so a receipt inside fCharge lands inside `fLvlD`'s
-- zeroth story and every story above it (`fLvl≤fLvlD`, .Caps).  No
-- assembly composes two faces additively, so each construction site
-- takes exactly one of these
face-lift : ∀ (c : Caps) (d j j′ : ℕ) →
  j′ ≤ fCharge (Caps.cSize c) (Caps.cWid c) j →
  j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) d j
face-lift c d j j′ h =
  ≤-trans (+-monoʳ-≤ j h) (fLvl≤fLvlD (Caps.cSize c) (Caps.cWid c) d j)

------------------------------------------------------------------
-- GRINDING THE TREE, most uncertain first: subscribeInner-caps, the
-- self-feeding edge.  The inner observable is drawn from a BURST
-- PAYLOAD rather than from the syntax, so every hypothesis it hands to
-- subscribeE-caps comes off valCaps? — its size from the cSize half,
-- its chain from κ extended by the from-inner frame.  If the caps face
-- were going to fail to close on itself, it would fail here.
--
-- It does not.  The clause is two lines: out of gas, nothing happens
-- (j′ = 0, a dry close, no values); with gas, subscribeE-caps at the
-- extended path, then split the burst.
--
-- AND THIS IS WHERE THE HOP PAYS ITS j.  Under the old joint bound the
-- clause consumed `suc (pathLen κ) + sizeᵛ (obs u) o ≤ cSize` and built
-- the extended chain's hypotheses out of its slack — free, and false on
-- real runs (Joint-Probe).  Now it recurses at level `suc j` instead:
-- one j buys `sizeStep S B ≥ suc B`, which is the one extra frame, and
-- the receipt comes back as `suc j₂` rather than `j₂` — `+-suc` is the
-- only arithmetic the change costs, three times, once per output.
------------------------------------------------------------------

-- capsOK? reads slots, live and the store — never the node counter, so
-- minting an instance id is free (record eta makes this refl)
capsOK?-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (k : NodeId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { nextNode = k }) st ≡ true
capsOK?-nextNode c k sched st h = h

-- splitting one emit's events, and a whole burst, at the caps
splitEvents-vals-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? c sl) es ≡ true →
  all (valCaps? c sl s) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-caps c sl []              h = refl
splitEvents-vals-caps c sl (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h)))
splitEvents-vals-caps c sl (init _    ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (close _ _ ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (handoff _ ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (complete  ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))

-- (b2) THE PAYLOAD COUNT, and the enumeration that makes it free.
-- `splitEvents` is a partition and nothing else: `value v ∷ es` conses v
-- onto the payloads, init / close / handoff cons themselves onto the
-- bookkeeping, `complete` sets the flag, and NO clause grows either
-- list.  So the payload list's length is `valCountᵉ` on the nose — the
-- count is a property of the EMIT, not of the split, and the split can
-- only be told it.
splitEvents-len : ∀ {n} {Γ : Ctx n} {u : Ty} {A : Set}
  (es : List (InstEvent (Val Γ u))) →
  length (proj₁ (splitEvents {A = A} es)) ≡ valCountᵉ es
splitEvents-len []              = refl
splitEvents-len {A = A} (value _   ∷ es) = cong suc (splitEvents-len {A = A} es)
splitEvents-len {A = A} (init _    ∷ es) = splitEvents-len {A = A} es
splitEvents-len {A = A} (close _ _ ∷ es) = splitEvents-len {A = A} es
splitEvents-len {A = A} (handoff _ ∷ es) = splitEvents-len {A = A} es
splitEvents-len {A = A} (complete  ∷ es) = splitEvents-len {A = A} es

-- and the (b2) STATEMENT: the same split, landing in valsCaps? — the
-- LENGTH conjunct alongside the caps — under the emit's own count.  This
-- is the form stepFrame-caps's payload premise wants; it asks for
-- `all (valCaps? …)` today, which is exactly the cardinality-free half
splitEvents-valsCaps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? c sl) es ≡ true →
  valCountᵉ es ≤ suc (Caps.cWid c) →
  valsCaps? c sl (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-valsCaps {Γ = Γ} {s = s} {u = u} c sl es h hc =
  ∧-intro (splitEvents-vals-caps {u = u} c sl es h)
          (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (≤-reflexive (splitEvents-len {A = Val Γ u} es)) hc)))

splitEvents-bk-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? c sl) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-caps c sl []               = refl
splitEvents-bk-caps {u = u} c sl (value _  ∷ es) = splitEvents-bk-caps {u = u} c sl es
splitEvents-bk-caps {u = u} c sl (init _   ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (close _ _ ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (handoff _ ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (complete ∷ es) = splitEvents-bk-caps {u = u} c sl es

splitBurst-vals-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ s) →
  burstCaps? c sl str ≡ true →
  all (valCaps? c sl s) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-caps c sl []         h = refl
splitBurst-vals-caps {Γ = Γ} {u = u} c sl (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-caps c sl (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-caps {u = u} c sl ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ s) →
  all (eventCaps? c sl) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-caps c sl []         = refl
splitBurst-bk-caps {Γ = Γ} {u = u} c sl (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-caps {u = u} c sl (InstEmit.events em))
    (splitBurst-bk-caps {u = u} c sl ems)

------------------------------------------------------------------
-- THE SHARED-SLOT PAIR, GROUND — and the second side condition the
-- tree needs.
--
-- REGISTERING COSTS EXACTLY ONE j, and it is the first clause anywhere
-- in the tree that spends a fold on the cReg dimension rather than on
-- cSize or cWid.  The registry gains one entry, so the count conjunct
-- needs one more unit of headroom; frameStep-reg-suc says one j buys
-- `cReg c * cSize c` of it — which is at least one exactly when the cap
-- admits a registration at all.
--
-- SO THE REGISTERING COMPANIONS CARRY `1 ≤ Caps.cReg c`, alongside
-- `2 ≤ Caps.cSize c`, and it is not decoration either: at cReg c = 0 the
-- statement is FALSE, since cReg (frameStep j c) is `0 * suc (j * S)` =
-- 0 at every j and a registry of length one cannot fit under it.  It is
-- threaded UNCHANGED (c never moves inside a frame) and is supplied at
-- the top by 1≤capsAt-reg below, which the recurrence proves rather than
-- assumes — the same discipline 2≤capsAt-size already follows.  The
-- delivery clique never registers, so it does not carry it.
------------------------------------------------------------------

register-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  capsOK? (frameStep (suc j) c) sched (register src κ st) ≡ true
register-caps {u = u} c j src κ sched st 2≤S 1≤R inv pC =
    ∧-intro h0
    (∧-intro (all-++-intro (λ en → pathSz? (Caps.cSize (frameStep (suc j) c))
                                     (proj₂ (proj₂ (proj₂ en))))
                (EvalSt.registry st) ((EvalSt.nextReg st , src , u , κ) ∷ [])
                h1 (∧-intro (pathSz?-⊑ κ (frameStep-mono-j c 2≤S (n≤1+n j)) pC) refl))
    (∧-intro h2
    (∧-intro h3 COUNT)))
  where
  inv′ = capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st
           (frameStep-mono-j c 2≤S (n≤1+n j)) inv
  P    = capsOK?-parts (frameStep (suc j) c) sched st inv′
  h0   = proj₁ P
  h1   = proj₁ (proj₂ P)
  h2   = proj₁ (proj₂ (proj₂ P))
  h3   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  1≤RS : 1 ≤ Caps.cReg c * Caps.cSize c
  1≤RS = ≤-trans (≤-reflexive refl) (*-mono-≤ 1≤R (≤-trans (s≤s z≤n) 2≤S))
  COUNT : (length (EvalSt.registry st ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
             ≤ᵇ Caps.cReg (frameStep (suc j) c)) ≡ true
  COUNT = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (≤-reflexive (length-++ (EvalSt.registry st)))
      (≤-trans (+-mono-≤ (capsOK?-count (frameStep j c) sched st inv) 1≤RS)
               (≤-reflexive (frameStep-reg-suc c j)))))

-- a share's connect burst is re-kinded on the way up, and eventCaps?
-- does not read the kind
sharedPlumb-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ u) →
  burstCaps? c sl str ≡ true → burstCaps? c sl (sharedPlumb str) ≡ true
sharedPlumb-caps c sl []         h = refl
sharedPlumb-caps c sl (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-caps c sl ems (proj₂ (∧-true _ _ h)))

-- dropping a source's registrations without sweeping the live set: the
-- registry shrinks and nothing else moves
dropOnly-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { registry = dropSource src (EvalSt.registry st) })
    ≡ true
dropOnly-caps c src sched st inv =
    ∧-intro h0
    (∧-intro (dropSource-all (λ en → pathSz? (Caps.cSize c)
                                       (proj₂ (proj₂ (proj₂ en))))
                src (EvalSt.registry st) h1)
    (∧-intro h2
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- `j + 1` and `j + suc k` against the shapes register-caps and
-- subscribeE-caps hand back
j+1 : ∀ (j : ℕ) → j + 1 ≡ suc j
j+1 j = trans (+-suc j 0) (cong suc (+-identityʳ j))

------------------------------------------------------------------
-- GRINDING stepFrame-caps, THE CLAUSE THAT PAYS A j.
--
-- Five clauses, and they split cleanly in two.  THREE ARE STRUCTURAL —
-- take-f is a filter on the payload list plus a registry cut, from-inner
-- and thru-outer delegate to innerFinish-caps and thruWalk-caps and then
-- do node bookkeeping — so they spend no folds at all and are ground
-- here.  TWO ARE ARITHMETIC: map-f and scan-f are the sites where a
-- value is actually built, by `applyFn`, and what they cost is the
-- subject of stepFrame-value-caps below.
--
-- The leaves first, in the order the clauses consume them.
------------------------------------------------------------------

-- setNode's caps face.  Measures has the size half (setNode-bounded);
-- this is the width half, the same three-line induction
setNode-widNode : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ)
  (nid : NodeId) (ns : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
  widNode W sl ns ≡ true →
  all (λ kv → widNode W sl (proj₂ kv)) nodes ≡ true →
  all (λ kv → widNode W sl (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-widNode W sl nid ns []             bn h = ∧-intro bn refl
setNode-widNode W sl nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-widNode W sl nid ns r bn (proj₂ (∧-true _ _ h)))

-- so installing one bounded node keeps all five conjuncts: the registry,
-- the live set and the slot telescope are untouched
capsOK?-setNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedNode (Caps.cSize c) ns ≡ true →
  widNode (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) ≡ true
capsOK?-setNode {Γ = Γ} c nid ns sched st bn wn inv =
    ∧-intro (∧-intro (proj₁ hL)
                     (setNode-bounded (Caps.cSize c) nid ns (EvalSt.nodes st) bn
                        (proj₂ hL)))
    (∧-intro h1
    (∧-intro h2
    (∧-intro (setNode-widNode (Caps.cWid c) (Sched.slots sched) nid ns
                (EvalSt.nodes st) wn h3)
             h4)))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- take's cut is dropSweep's sibling: cutThrough is a filter on the
-- registry (by node membership rather than by source), its closes carry
-- no payload, and the live set is swept against what it kept
cutThrough-regsSz : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsSz? B reg ≡ true → regsSz? B (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regsSz B nid d wm dy []                    h = refl
cutThrough-regsSz B nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regsSz B nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | _ | ih = ih
... | false | _ | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closes-caps : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (sl : Slots Γ)
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventCaps? c sl) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closes-caps c sl nid d wm dy []                     = refl
cutThrough-closes-caps c sl nid d wm dy ((rid , src , ch) ∷ r)
  with pathHasNode nid (proj₂ ch) | cutThrough nid d wm dy r
     | cutThrough-closes-caps c sl nid d wm dy r
... | false | _ | ih = ih
... | true  | _ | ih with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

-- the cut's whole state move, in one lemma: registry filtered, live
-- swept against the survivors, and one node overwritten
cutSweep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedNode (Caps.cSize c) ns ≡ true →
  widNode (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  capsOK? c sched st ≡ true →
  let kept = proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                               (EvalSt.dying st) (EvalSt.registry st))
  in capsOK? c (record sched { live = sweepLive kept (Sched.live sched) })
               (record st { registry  = kept
                          ; cancelled = proj₂ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                                       (EvalSt.regWatermark st)
                                                       (EvalSt.dying st)
                                                       (EvalSt.registry st)))
                                        ++ EvalSt.cancelled st
                          ; nodes     = setNode nid ns (EvalSt.nodes st) }) ≡ true
cutSweep-caps {Γ = Γ} c nid ns sched st bn wn inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ hL))
                     (setNode-bounded (Caps.cSize c) nid ns (EvalSt.nodes st) bn
                        (proj₂ hL)))
    (∧-intro (cutThrough-regsSz (Caps.cSize c) nid (EvalSt.delivered st)
                (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro (setNode-widNode (Caps.cWid c) (Sched.slots sched) nid ns
                (EvalSt.nodes st) wn h3)
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (cutThrough-len nid (EvalSt.delivered st)
                                          (EvalSt.regWatermark st) (EvalSt.dying st)
                                          (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                           (EvalSt.dying st) (EvalSt.registry st))
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- take passes a PREFIX of what it was given, so its payload bound is
-- inherited rather than paid for
takeVals-caps : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (k : ℕ) (vals : List (Val Γ s)) →
  all (valCaps? c sl s) vals ≡ true →
  all (valCaps? c sl s) (proj₁ (takeVals k vals)) ≡ true
takeVals-caps c sl zero          vals      h = refl
takeVals-caps c sl (suc k)       []        h = refl
takeVals-caps c sl (suc zero)    (v ∷ vs)  h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-caps c sl (suc (suc k)) (v ∷ vs)  h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-caps c sl (suc k) vs (proj₂ (∧-true _ _ h)))

-- THE take-f CLAUSE, and it spends no folds: j′ = 0 either way
takeDispatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  all (valCaps? c sl s) vals ≡ true →
  let r = takeDispatch {t = t} nid vals fin sched st mns
  in (capsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
        ≡ true)
     × (all (valCaps? c sl s) (proj₁ r) ≡ true)
     × (all (eventCaps? c sl) (proj₁ (proj₂ r)) ≡ true)
takeDispatch-caps c nid vals fin sl sched st (just (take-st k)) slEq inv vC
  with proj₂ (proj₂ (takeVals k vals))
... | true  = cutSweep-caps c nid (take-st zero) sched st refl refl inv
            , takeVals-caps c sl k vals vC
            , subst (λ x → all (eventCaps? c x)
                             (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                              (EvalSt.regWatermark st) (EvalSt.dying st)
                                              (EvalSt.registry st)))) ≡ true)
                    slEq
                    (cutThrough-closes-caps c (Sched.slots sched) nid
                       (EvalSt.delivered st) (EvalSt.regWatermark st)
                       (EvalSt.dying st) (EvalSt.registry st))
... | false = capsOK?-setNode c nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                sched st refl refl inv
            , takeVals-caps c sl k vals vC
            , refl
takeDispatch-caps c nid vals fin sl sched st nothing slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (scan-st _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (merge-st _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (concat-st _ _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (switch-st _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (exhaust-st _ _)) slEq inv vC = inv , refl , refl

-- reading a node back out at the caps, so a clause that REINSTALLS one
-- (thruWrap sets only the `done` flag) can show the payload it keeps is
-- still bounded.  Mirrors Wet's lookupNode-B
NodeCaps : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → Maybe (NodeState Γ) → Set
NodeCaps c sl nothing   = ⊤
NodeCaps c sl (just ns) =
  (boundedNode (Caps.cSize c) ns ≡ true) × (widNode (Caps.cWid c) sl ns ≡ true)

lookupNode-caps : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) nodes ≡ true →
  all (λ kv → widNode (Caps.cWid c) sl (proj₂ kv)) nodes ≡ true →
  NodeCaps c sl (lookupNode nid nodes)
lookupNode-caps c sl nid []            hb hw = tt
lookupNode-caps c sl nid ((k , s) ∷ r) hb hw with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ hb) , proj₁ (∧-true _ _ hw)
... | false = lookupNode-caps c sl nid r (proj₂ (∧-true _ _ hb)) (proj₂ (∧-true _ _ hw))

-- the two projections of capsOK? the node ring needs
capsOK?-nodeSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st) ≡ true
capsOK?-nodeSz {Γ = Γ} c sched st h =
  proj₂ (∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
                (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
                (proj₁ (capsOK?-parts c sched st h)))

capsOK?-nodeWid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
      (EvalSt.nodes st) ≡ true
capsOK?-nodeWid c sched st h = proj₁ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st h))))

-- THE thru-outer WRAP: the walk has already run, and all this does is
-- stamp `done` on the node it found, keeping that node's payload.  No
-- values are built, so no folds are spent
thruWrap-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (op : AllOp) (nid : NodeId) (fin : Bool) (sl : Slots Γ)
  (out : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  capsOK? c (proj₁ (proj₂ (proj₂ out))) (proj₂ (proj₂ (proj₂ out))) ≡ true →
  all (valCaps? c sl u) (proj₁ out) ≡ true →
  all (eventCaps? c sl) (proj₁ (proj₂ out)) ≡ true →
  let r = thruWrap op nid fin out
  in (capsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valCaps? c sl u) (proj₁ r) ≡ true)
     × (all (eventCaps? c sl) (proj₁ (proj₂ r)) ≡ true)
thruWrap-caps c op nid false sl (vs , bs , sd , st) inv vC eC = inv , vC , eC
thruWrap-caps c mergeᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps c (Sched.slots sd) nid (EvalSt.nodes st)
         (capsOK?-nodeSz c sd st inv) (capsOK?-nodeWid c sd st inv)
... | just (merge-st k od) | (bn , wn) =
      capsOK?-setNode c nid (merge-st k true) sd st refl refl inv , vC , eC
... | nothing              | _ = inv , vC , eC
... | just (scan-st _)     | _ = inv , vC , eC
... | just (take-st _)     | _ = inv , vC , eC
... | just (concat-st _ _ _) | _ = inv , vC , eC
... | just (switch-st _ _) | _ = inv , vC , eC
... | just (exhaust-st _ _) | _ = inv , vC , eC
thruWrap-caps c concatᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps c (Sched.slots sd) nid (EvalSt.nodes st)
         (capsOK?-nodeSz c sd st inv) (capsOK?-nodeWid c sd st inv)
... | just (concat-st q act od) | (bn , wn) =
      capsOK?-setNode c nid (concat-st q act true) sd st bn wn inv , vC , eC
... | nothing              | _ = inv , vC , eC
... | just (scan-st _)     | _ = inv , vC , eC
... | just (take-st _)     | _ = inv , vC , eC
... | just (merge-st _ _)  | _ = inv , vC , eC
... | just (switch-st _ _) | _ = inv , vC , eC
... | just (exhaust-st _ _) | _ = inv , vC , eC
thruWrap-caps c switchᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
      capsOK?-setNode c nid (switch-st cur true) sd st refl refl inv , vC , eC
... | nothing              = inv , vC , eC
... | just (scan-st _)     = inv , vC , eC
... | just (take-st _)     = inv , vC , eC
... | just (merge-st _ _)  = inv , vC , eC
... | just (concat-st _ _ _) = inv , vC , eC
... | just (exhaust-st _ _) = inv , vC , eC
thruWrap-caps c exhaustᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act od) =
      capsOK?-setNode c nid (exhaust-st act true) sd st refl refl inv , vC , eC
... | nothing              = inv , vC , eC
... | just (scan-st _)     = inv , vC , eC
... | just (take-st _)     = inv , vC , eC
... | just (merge-st _ _)  = inv , vC , eC
... | just (concat-st _ _ _) = inv , vC , eC
... | just (switch-st _ _) = inv , vC , eC

------------------------------------------------------------------
-- THE *All OUTER EDGE, GROUND: thruConsume-caps and thruWalk-caps.
--
-- These are the two companions the joint bound blocked.  thruConsume
-- was always provable — its hypotheses are subscribeInner-caps's
-- verbatim — and what its CALLER owed it was a joint bound it did not
-- have.  Under the separate pair the two line up exactly: thruWalk
-- carries `suc (pathLen κ) ≤ cSize` and hands that same conjunct down,
-- per payload, unchanged.
--
-- The per-op node bookkeeping stores nothing the caps do not already
-- bound: merge's counter and switch's current-inner carry no payload,
-- exhaust's flag none either, and concatAll's queue stores the payload
-- VERBATIM — so its bound is the valCaps? already in hand, appended to
-- the queue's own by all-++-intro.  switchAll's cut is the only clause
-- that moves the registry, and it is cutSweep-caps without the node.
------------------------------------------------------------------

-- merge's counter is a node both bounds accept unconditionally, so
-- bumping it is a setNode of something already bounded
capsOK?-mergeBump : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (done : Bool) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { nodes = mergeBump nid done (EvalSt.nodes st) }) ≡ true
capsOK?-mergeBump c nid done sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od) =
      capsOK?-setNode c nid (merge-st (if done then k else suc k) od) sched st
        refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

-- switchAll's cut: registry filtered, live swept against the survivors,
-- the cancelled ledger grown — and capsOK? reads none of the last
switchKill-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  let r = switchKill {t = t} cur sched st
  in capsOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
switchKill-caps c nothing  sched st inv = inv
switchKill-caps {Γ = Γ} c (just v) sched st inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ hL))
                     (proj₂ hL))
    (∧-intro (cutThrough-regsSz (Caps.cSize c) v (EvalSt.delivered st)
                (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (cutThrough-len v (EvalSt.delivered st)
                                          (EvalSt.regWatermark st) (EvalSt.dying st)
                                          (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = proj₁ (cutThrough v (EvalSt.delivered st) (EvalSt.regWatermark st)
                           (EvalSt.dying st) (EvalSt.registry st))
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- the cut's closes carry no payload
switchKill-closes-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  all (eventCaps? c sl) (proj₁ (switchKill {t = t} {e = e} cur sched st)) ≡ true
switchKill-closes-caps c sl nothing  sched st = refl
switchKill-closes-caps c sl (just v) sched st =
  cutThrough-closes-caps c sl v (EvalSt.delivered st) (EvalSt.regWatermark st)
    (EvalSt.dying st) (EvalSt.registry st)

------------------------------------------------------------------
-- concatAll's DRAIN and the *All FINISH, ground.  The queue is the one
-- node whose stored observables the size conjunct bounds directly —
-- `obsCaps?` IS `valCaps? … (obs s)`, definitionally — so the residue
-- goes back into the node with the bound it came out with, and the
-- drain's receipts add exactly as thruWalk's do.
------------------------------------------------------------------

-- the queue's two halves, as boundedNode and widNode read them
obsList-nodeSz : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (obsCaps? c sl) q ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q ≡ true
obsList-nodeSz c sl []      h = refl
obsList-nodeSz {n = n} c sl (o ∷ q) h
  with ∧-true (obsCaps? c sl o) (all (obsCaps? c sl) q) h
... | h1 , h2 =
  ∧-intro (proj₁ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize c)
                         (pWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeSz c sl q h2)

-- and back again, which is how the drained residue re-enters the node
obsList-intro : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q ≡ true →
  all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true →
  all (obsCaps? c sl) q ≡ true
obsList-intro c sl []      hsz hwd = refl
obsList-intro {n = n} c sl (x ∷ q) hsz hwd
  with ∧-true (sizeᵉ x ≤ᵇ Caps.cSize c)
              (all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q) hsz
     | ∧-true (pWᵉ n sl x ≤ᵇ Caps.cWid c)
              (all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q) hwd
... | s1 , s2 | w1 , w2 = ∧-intro (∧-intro s1 w1) (obsList-intro c sl q s2 w2)

obsList-nodeWid : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (obsCaps? c sl) q ≡ true →
  all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true
obsList-nodeWid c sl []      h = refl
obsList-nodeWid {n = n} c sl (o ∷ q) h
  with ∧-true (obsCaps? c sl o) (all (obsCaps? c sl) q) h
... | h1 , h2 =
  ∧-intro (proj₂ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize c)
                         (pWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeWid c sl q h2)

