------------------------------------------------------------------
-- THE RECURSION, AFTER IT LEFT THE MACHINE IT NAMES.

-- WHY IT IS A MODULE OF ITS OWN, AND THE REASON IS CONTAINMENT RATHER
-- THAN SIZE.  What is collected here is exactly the twenty definitions
-- the recursion reaches — the block below says which edges carry it and
-- what each costs.  Nothing here decreases and no pragma is admissible
-- on the proof path, so Agda rejects this module; the split is what
-- stops that verdict reaching anything else.  `Rx.Evaluator` keeps the
-- types, the schedule, the store and every helper that terminates on its
-- own argument, and it compiles; `Rx.Evaluator.Domain` indexes its
-- relations by RESULT, so it needs nothing from here either.
--
-- AND THE MEMBERSHIP IS CHECKED RATHER THAN CURATED.  `make
-- recursion-cover` reads THIS file's call graph, so a definition that
-- stops recursing belongs back down in the machine and one that starts
-- has to arrive here — the count it prints is the move set, not a list
-- anybody maintains.
--
-- UNTIL THE BUILDER LANDS THIS FILE IS THE ONE RED MODULE IN THE TREE,
-- and it is red for a reason that is written down rather than for one
-- that has to be rediscovered.
------------------------------------------------------------------
module Rx.Evaluator.Run where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _∸_; _≡ᵇ_; _≤_; _<_)
open import Data.Nat.Properties using (_<?_; ≤-refl)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Induction.WellFounded using (Acc; acc)
open import Data.List    using (List; []; _∷_; _++_; map; null)
open import Data.Bool.ListAction using (any)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Tick; Fuel; Id; Source; after_,_; hot; cold; InstEvent; init; value; close; handoff;
  complete; exhausted; subscribe; delivery; InstEmit; _at_from_as_)
open import Rx.Exp  using (obs; _≟ᵗ_; Ctx; Val; Closed; applyFn; evalTm; unfoldμ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (scripted; shared; Slots)
open import Rx.Evaluator using (AllOp; Arrival; AtFloor; EvalSt; Frame; NodeId; NodeState; Path; RegId;
  Sched; Stream; _↠_; aliveThroughᶠ; arrSource; arrTick; arrTy; arrVal; atDyn;
  atSlot; burstCompleted; cascadeFinish; cascadeLatch; chainsOf; dropSource;
  exhaust-st; floorFalls; from-inner; hasRoom; installNode; lookupNode;
  lowerFloor; map-f; memberSource; mergeAll-st; mergeAllBump; mintNode;
  mintOrdinal; mintSource; oneShotBurst; register; resolve; retagEvents; root;
  mergeAllᵒ; switchᵒ; exhaustᵒ;
  scan-f; scan-st; scanVals; sched-init; sched-next; setNode; share-sink;
  shareAdmit; shareFinish; shareLatch; sharedPlumb; spentBurst; splitBurst;
  splitEvents; st-init; switch-st; switchKill; take-f; take-st; takeDispatch;
  thru-outer; thruWrap)

variable
  lo : ℕ

-- THE DESCENT DISCIPLINE, AND THE MACHINE NO LONGER CARRIES IT.  Three
-- edges below reach a deeper subscribe without descending the term:
--
--   · `sharedConnect → subscribeE`, at the definition a slot stores;
--   · `subscribeInner → subscribeE`, at a runtime observable;
--   · `subscribeE (μᵉ body) → subscribeE (unfoldμ body)`.
--
-- Each used to TEST a reading and emit a marker on the negative answer,
-- which made an inadequate figure a wrong ANSWER rather than an open
-- obligation — and so put the whole measure inside the run, where every
-- syntactic candidate for it died.  The obligation is the DERIVATION's
-- now: `Rx.Evaluator.Domain` relates a call to its result with a
-- sub-derivation per edge, so an edge that cannot be justified is a
-- proof that does not exist rather than a run that emits something.
--
-- SO THIS MODULE NO LONGER TERMINATES BY ITSELF, AND THAT IS THE TRADE.
-- Agda's checker sees three non-structural calls and nothing decreasing;
-- no pragma is admissible here, so what stands in its place is
-- `Verify-Rank-Sufficient.Doorless`, whose builder returns a result
-- together with its derivation and pays the three facts at the sites
-- that hold them.  `deferᵉ` is not one of the three: it parks the body
-- for `suc now`, a later instant entered afresh.

-- AND THE EDGE SET IS CHECKED RATHER THAN READ OFF, WHICH MATTERS MORE
-- NOW THAN IT DID.  `make recursion-cover` cuts the edges declared below
-- and requires every cycle still standing to be declared too: cutting
-- three edges collapses BOTH of this module's multi-member recursions
-- and exactly one cycle survives, the pair that walks the expression.
-- While a witness was threaded, Agda was satisfied and silent about
-- which edges carried it; with no witness at all Agda is silent about
-- the whole question, so this check is the only thing that fails when a
-- clause opens a FOURTH edge — one the builder next door has no case
-- for and would never be asked to write.

-- THE SHARE HOP KEEPS ITS OWN DESCENT, AND IT IS THE SHAPE THE OTHER
-- THREE BECAME.  `Acc _<_ (n ∸ lo)` is peeled by MATCHING on
-- `floorFalls`, a proof about the sink constructor's own premise — so it
-- asks nothing, has no negative answer, and needs no arm.  It never had
-- a door to kill.  It reaches the frame walk one way only: nothing in
-- the subscribe recursion calls back into it.

-- PEEL: subscribeInner -> subscribeE
-- PEEL: sharedConnect -> subscribeE
-- PEEL: dispatchShare -> shareGo
-- STRUCTURAL SCC: subscribeE subscribeAll

-- THE ONE DECLARATION TAKEN ON TRUST IS THAT LAST PAIR, and it is the
-- μ edge that makes it worth naming.  `subscribeE` reaches
-- `subscribeAll` and back on a strictly smaller expression at every
-- operator node, so the pair is structural — except at `μᵉ`, where the
-- body is UNFOLDED rather than descended into and the third drop lives.
-- A self-edge is invisible to a component check, so this is where the
-- check stops and syncSize starts.

-- the subscription machine: walk the target expression, minting
-- NodeIds for its operator nodes and installing their states (evalTm
-- for takeᵉ counts, scanᵉ seeds); register every internal source's
-- chains, each local path extended with the given rootward
-- continuation; anchor colds (resolve at the given tick) and deferᵉ
-- bodies (suc tick) on the schedule; and fire the sync burst NOW,
-- inside cascade `Id` (id-inheritance), emitting init per new
-- registration.  Declared here, defined after stepFrame — the two are
-- mutually recursive: the burst re-enters the pipeline one frame at a
-- time (pushBurst → stepFrame), and the *All frames subscribe inners
-- (stepFrame → subscribeInner → subscribeE)
-- AND THE BOUND RIDES ALONG AS AN IMPLICIT, WHICH IS WHAT KEEPS IT OFF
-- THE CALL SITES.  A subscription's expression may name only inputs
-- below the floor its continuation sinks at, and that is what the
-- `input i` clause spends to register one above `i`.  `T b` is `⊤`
-- wherever `b` computes, so at a concrete program Agda's eta solves the
-- argument and nothing is written; only a statement quantifying over the
-- expression carries it, which is the content.  `Rx.Inputs-Below` holds
-- the descent arm each clause spends.
subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
           → (b : Closed Γ u)
           → Path Γ lo u t → Id → Tick
           → Sched Γ → EvalSt e
           → Stream Γ u × Sched Γ × EvalSt e

-- mint the inner's exit-frame instance, subscribe it inside the
-- current instant, split its burst.  THE HOP EDGE, AND IT NO LONGER
-- ASKS ANYTHING.  The inner is a runtime VALUE, structurally unrelated
-- to the caller, so nothing about the caller's TERM makes it smaller —
-- which is why this clause used to compare what arrived against the
-- component it stands at and emit a marker on the negative answer.  The
-- comparison is a PREMISE now and it is owed by the derivation rather
-- than by the run: `Verify-Rank-Sufficient.Doorless.subscribeInner!`
-- spends the report where the value was produced, so there is no
-- question here to answer and no arm to answer it with.
subscribeInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
               → AllOp → NodeId → Path Γ lo u t → Id → Tick
               → Val Γ (obs u) → Sched Γ → EvalSt e
               → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
subscribeInner {lo = lo} op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE o (from-inner op allNid inst ↠ κ) id now
                   (record sched { nextNode = suc inst }) st
      (vs , bs , done) = splitBurst burst
  in inst , vs , bs , done , sched′ , st′

thruConsume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
            → AllOp → NodeId → Path Γ lo u t → Id → Tick
            → Val Γ (obs u) → Sched Γ → EvalSt e
            → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruConsume {u = u} mergeAllᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = [] , [] , sched₀ , st₀
...   | yes refl with hasRoom lim act
...     | true =
          let (_ , vs , bs , done , sched₁ , st₁) =
                subscribeInner mergeAllᵒ nid κ id now o sched₀ st₀
          in vs , bs , sched₁ ,
             record st₁ { nodes = mergeAllBump nid done (EvalSt.nodes st₁) }
...     | false =
          [] , [] , sched₀ ,
          record st₀ { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                                 (EvalSt.nodes st₀) }
thruConsume mergeAllᵒ nid κ id now o sched₀ st₀ | _ = [] , [] , sched₀ , st₀
thruConsume switchᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (switch-st cur od) =
      let (closes , sched₁ , st₁) = switchKill cur sched₀ st₀
          (inst , vs , bs , done , sched₂ , st₂) =
            subscribeInner switchᵒ nid κ id now o sched₁ st₁
      in vs , closes ++ bs , sched₂ ,
         record st₂ { nodes = setNode nid
           (switch-st (if done then nothing else just inst) od) (EvalSt.nodes st₂) }
... | _ = [] , [] , sched₀ , st₀
thruConsume exhaustᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (exhaust-st true od)  = [] , [] , sched₀ , st₀   -- busy: drop
... | just (exhaust-st false od) =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner exhaustᵒ nid κ id now o sched₀ st₀
      in vs , bs , sched₁ ,
         record st₁ { nodes = setNode nid (exhaust-st (not done) od) (EvalSt.nodes st₁) }
... | _ = [] , [] , sched₀ , st₀

thruWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → AllOp → NodeId → Path Γ lo u t → Id → Tick
         → List (Val Γ (obs u)) → Sched Γ → EvalSt e
         → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruWalk op nid κ id now []       sched₀ st₀ = [] , [] , sched₀ , st₀
thruWalk op nid κ id now (o ∷ os) sched₀ st₀ =
  let (vs  , bs  , sched₁ , st₁) = thruConsume op nid κ id now o sched₀ st₀
      (vs′ , bs′ , sched₂ , st₂) = thruWalk op nid κ id now os sched₁ st₁
  in vs ++ vs′ , bs ++ bs′ , sched₂ , st₂

-- The count is THREADED and not re-read from the node table between
-- iterations, so a drained inner whose own synchronous burst routes
-- back through THIS node and finishes there is not seen by the rest of
-- the walk.  The face this replaced threaded a flag with the same
-- blind spot, so nothing regresses — but the loss is now quantitative
-- rather than one bit, which is what makes it worth naming: at limit 1
-- a missed self-finish costs the drain its only lane, at limit k it
-- can cost several, and the two do not fail the same way
mergeAllDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             → NodeId → Path Γ lo s t → Id → Tick
             → Maybe ℕ → ℕ → List (Closed Γ s) → Sched Γ → EvalSt e
             → List (Val Γ s) × List (InstEvent (Val Γ t)) × ℕ
               × List (Closed Γ s) × Sched Γ × EvalSt e
mergeAllDrain allNid κ id now lim act []      sched₀ st₀ =
  [] , [] , act , [] , sched₀ , st₀
mergeAllDrain allNid κ id now lim act (o ∷ q) sched₀ st₀
  with hasRoom lim act
... | false = [] , [] , act , o ∷ q , sched₀ , st₀
... | true =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner mergeAllᵒ allNid κ id now o sched₀ st₀
          (vs′ , bs′ , act′ , q′ , sched₂ , st₂) =
            mergeAllDrain allNid κ id now lim
              (if done then act else suc act) q sched₁ st₁
      in vs ++ vs′ , bs ++ bs′ , act′ , q′ , sched₂ , st₂

innerFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
            → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
            → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerFinish {s = s} mergeAllᵒ allNid inst κ id now vals sched st
            (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | yes refl =
      let (vs , bs , act′ , q′ , sched′ , st′) =
            mergeAllDrain allNid κ id now lim (pred act) q sched st
      in vals ++ vs , bs , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched′ ,
         record st′ { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′) }
... | no _ = vals , [] , false , sched , st
innerFinish switchᵒ allNid inst κ id now vals sched st (just (switch-st (just c) od)) =
  if c ≡ᵇ inst
  then (vals , [] , od , sched ,
        record st { nodes = setNode allNid (switch-st nothing od) (EvalSt.nodes st) })
  else (vals , [] , false , sched , st)
innerFinish exhaustᵒ allNid inst κ id now vals sched st (just (exhaust-st act od)) =
  vals , [] , od , sched ,
  record st { nodes = setNode allNid (exhaust-st false od) (EvalSt.nodes st) }
innerFinish _ allNid inst κ id now vals sched st _ = vals , [] , false , sched , st

-- a fin only completes THIS INNER once nothing under its exit frame
-- can ever deliver again: a sibling registration of the dying source
-- still queued this cascade, or any other live registration, absorbs
-- it (the TS join's open-multiset, read off the registry) — one
-- chain's exhaustion is not a multi-registration subtree's completion
innerReact : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
           → List (Val Γ s) → Sched Γ → EvalSt e → Bool
           → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerReact op allNid inst κ id now vals sched st false =
  vals , [] , false , sched , st
innerReact op allNid inst κ id now vals sched st true =
  if any (aliveThroughᶠ inst st) (EvalSt.registry st)
  then vals , [] , false , sched , st
  else innerFinish op allNid inst κ id now vals sched st
         (lookupNode allNid (EvalSt.nodes st))

stepFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Id → Tick → Frame Γ s u → Path Γ lo u t
          → List (Val Γ s) → Bool → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e

stepFrame id now (map-f fn) κ vals fin sched st =
  map (applyFn fn) vals , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} {u = u} id now (scan-f fn nid) κ vals fin sched st
  = dispatch (lookupNode nid (EvalSt.nodes st))
  where
  dispatch : Maybe (NodeState Γ)
           → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  dispatch (just (scan-st {w} ac)) with w ≟ᵗ u
  ... | yes refl =
        let (outs , ac′) = scanVals fn ac vals
        in outs , [] , fin , sched ,
           record st { nodes = setNode nid (scan-st ac′) (EvalSt.nodes st) }
  ... | no _ = [] , [] , fin , sched , st
  dispatch _ = [] , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} id now (take-f nid) κ vals fin sched st
  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

stepFrame id now (from-inner op allNid inst) κ vals fin sched st
  = innerReact op allNid inst κ id now vals sched st fin

stepFrame id now (thru-outer op nid) κ vals fin sched st
  = thruWrap op nid fin (thruWalk op nid κ id now vals sched st)

-- push a child subscription's sync burst through the one frame just
-- built above it: split each emit, step it, reassemble under the same
-- envelope — the burst leaves each subscription level already shaped
-- like any later emit of its source
pushBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Id → Tick → Frame Γ s u → Path Γ lo u t
          → Stream Γ s → Sched Γ → EvalSt e
          → Stream Γ u × Sched Γ × EvalSt e
pushBurst id now f κ []         sched st = [] , sched , st
pushBurst id now f κ (em ∷ ems) sched st =
  let sp   = splitEvents (InstEmit.events em)
      (vals′ , evs , fin′ , sched₁ , st₁) =
        stepFrame id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
      (rest , sched₂ , st₂) = pushBurst id now f κ ems sched₁ st₁
  in ((proj₁ (proj₂ sp) ++ retagEvents evs ++ map value vals′
        ++ (if fin′ then complete ∷ [] else []))
       at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
       ∷ rest , sched₂ , st₂

-- the shared *All shape: mint the node, install its initial state,
-- subscribe the outer under a thru-outer frame, push the burst through
subscribeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → AllOp → NodeState Γ → (b : Closed Γ (obs u))
             → Path Γ lo u t
             → Id → Tick → Sched Γ → EvalSt e
             → Stream Γ u × Sched Γ × EvalSt e
subscribeAll op initialState b κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE b (thru-outer op nid ↠ κ) id now sched₁
                   (installNode nid initialState st)
  in pushBurst id now (thru-outer op nid) κ burst sched₂ st₁

-- the connect is a non-structural edge: the def d is a stored
-- expression, structurally unrelated to the `input i` being
-- subscribed, so nothing about the term being walked shrinks here.
-- It is separated from `subscribeSharedSlot`'s other branches because
-- joining an already-connected share takes no edge at all, and lifted
-- out of its where block so the derivation can name it (as with
-- takeVals / thruConsume / mergeAllDrain)
sharedConnect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → (i : Fin n) → (d : Closed Γ (lookup Γ i))
              → Path Γ lo (lookup Γ i) t → toℕ i < lo → Id → Tick
              → Sched Γ → EvalSt e
              → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
-- THE CONNECT'S DESCENT IS A COUNT AND IT IS OWED ELSEWHERE NOW.
-- Connecting slot `i` puts `i` into the connected set, so the reading
-- over the slots NOT in that set drops by exactly one — provided `i`
-- was not already there, which is the branch `subscribeSharedSlot` took
-- to reach this clause.  That proviso is why the fact cannot be stated
-- free, and it is `Rx.Evaluator.Doorless.connect-edge`; the clause
-- itself reads nothing.
sharedConnect i d κ below id now sched st =
  let st₁ = register (atSlot i) (lowerFloor below κ)
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      (burst , sched₁ , st₂) =
        subscribeE d (share-sink i ≤-refl) id now sched st₁
      -- the def's connect burst flows up the first subscriber's own
      -- frames (the returned burst); dispatch only serves arrivals
  in if burstCompleted burst
     then -- the def died inside its own connect burst: latch, and
          -- this registration closes in the same instant
          (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
             at id from toℕ i as subscribe) ∷ sharedPlumb burst)
          , sched₁ ,
          record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                     ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
     else ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst
          , sched₁ , st₂

subscribeSharedSlot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    → (i : Fin n) → (d : Closed Γ (lookup Γ i))
                    → Path Γ lo (lookup Γ i) t → toℕ i < lo → Id → Tick
                    → Sched Γ → EvalSt e
                    → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
subscribeSharedSlot {Γ = Γ} {e = e} i d κ below id now sched st =
  if memberSource (toℕ i) (EvalSt.completedSources st)
  then spentBurst (toℕ i) id , sched , st
  else if memberSource (toℕ i) (EvalSt.connectedShares st)
  then -- live: join mid-flight, future values only
       ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
       , sched , register (atSlot i) (lowerFloor below κ) st
  else sharedConnect i d κ below id now sched st

subscribeE {lo = lo} {Γ = Γ} (input i) κ id now sched st with toℕ i <? lo
... | no _ = spentBurst (toℕ i) id , sched , st
... | yes below with Sched.slots sched i
...   | shared d =
      subscribeSharedSlot i d κ below id now sched st
...   | scripted (hot _) =
      if memberSource (toℕ i) (EvalSt.completedSources st)
      then -- spent script: a completed Subject — immediate
           -- close/complete, nothing registered
           spentBurst (toℕ i) id , sched , st
      else -- already live (sched-init, source = ordinal = toℕ i); just
           -- another registration — fan-out IS this multiplicity
           ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
           , sched , register (atSlot i) (lowerFloor below κ) st
...   | scripted (cold sync []) =
      let (burst , sched₁) = oneShotBurst sync id sched
      in burst , sched₁ , st
...   | scripted (cold sync (d ∷ ds)) =
      -- per-subscription anchoring: a fresh source per subscribe, the
      -- async tail resolved against the subscription tick
      let (src , sched₁) = mintSource sched
          (ord , sched₂) = mintOrdinal sched₁
          sched₃ = record sched₂
            { live = record { source = src ; ordinal = ord
                            ; elemTy = lookup Γ i
                            ; pending = resolve now (d ∷ ds) }
                     ∷ Sched.live sched₂ }
      in ((init src ∷ map value sync) at id from src as subscribe) ∷ []
         , sched₃ , register (atDyn src _) κ st

subscribeE (ofᵉ ts) κ id now sched st =
  let (burst , sched₁) = oneShotBurst (map (λ tm → evalTm tm) ts) id sched
  in burst , sched₁ , st

subscribeE emptyᵉ κ id now sched st =
  let (burst , sched₁) = oneShotBurst [] id sched
  in burst , sched₁ , st

subscribeE (mapᵉ f b) κ id now sched st =
  let (burst , sched₁ , st₁) =
        subscribeE b (map-f f ↠ κ) id now sched st
  in pushBurst id now (map-f f) κ burst sched₁ st₁

subscribeE (takeᵉ count b) κ id now sched st with evalTm count
... | zero =
      -- take 0 never subscribes its source (as in rxjs): a spent
      -- one-shot, exactly emptyᵉ
      let (burst , sched₁) = oneShotBurst [] id sched
      in burst , sched₁ , st
... | suc k =
      let (nid , sched₁) = mintNode sched
          (burst , sched₂ , st₁) =
            subscribeE b (take-f nid ↠ κ) id now sched₁
                       (installNode nid (take-st (suc k)) st)
      in pushBurst id now (take-f nid) κ burst sched₂ st₁

subscribeE (scanᵉ f seed b) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE b (scan-f f nid ↠ κ) id now sched₁
                   (installNode nid (scan-st (evalTm seed)) st)
  in pushBurst id now (scan-f f nid) κ burst sched₂ st₁

subscribeE {u = u} (mergeAllᵉ lim b) κ id now sched st =
  subscribeAll mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b
               κ id now sched st
subscribeE (switchAllᵉ b) κ id now sched st =
  subscribeAll switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE (exhaustAllᵉ b) κ id now sched st =
  subscribeAll exhaustᵒ (exhaust-st false false) b κ id now sched st

-- one unfold per subscription; the recursive occurrences inside the
-- unfolding are deferᵉ-gated, so each re-entry costs a schedule hop —
-- no synchronous loop.  A non-structural edge: the unfolding is larger
-- than the μ, not a subterm — and the only one of the three whose fact
-- was already proven, since `Rx.Sync-Size.unfoldμ-shrinks` speaks of
-- the term rather than of anything the run was handed.
subscribeE (μᵉ body) κ id now sched st =
  subscribeE (unfoldμ body) κ id now sched st

subscribeE (varᵉ ()) κ id now sched st

-- deferᵉ is mergeAll of a one-shot scheduled outer: the body itself is
-- the pending payload (Val Γ (obs u) IS Closed Γ u), delivered at
-- suc now with isLast — the arrival's thru-outer frame subscribes it
-- under that arrival's fresh instant, wrap marks the outer done, and
-- the node completes when the body does.  Cancellation is free:
-- cutting the registration lets sweepLive collect the pending hop
subscribeE {u = u} (deferᵉ body) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (src , sched₂) = mintSource sched₁
      (ord , sched₃) = mintOrdinal sched₂
      sched₄ = record sched₃
        { live = record { source = src ; ordinal = ord
                        ; elemTy = obs u
                        ; pending = (suc now , body) ∷ [] }
                 ∷ Sched.live sched₃ }
  in ((init src ∷ []) at id from src as subscribe) ∷ [] , sched₄ ,
     register (atDyn src _) (thru-outer mergeAllᵒ nid ↠ κ)
              (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st)

-- delivery at a share boundary re-enters chain evaluation: foldPath
-- and dispatchShare are mutually recursive, and what falls across that
-- cycle is the DISTANCE FROM THE FLOOR TO THE TOP OF THE TELESCOPE.  A
-- chain indexed at floor `lo` sinks only into the root or a share whose
-- own index is at least `lo`, and the sink constructor carries that as
-- a premise; dispatching at share i re-enters at floor `suc (toℕ i)`,
-- which is strictly above `lo`, so `n ∸ lo` strictly falls.  The
-- accessibility on `_<_` at that quantity is what the three functions
-- recurse on.
--
-- SO THE ORDER IS THE TREE'S OWN AND NOT A STAND-IN FOR IT.  This edge
-- used to spend a counter seeded at the context size, whose clamp arm
-- was reachable in the TYPE and unreachable only on a registry
-- invariant no postulate carried — a bound asserted in prose at the
-- clause that fires when it fails, and nowhere else.  Indexing the path
-- by its floor turns that invariant into the sink constructor's
-- premise, so the descent is discharged by what the registry's rows
-- ARE rather than by a fact about what a run put in them, and the clamp
-- arm has no type to be written at.

-- THE DISPATCH STANDS AT THE CHAIN'S FLOOR AND PEELS TO THE FAN-OUT'S,
-- which is why the sink's own premise is an argument here.  A dependent
-- function type binds left to right, so a premise mentioning `i` cannot
-- precede it; everything else keeps the position the counter held.
dispatchShare : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Acc _<_ (n ∸ lo)  -- the descent, at the chain's own floor
              → Id → Tick → (i : Fin n) → lo ≤ toℕ i
              → List (Val Γ (lookup Γ i)) → Bool
              → Sched Γ → EvalSt e
              → Stream Γ t × Sched Γ × EvalSt e

-- a fan-out chain cancelled earlier in this cascade (an operator cut
-- named it a victim) delivers NOTHING — its close already rode the
-- cutting emit; the survivors are marked delivered as they fold.
-- Lifted out of dispatchShare's where block so the budget proof can
-- name it (as with takeVals / thruConsume / sharedConnect)
shareGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Acc _<_ (n ∸ lo) → Id → Tick → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e

-- one chain, ONE emit — plus, past a share boundary, the fan-out
-- emits it causes.  Fold the value list sinkward through the frames,
-- accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
foldPath : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Acc _<_ (n ∸ lo) → Id → Tick → Source → Path Γ lo u t
         → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
         → Sched Γ → EvalSt e
         → Stream Γ t × Sched Γ × EvalSt e
foldPath ac id now envSrc root vals evs fin sched st =
  ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    at id from envSrc as delivery) ∷ [] , sched , st
-- THE SINK HANDS ITS OWN PREMISE DOWN, and that premise is the whole
-- descent: the dispatch peels the witness by it rather than being
-- trusted to stay inside a count.
foldPath ac id now envSrc (share-sink i below) vals evs fin sched st =
  -- the chain's own (valueless) emit first — announcing the handoff:
  -- share i fans out next, still inside this instant.  The share
  -- delivers vals to every chain registered on it — the diamond
  -- case, batched by construction
  let (fanout , sched₁ , st₁) =
        dispatchShare ac id now i below vals fin sched st
  in (((evs ++ handoff (toℕ i) ∷ []) at id from envSrc as delivery) ∷ fanout)
     , sched₁ , st₁
foldPath ac id now envSrc (f ↠ path′) vals evs fin sched st =
  let (vals′ , evs′ , fin′ , sched₁ , st₁) =
        stepFrame id now f path′ vals fin sched st
  in foldPath ac id now envSrc path′ vals′ (evs ++ evs′) fin′ sched₁ st₁

-- deliver to the chains of share i, one emit per registration from
-- source toℕ i (the share's owed count), in subscription order.  A
-- completing def (fin) latches the share BEFORE the fan-out — as a
-- Subject closes before delivering its completion — so a subscriber
-- joining mid-dispatch already sees the one-shot close/complete and
-- never registers only to be dropped silently; then every snapshot
-- registration closes and the sweep collects whatever the share kept
-- alive
-- `shareAdmit` hands back rows indexed at `suc (toℕ i)`, so the witness
-- the fan-out is handed is this one peeled by the sink's own premise —
-- matched here rather than applied, since that is the only form the
-- termination checker reads as a descent.
dispatchShare (acc rs) id now i below vals fin sched st =
  shareFinish i fin
    (shareGo (rs (floorFalls i below)) id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))

shareGo ac id now i vals fin []               sched₀ st₀ = [] , sched₀ , st₀
shareGo ac id now i vals fin ((rid , p) ∷ ps) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true  = shareGo ac id now i vals fin ps sched₀ st₀
... | false =
  let (emits , sched₁ , st₁) =
        foldPath ac id now (toℕ i) p vals
                 (if fin then close (toℕ i) exhausted ∷ [] else [])
                 fin sched₀
                 (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      (rest , sched₂ , st₂) = shareGo ac id now i vals fin ps sched₁ st₁
  in emits ++ rest , sched₂ , st₂

-- seed one arrival into one chain: the value, plus fin and this
-- registration's close when the source is spent (isLast)
chainStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Id → (a : Arrival Γ) → AtFloor Γ (arrTy a) t → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
chainStep {n = n} {e = e} id a (lo , path) sched st =
  foldPath (<-wellFounded-fast (n ∸ lo))
           id (arrTick a) (arrSource a) path (arrVal a ∷ [])
           (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
           (Arrival.isLast a) sched st

-- fold the snapshot chains.  A chain cancelled earlier in this same
-- cascade (an operator cut named it a victim) delivers NOTHING — as
-- in rxjs, where the unsubscribed branch of take(1)(merge(s,s)) is
-- silent; its close (cut or cutPending) already rode the cutting emit
cascadeGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → (a : Arrival Γ) → Id
          → List (RegId × AtFloor Γ (arrTy a) t) → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
cascadeGo a id []                   sched₀ st₀ = [] , sched₀ , st₀
cascadeGo a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true  = cascadeGo a id chains sched₀ st₀
... | false =
  let (emits , sched₁ , st₁) =
        chainStep id a c sched₀
                  (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      (rest  , sched₂ , st₂) = cascadeGo a id chains sched₁ st₁
  in emits ++ rest , sched₂ , st₂

cascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Arrival Γ → Id → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e
cascade a id sched st =
  let (emits , sched′ , st′) =
        cascadeGo a id (chainsOf a st) sched (cascadeLatch a st)
      (sched″ , st″) = cascadeFinish a sched′ st′
  in emits , sched″ , st″

-- fuel = ARRIVALS PROCESSED; each arrival's cascade runs to
-- quiescence (never truncated mid-batch).  The root subscription's
-- burst is free: fuel 0 still yields it.
-- fuel-many arrivals, each cascading to quiescence.  Top level (not a
-- where-local of evaluate) so Verify-Well-Formed can induct on it.
-- Instant ids mint from ARRIVAL POSITION (the counter threaded here):
-- structural distinctness, strictly increasing along the stream.
drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → Fuel → Id → Sched Γ → EvalSt e → Stream Γ t
drain zero    _      _     _  = []            -- out of fuel: truncate (only here)
drain (suc k) nextId sched st with sched-next sched
... | inj₁ _            = []                  -- schedule empty: program done
... | inj₂ (a , sched′) =
  let (out , sched″ , st′) = cascade a nextId sched′ st
  in out ++ drain k (suc nextId) sched″ st′

-- THE FUEL IS AN ARRIVAL ALLOWANCE AND NOTHING ELSE.  It bounds how
-- many arrivals `drain` will serve; the rank a subscription descends on
-- is read off the term, so no reading anywhere is relative to it.  The
-- two quantities were once one field, and they are not the same
-- quantity: `drain` spends one unit per ARRIVAL while a fold refolds
-- per DELIVERY, so a cascade delivering entirely inside one subscribe
-- frame refolds as often as its source is long against no fuel at all.
-- AND THE ROOT'S FLOOR IS THE CONTEXT SIZE, which is where the whole
-- stratification enters and where it costs nothing.  A closed term's
-- inputs are drawn from `Fin n`, so every one of them is below `n` by
-- construction; and the root path sinks into no share at all, so it
-- meets the floor vacuously.  Everything below descends from here.
--
-- AND THE ROOT NO LONGER SEEDS A RANK, WHICH IS THE WHOLE OF THE DIFF
-- AT THE TOP LINE.  The type is unchanged, so the oracle, the bug cache
-- and every protocol theorem above see nothing — which is the test that
-- the descent was never part of the semantics.  What it costs is that
-- this definition is not accepted on its own: the three edges below
-- descend on facts stated in `Rx.Evaluator.Doorless` and spent in
-- `Verify-Rank-Sufficient.Doorless`, and no pragma may stand in for
-- them here.
evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → Stream Γ t
evaluate {n = n} fuel e ins =
  let (burst , sched₀ , st₀) =
        subscribeE {lo = n} e root 0 0 (sched-init e ins)
          (st-init e)
  in burst ++ drain fuel 1 sched₀ st₀
