------------------------------------------------------------------
-- THE BUILDER: WHERE THE ARITHMETIC GOES ONCE THE MACHINE STOPS DOING
-- IT.
------------------------------------------------------------------

-- WHAT A BUILDER IS, AND WHY IT IS NOT THE TOTALITY PROOF NEXT DOOR.
-- That one builds a derivation at `subscribeE`'s OWN RESULT, so it has
-- to follow the machine into the test and answer the negative arm with
-- `⊥-elim` — an arm proven unreachable, writeable only where the fact
-- happens to be in hand.  Here the result is not fixed by a machine:
-- the builder RETURNS the pair, so it chooses which clause ran, and a
-- clause it does not write is a run that does not exist.  The `⊥-elim`
-- has nothing to eliminate because the `with` is gone.
--
-- SO THE EVALUATOR IS A PROJECTION.  It is `proj₁` of this, and every
-- reading of a rank, every `<?`, every `dryBurst` and the marker `dried`
-- itself have left the evaluator entirely.  `hasDry` reads `false` of
-- every run because no constructor of the relation builds a dry emit —
-- not because a number came out large enough.
--
-- AND A PROJECTION COMPUTES ONLY IF THE THING PROJECTED IS A REAL BODY,
-- WHICH IS WHAT THE EVALUATOR IS CURRENTLY TRADING.  While any leaf
-- below is a postulate the run typechecks and does not reduce, so the
-- bug cache, the oracle and every `refl` over a run are stuck at the
-- first match — which is why the cache is off the gate and the corpus is
-- a target to type rather than one the gate types for you.  Nothing
-- about the claim changes: what is owed is the leaves.
--
-- WHY IT SITS BELOW THE MACHINE RATHER THAN BESIDE THE PROOF THAT
-- CONSUMES IT.  Nothing here needs the recursion it replaces, and the
-- recursion does not compile — so a builder placed above it inherits a
-- cone the dev loop cannot warm and stops being iterable at exactly the
-- point where it is being written.  Below, the cone is `Rx.Evaluator`,
-- `Rx.Evaluator.Domain` and `Rx.Evaluator.Doorless`, all of which check
-- in seconds.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; head to headᵃ; tail to tailᵃ)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; _≡ᵇ_; _<?_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; ≮⇒≥; ∸-monoʳ-<)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Fuel; Id; Source; Tick; InstEmit; InstEvent; close;
  exhausted; hot; cold)
open import Rx.Exp using (Ctx; Closed; Val; _≟ᵗ_; obs; unfoldμ; evalTm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Slot-Depth using (slotDepth)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId; NodeState; Frame; root; _↠_; map-f; take-f; scan-f;
  thru-outer; from-inner; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; take-st;
  scan-st; installNode; lookupNode; setNode; hasRoom; switchKill; aliveThroughᶠ; splitEvents; splitBurst; sched-init; st-init;
  unconn; memberSource; share-sink; lowerFloor; register; atSlot; burstCompleted;
  Arrival; arrTick; arrSource; arrTy; arrVal; AtFloor; RegId; chainsOf;
  cascadeLatch; sched-next; shareAdmit; shareLatch)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  stepFrame⇓; innerReact⇓; innerFinish⇓; mergeAllDrain⇓; thruWalk⇓;
  thruConsume⇓; subscribeInner⇓;
  finish-all-drain; finish-switch-clear;
  finish-exhaust-clear; finish-nil; react-false; react-alive; react-dead;
  push-nil; push-cons; step-map; step-scan;
  step-scan-nil; step-take; step-from-inner; step-thru-outer;
  walk-nil; walk-cons; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil; inner;
  foldPath⇓; shareGo⇓; dispatchShare⇓; chainStep⇓; cascadeGo⇓; cascade⇓;
  fold-root; fold-sink; fold-step; go-nil; go-cut; go-live; disp;
  chain-step; casc-nil; casc-cut; casc-live; casc-run;
  drain-done; drain-empty; drain-step;
  drain-nil; drain-no-room; drain-room;
  drain⇓; evaluate⇓; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; sub-all; eval-run;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; slot-spent; slot-join; slot-connect; connect-live;
  connect-died)
open import Rx.Evaluator.Burst-Report using (burst-carries; depᵛˢ; handed-below)
open import Rx.Evaluator.Doorless using (μ-edge; μ-entry; rootWitness;
  EntryOK; SharesUnder; inner-ok; under-ok; HandedOK; BurstOK; split-handed;
  hop-edge; hop-guard; connect-edge; connect-entry)

------------------------------------------------------------------
-- WHAT A BUILDER RETURNS.  The result and the derivation together, so
-- that "which clause ran" is an output rather than something the
-- builder has to agree with.
------------------------------------------------------------------

Runs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
     → Closed Γ u → Path Γ lo u t → Id → Tick → Sched Γ → EvalSt e → Set
Runs {e = e} b κ id now sched st =
  ∃ λ r → subscribeE⇓ {e = e} b κ id now sched st r

PushRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
         → Id → Tick → Frame Γ s u → Path Γ lo u t
         → Stream Γ s → Sched Γ → EvalSt e → Set
PushRuns {e = e} id now fr κ bs sched st =
  ∃ λ r → pushBurst⇓ {e = e} id now fr κ bs sched st r

AllRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
        → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ lo u t
        → Id → Tick → Sched Γ → EvalSt e → Set
AllRuns {e = e} op ns b κ id now sched st =
  ∃ λ r → subscribeAll⇓ {e = e} op ns b κ id now sched st r

StepRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
         → Id → Tick → Frame Γ s u → Path Γ lo u t
         → List (Val Γ s) → Bool → Sched Γ → EvalSt e → Set
StepRuns {e = e} id now fr κ vals fin sched st =
  ∃ λ r → stepFrame⇓ {e = e} id now fr κ vals fin sched st r

InnerRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
          → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
          → List (Val Γ s) → Sched Γ → EvalSt e → Bool → Set
InnerRuns {e = e} op allNid inst κ id now vals sched st fin =
  ∃ λ r → innerReact⇓ {e = e} op allNid inst κ id now vals sched st fin r

WalkRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
         → AllOp → NodeId → Path Γ lo u t → Id → Tick
         → List (Val Γ (obs u)) → Sched Γ → EvalSt e → Set
WalkRuns {e = e} op nid κ id now os sched st =
  ∃ λ r → thruWalk⇓ {e = e} op nid κ id now os sched st r

ConsumeRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
            → AllOp → NodeId → Path Γ lo u t → Id → Tick
            → Val Γ (obs u) → Sched Γ → EvalSt e → Set
ConsumeRuns {e = e} op nid κ id now o sched st =
  ∃ λ r → thruConsume⇓ {e = e} op nid κ id now o sched st r

InnerSubRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
             → AllOp → NodeId → Path Γ lo u t → Id → Tick
             → Val Γ (obs u) → Sched Γ → EvalSt e → Set
InnerSubRuns {e = e} op allNid κ id now o sched st =
  ∃ λ r → subscribeInner⇓ {e = e} op allNid κ id now o sched st r

FinishRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
           → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
           → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ) → Set
FinishRuns {e = e} op allNid inst κ id now vals sched st ns =
  ∃ λ r → innerFinish⇓ {e = e} op allNid inst κ id now vals sched st ns r

DrainsQ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
        → NodeId → Path Γ lo s t → Id → Tick
        → Maybe ℕ → ℕ → Bool → List (Closed Γ s) → Sched Γ → EvalSt e → Set
DrainsQ {e = e} allNid κ id now lim act od q sched st =
  ∃ λ r → mergeAllDrain⇓ {e = e} allNid κ id now lim act od q sched st r

------------------------------------------------------------------
-- WHAT A RUN DOES NOT TOUCH.
------------------------------------------------------------------

-- THE TELESCOPE IS WRITTEN ONCE AND NEVER AGAIN, which is what lets the
-- entry invariant be denominated in ONE environment from the root to the
-- deepest hop.  `sched-init` sets it; every schedule the machine builds
-- afterwards is a record update over the fields a step genuinely moves,
-- so the reading is a constant of the run and the builder carries its
-- premises rather than transporting them at each call.  Stated the other
-- way round the premises would move with the schedule and every
-- recursive call would owe a `subst`, which is the same fact paid for
-- once per call site instead of once.
--
-- THREE STATEMENTS AND NOT THE WHOLE FAMILY, because these name the
-- three places a builder clause is handed a schedule some OTHER clause
-- built: the burst's producer, the frame step inside the push cycle, and
-- the consume inside the walk.  Everywhere else the schedule is this
-- clause's own record update, where the equation holds definitionally.
--
-- DEAD ROUTE: proving each of the three as an induction over the ⇓
--   family, which is how all three are stated.  It is dead structurally
--   rather than by being long: the family's mutual block is the
--   builder's own, so the induction has to re-walk every clause of a
--   recursion whose accessibility argument it does not carry, and the
--   equation it would establish at each step is one that clause ALREADY
--   holds.  The repair is to widen what a builder RETURNS, which closes
--   all three at once and leaves the obligation on the two leaves that
--   hand back a schedule nothing here built.
postulate
  subs-keeps-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched

  step-keeps-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
    {vals : List (Val Γ s)} {fin : Bool} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    stepFrame⇓ {e = e} id now fr κ vals fin sched st
      (vals′ , evs , fin′ , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched

  consume-keeps-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (vals′ , evs , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched

-- AND THE SAME THREE SITES OWE THE OTHER AGREEMENT, WHICH IS THE ONE
-- THE CONNECT'S EDGE READS.  A clause handing a LATER state onward is
-- standing at the triple it entered with, so what it must re-establish
-- is that the later state's unconnected count still sits under that
-- triple — and it does, because the connected set only ever GAINS an
-- index: no clause of any family removes one, so the count is
-- monotone down the run and the gap the caller was handed only widens.
-- Stated at an arbitrary slot table rather than at the run's own,
-- because the table is what the count is denominated in and every
-- consumer already holds the agreement fixing it.
--
-- AND IT IS THREE STATEMENTS RATHER THAN ONE OVER THE STORE, WHICH IS
-- FORCED BY WHERE THE STATES COME FROM.  Each is a claim about what a
-- DERIVATION produced, so it is stated over the ⇓ family whose clause
-- produced it; a single claim about `EvalSt` would have to quantify
-- over states no run reaches, which is the shape three refutations on
-- this face have already killed.
postulate
  subs-unconn-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)

  step-unconn-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
    {vals : List (Val Γ s)} {fin : Bool} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    stepFrame⇓ {e = e} id now fr κ vals fin sched st
      (vals′ , evs , fin′ , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)

  consume-unconn-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))}
    {sched′ : Sched Γ} {st′ : EvalSt e} (sl : Slots Γ) →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (vals′ , evs , sched′ , st′) →
    unconn sl (EvalSt.connectedShares st′)
      ≤ unconn sl (EvalSt.connectedShares st)

-- THE SWITCH'S KILL IS THE ONE OF THE FOUR THAT IS NOT A RELATION, so it
-- is a function and the fact is two clauses of `refl`.  It is stated
-- over the whole triple rather than over a named schedule because the
-- consume clause reaches it through a `with … in`, which hands back the
-- equation at the tuple the pattern bound.
switchKill-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) {res} →
  switchKill cur sched st ≡ res →
  Sched.slots (proj₁ (proj₂ res)) ≡ Sched.slots sched
switchKill-slots nothing  sched st refl = refl
switchKill-slots (just v) sched st refl = refl

-- and its share set, which it does not touch at all: the kill closes an
-- inner and drops a registration, so the count is the same number and
-- the agreement passes through by `≤-refl` under the same two clauses.
switchKill-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) {res} →
  switchKill cur sched st ≡ res →
  unconn sl (EvalSt.connectedShares (proj₂ (proj₂ res)))
    ≤ unconn sl (EvalSt.connectedShares st)
switchKill-unconn sl nothing  sched st refl = ≤-refl
switchKill-unconn sl (just v) sched st refl = ≤-refl

-- AND THE AGREEMENT READ AT ONE INDEX.  Every builder is handed the
-- table as a premise so its measure is denominated in a constant, while
-- the relation's slot arms speak of the schedule's own table; at a
-- single index the two are the same reading, and this is that step.  It
-- exists because the arms below select on `sl i`, which is what
-- `connect-entry` wants, and then owe the constructor a statement about
-- `Sched.slots sched i`, which is what the relation wants.
slot-agree : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (sched : Sched Γ) (i : Fin n)
           → Sched.slots sched ≡ sl
           → ∀ {s} → sl i ≡ s → Sched.slots sched i ≡ s
slot-agree sl sched i ag eq = trans (cong (λ f → f i) ag) eq

------------------------------------------------------------------
-- THE CYCLE ITSELF, WHICH IS ONE BLOCK BECAUSE THE HOP CLOSES IT.
------------------------------------------------------------------

-- SEVEN SIGNATURES BEFORE ANY BODY, AND THE ONE THAT FORCES IT IS THE
-- HOP.  Every other member descends on a term or shortens a list with τ
-- held fixed, so on its own each would be an ordinary structural
-- recursion; the hop takes a runtime observable out of a burst and
-- subscribes it, which re-enters the subscribe at a τ the accessibility
-- has to pay for.  That is the single strict descent in the block, and
-- it is why the entry invariant is not enough on its own — what arrives
-- at the hop is a VALUE, so `EntryOK` says nothing about it and the
-- report `HandedOK` threads from the burst that produced it does.
--
-- AND THE DESCENT IS DECLARED STRUCTURAL RATHER THAN PEELED, WHICH IS
-- WHAT THE DOORLESS SHAPE BOUGHT.  The predecessor carried a counter
-- Agda could not read, so which edges paid for the recursion was a
-- claim only a declaration held; here the accessibility witness is an
-- ARGUMENT, so every member descends on something it already carries
-- and Agda checks that at each call site rather than taking this line's
-- word for it.  The line stays because a future edge re-entering the
-- block from outside would still be a site the order does not cover.
--
-- STRUCTURAL SCC: pushBurst! stepFrame! subscribeAll! subscribeE! subscribeE!-input subscribeInner! thruConsume! thruWalk!

-- THE FRAME A SUBSCRIBE CAN PUSH, WHICH IS EVERY FRAME BUT ONE, AND
-- SAYING SO IN A TYPE IS WHAT TAKES THE DRAIN OUT OF THIS BLOCK.  A
-- push cycle steps the frame it was handed, and what hands it one is a
-- source former -- the map, the take, the scan, the outer of an
-- operator.  The inner's own frame is never pushed: a subscribe returns
-- the inner's synchronous burst UP to its caller as values, and the
-- frame is walked later, by the instant loop, down a path the registry
-- holds.  So the completion side -- react, finish, drain, and the
-- queued subscribe they end in -- is not reachable from a subscribe at
-- all, and the cycle that a measure was owed for does not exist.  What
-- did exist was a DEFINITION order: this block had to answer for a
-- frame it can never be given, and answering cost it the drain.
srcFrame : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
srcFrame (from-inner _ _ _) = ⊥
srcFrame _                  = ⊤

subscribeE! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (b : Closed Γ u) → EntryOK (slotDepth sl) b τ →
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  Runs {e = e} b κ id now sched st

subscribeE!-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (i : Fin n) →
  EntryOK {Γ = Γ} (slotDepth sl) (input i) τ →
  (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  Runs {e = e} (input i) κ id now sched st

subscribeAll! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) →
  EntryOK (slotDepth sl) b τ → (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  AllRuns {e = e} op ns b κ id now sched st

pushBurst! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  → srcFrame fr →
  (κ : Path Γ lo u t) (bs : Stream Γ s) → BurstOK (slotDepth sl) bs τ →
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  PushRuns {e = e} id now fr κ bs sched st

stepFrame! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  → srcFrame fr →
  (κ : Path Γ lo u t) (vals : List (Val Γ s)) → HandedOK (slotDepth sl) vals τ →
  (fin : Bool) (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  StepRuns {e = e} id now fr κ vals fin sched st

thruWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u))) →
  HandedOK (slotDepth sl) os τ →
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  WalkRuns {e = e} op nid κ id now os sched st

thruConsume! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) →
  HandedOK (slotDepth sl) (o ∷ []) τ →
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  ConsumeRuns {e = e} op nid κ id now o sched st

subscribeInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) →
  HandedOK (slotDepth sl) (o ∷ []) τ →
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  InnerSubRuns {e = e} op allNid κ id now o sched st

-- EVERY OPERATOR CLAUSE DESCENDS ON THE TERM AND CARRIES THE SAME τ,
-- so the accessibility is passed through untouched and only the entry
-- invariant has to travel.  `inner-ok` and `under-ok` are that
-- travelling: the two measures read an operator as `suc (template +
-- source)` and `template ⊔ source` respectively, and what the source
-- needs is the right half of each.  The one clause that moves τ is the
-- μ peel below, and it is the only place a witness is spent on a TERM.
subscribeE! ac sl (input i) ok κ id now sched ag st ub =
  subscribeE!-input ac sl i ok κ id now sched ag st ub
subscribeE! ac sl (ofᵉ ts)  ok κ id now sched ag st ub = _ , subs-of refl
subscribeE! ac sl emptyᵉ    ok κ id now sched ag st ub = _ , subs-empty refl

subscribeE! ac sl (mapᵉ f b) ok κ id now sched ag st ub =
  let ((burst , sched₁ , st₁) , d) =
        subscribeE! ac sl b (inner-ok ok) (map-f f ↠ κ) id now sched ag st ub
      (r , p) = pushBurst! ac sl id now (map-f f) tt κ burst
                  (burst-carries sl (inner-ok ok) d) sched₁
                  (trans (subs-keeps-slots d) ag) st₁
                  (≤-trans (subs-unconn-drops sl d) ub)
  in r , subs-map d p

subscribeE! ac sl (takeᵉ c b) ok κ id now sched ag st ub
  with evalTm c in eq
... | zero  = _ , subs-take-zero eq refl
... | suc k =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac sl b (inner-ok ok) (take-f nid ↠ κ) id now
                    (record sched { nextNode = suc nid }) ag
                    (installNode nid (take-st (suc k)) st) ub
      (r , p) = pushBurst! ac sl id now (take-f nid) tt κ burst
                  (burst-carries sl (inner-ok ok) d) sched₂
                  (trans (subs-keeps-slots d) ag) st₁
                  (≤-trans (subs-unconn-drops sl d) ub)
  in r , subs-take-suc eq refl d p

subscribeE! ac sl (scanᵉ f z b) ok κ id now sched ag st ub =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac sl b (inner-ok ok) (scan-f f nid ↠ κ) id now
                    (record sched { nextNode = suc nid }) ag
                    (installNode nid (scan-st (evalTm z)) st) ub
      (r , p) = pushBurst! ac sl id now (scan-f f nid) tt κ burst
                  (burst-carries sl (inner-ok ok) d) sched₂
                  (trans (subs-keeps-slots d) ag) st₁
                  (≤-trans (subs-unconn-drops sl d) ub)
  in r , subs-scan refl d p

subscribeE! ac sl (mergeAllᵉ lim b) ok κ id now sched ag st ub =
  let (r , a) = subscribeAll! ac sl mergeAllᵒ (mergeAll-st lim 0 [] false)
                              b (under-ok ok) κ id now sched ag st ub
  in r , subs-merge-all a
subscribeE! ac sl (switchAllᵉ b) ok κ id now sched ag st ub =
  let (r , a) = subscribeAll! ac sl switchᵒ (switch-st nothing false)
                              b (under-ok ok) κ id now sched ag st ub
  in r , subs-switch-all a
subscribeE! ac sl (exhaustAllᵉ b) ok κ id now sched ag st ub =
  let (r , a) = subscribeAll! ac sl exhaustᵒ (exhaust-st false false)
                              b (under-ok ok) κ id now sched ag st ub
  in r , subs-exhaust-all a

-- THE μ PEEL.  Against the machine the deletion is the whole clause's
-- `with`: `unfoldμ-shrinks` is a fact about the term and needs no
-- number handed in, so `μ-edge` is the descent outright.  The entry
-- invariant travels with it through `μ-entry`, which is the same
-- composition the old totality proof wrote under `⊥-elim`.
subscribeE! (acc rec) sl (μᵉ body) (sz≤ , r≤) κ id now sched ag st ub =
  let (r , d) = subscribeE! (rec (μ-edge (slotDepth sl) body sz≤ r≤)) sl
                            (unfoldμ body)
                            (≤-refl , μ-entry (slotDepth sl) body r≤)
                            κ id now sched ag st ub
  in r , subs-μ d

subscribeE! ac sl (varᵉ ()) ok κ id now sched ag st ub
subscribeE! ac sl (deferᵉ body) ok κ id now sched ag st ub = _ , subs-defer refl refl refl

-- THE FLATTENER'S OUTER SUBSCRIBE, WHICH HAS EXACTLY ONE CLAUSE.  All
-- three `*All` operators install their own node state and then run the
-- same outer subscribe through a `thru-outer` frame, so the operator is
-- carried as a value and the shape is shared.
subscribeAll! ac sl op ns b ok κ id now sched ag st ub =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac sl b ok (thru-outer op nid ↠ κ) id now
                    (record sched { nextNode = suc nid }) ag
                    (installNode nid ns st) ub
      (r , p) = pushBurst! ac sl id now (thru-outer op nid) tt κ burst
                  (burst-carries sl ok d) sched₂
                  (trans (subs-keeps-slots d) ag) st₁
                  (≤-trans (subs-unconn-drops sl d) ub)
  in r , sub-all refl d p

-- THE PUSH CYCLE SPLITS THE REPORT EXACTLY WHERE IT SPLITS THE BURST.
-- One emit is stepped per iteration and the frame is handed that emit's
-- own values, so the `All` over the burst peels into the head's events
-- and the tail's emits, and `split-handed` carries the head across the
-- splitter at whatever retag type the frame pins.
--
-- AND IT PEELS BY PROJECTION RATHER THAN BY PATTERN, WHICH IS WHAT KEEPS
-- THE REPORT OFF THE COMPUTATIONAL PATH.  A clause selected on the `All`
-- is a clause that cannot fire while the report is a postulate, and the
-- report's own leaf is the last thing in this module that will become a
-- body — so matching it here would hold the whole cutover hostage to a
-- proof obligation the run does not need.  Projected instead, a stuck
-- report reaches only `ltR`, which is a constructor, and the skipping
-- accessibility witness underneath reads nothing, so every clause on
-- both routes to the hop still reduces at a concrete program.  The same
-- rule binds the walk below, and every carried premise added after.
pushBurst! ac sl id now fr sv κ []         bk sched ag st ub = _ , push-nil
pushBurst! ac sl id now fr sv κ (em ∷ ems) bk sched ag st ub =
  let sp = splitEvents (InstEmit.events em)
      ((vals′ , evs , fin′ , sched₁ , st₁) , sf) =
        stepFrame! ac sl id now fr sv κ (proj₁ sp)
          (split-handed (slotDepth sl) (InstEmit.events em) (headᵃ bk))
          (proj₂ (proj₂ sp)) sched ag st ub
      (_ , pb) = pushBurst! ac sl id now fr sv κ ems (tailᵃ bk) sched₁
                   (trans (step-keeps-slots sf) ag) st₁
                   (≤-trans (step-unconn-drops sl sf) ub)
  in _ , push-cons refl sf pb

-- THE SCAN CLAUSE IS THE ONLY ONE THAT LOOKS AT THE STORE, AND THE
-- RELATION SAYS WHAT TO DO WHEN THE READING DISAGREES.  A node table
-- carries its accumulator's type existentially, so the frame's own `u`
-- has to be decided against what is installed; every answer but `yes`
-- takes the nil clause, which is the same collapse the machine reaches
-- by its `dispatch`.  Nothing is owed here — the relation offers a
-- constructor at every reading, so the builder chooses rather than
-- having to prove a branch unreachable.
stepFrame! ac sl id now (map-f fn) sv κ vals hk fin sched ag st ub = _ , step-map
stepFrame! ac sl id now (take-f nid) sv κ vals hk fin sched ag st ub = _ , step-take

stepFrame! {u = u} ac sl id now (scan-f fn nid) sv κ vals hk fin sched ag st ub
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , step-scan-nil
... | just (take-st _)           = _ , step-scan-nil
... | just (mergeAll-st _ _ _ _) = _ , step-scan-nil
... | just (switch-st _ _)       = _ , step-scan-nil
... | just (exhaust-st _ _)      = _ , step-scan-nil
... | just (scan-st {w} a)       with w ≟ᵗ u
...   | no  _    = _ , step-scan-nil
...   | yes refl = _ , step-scan eq refl

stepFrame! ac sl id now (from-inner op allNid inst) () κ vals hk fin sched ag st ub

stepFrame! ac sl id now (thru-outer op nid) sv κ vals hk fin sched ag st ub =
  let ((vs , bs , sched′ , st′) , w) =
        thruWalk! ac sl op nid κ id now vals hk sched ag st ub
  in _ , step-thru-outer w

thruWalk! ac sl op nid κ id now []       hk sched ag st ub = _ , walk-nil
thruWalk! ac sl op nid κ id now (o ∷ os) hk sched ag st ub =
  let ((vs , bs , sched₁ , st₁) , c) =
        thruConsume! ac sl op nid κ id now o (headᵃ hk ∷ᵃ []ᵃ) sched ag st ub
      (_ , w) = thruWalk! ac sl op nid κ id now os (tailᵃ hk) sched₁
                  (trans (consume-keeps-slots c) ag) st₁
                  (≤-trans (consume-unconn-drops sl c) ub)
  in _ , walk-cons c w

-- WHAT A CONSUME CLAUSE DECIDES IS WHETHER THE OBSERVABLE IS TAKEN AT
-- ALL, AND EVERY OPERATOR ANSWERS IT OFF THE STORE.  A merge takes it
-- when the lane count leaves room and queues it otherwise, a switch
-- always takes it and kills whatever was running first, an exhaust
-- takes it only while nothing is running.  Every other reading of the
-- node — the wrong operator's state, the wrong accumulator type, no
-- node at all — collapses to the operator's own nil clause, which is
-- the same collapse the machine reaches through its catch-all.
thruConsume! {u = u} ac sl mergeAllᵒ nid κ id now o hk sched ag st ub
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing              = _ , consume-all-nil
... | just (scan-st _)     = _ , consume-all-nil
... | just (take-st _)     = _ , consume-all-nil
... | just (switch-st _ _) = _ , consume-all-nil
... | just (exhaust-st _ _) = _ , consume-all-nil
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no  _    = _ , consume-all-nil
...   | yes refl with hasRoom lim act in eqr
...     | false = _ , consume-all-enqueue eq eqr
...     | true  =
          let (_ , i) = subscribeInner! ac sl mergeAllᵒ nid κ id now o hk
                          sched ag st ub
          in _ , consume-all-sub eq eqr i

thruConsume! ac sl switchᵒ nid κ id now o hk sched ag st ub
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-switch-nil
... | just (scan-st _)           = _ , consume-switch-nil
... | just (take-st _)           = _ , consume-switch-nil
... | just (mergeAll-st _ _ _ _) = _ , consume-switch-nil
... | just (exhaust-st _ _)      = _ , consume-switch-nil
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (closes , sched₁ , st₁) =
        let (_ , i) = subscribeInner! ac sl switchᵒ nid κ id now o hk sched₁
                        (trans (switchKill-slots cur sched st eqk) ag) st₁
                        (≤-trans (switchKill-unconn sl cur sched st eqk) ub)
        in _ , consume-switch-sub eq eqk i

thruConsume! ac sl exhaustᵒ nid κ id now o hk sched ag st ub
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-exhaust-nil
... | just (scan-st _)           = _ , consume-exhaust-nil
... | just (take-st _)           = _ , consume-exhaust-nil
... | just (mergeAll-st _ _ _ _) = _ , consume-exhaust-nil
... | just (switch-st _ _)       = _ , consume-exhaust-nil
... | just (exhaust-st true _)   = _ , consume-exhaust-nil
... | just (exhaust-st false od) =
      let (_ , i) = subscribeInner! ac sl exhaustᵒ nid κ id now o hk sched ag st ub
      in _ , consume-exhaust-sub eq i

-- THE HOP, WHICH IS WHERE THE DELETED DOOR USED TO ASK ITS QUESTION AND
-- WHERE THE ANSWER NOW ARRIVES INSTEAD.  The machine tested the handed
-- observable's depth against the rank it was holding and emitted a dry
-- close down the negative arm; here there is no arm to take, because the
-- report that came with the value already says the drop holds.
-- `hop-guard` reads it out and `hop-edge` turns it into the descent, so
-- the recursive subscribe re-enters at the observable's own rank with
-- `≤-refl` on both halves of the entry invariant.
subscribeInner! {τ = τ} (acc rec) sl op allNid κ id now o hk sched ag st ub =
  let inst = Sched.nextNode sched
      ((burst , sched′ , st′) , d) =
        subscribeE! (rec (hop-edge (slotDepth sl) o
                           (hop-guard (slotDepth sl) τ o hk)))
                    sl o (≤-refl , ≤-refl)
                    (from-inner op allNid inst ↠ κ) id now
                    (record sched { nextNode = suc inst }) ag st ub
      (vs , bs , done) = splitBurst burst
  in (inst , vs , bs , done , sched′ , st′) , inner refl d refl

-- THE SLOT TABLE'S SIX ARMS, AND THE ONE OF THEM THAT RECURSES — WHICH
-- IS WHY THIS SITS IN THE CYCLE RATHER THAN BESIDE IT.  Five arms read
-- the table and hand back a burst the relation already names, so they
-- are the agreement transported and a constructor; the sixth CONNECTS a
-- share, and connecting subscribes the slot's own definition, which is
-- an arbitrary term.  That is the edge no term measure can pay for, so
-- it is paid in the count instead: the connected set gains this index,
-- the unconnected count strictly falls, and `ltU` is the drop.
--
-- AND THE RECURSIVE CALL RE-ENTERS AT THE SLOT'S OWN READING RATHER
-- THAN AT THE CALLER'S.  `connect-entry` supplies both halves — the
-- size is the definition's own and the rank is the fixpoint's value at
-- this index — so the triple is rebuilt here and only its first
-- component is tied to what came in.  The share agreement goes back to
-- `≤-refl` for the same reason: the new triple's count IS the state's,
-- since the state handed down is the one that just gained the index.
subscribeE!-input {lo = lo} ac sl i ok κ id now sched ag st ub
  with toℕ i <? lo
... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below)
... | yes below  with sl i in slEq
...   | scripted (hot async)
        with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
...     | true  = _ , subs-hot-done below (slot-agree sl sched i ag slEq) doneEq
...     | false = _ , subs-hot-live below (slot-agree sl sched i ag slEq) doneEq
subscribeE!-input {lo = lo} ac sl i ok κ id now sched ag st ub
    | yes below | scripted (cold sync []) =
      _ , subs-cold-sync below (slot-agree sl sched i ag slEq) refl
subscribeE!-input {lo = lo} ac sl i ok κ id now sched ag st ub
    | yes below | scripted (cold sync (d ∷ ds)) =
      _ , subs-cold-async below (slot-agree sl sched i ag slEq) refl refl
subscribeE!-input {lo = lo} (acc rec) sl i ok κ id now sched ag st ub
    | yes below | shared d
        with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
...     | true  =
          _ , subs-shared {κ = κ} {below = below} (slot-agree sl sched i ag slEq)
                (slot-spent {κ = κ} {below = below} doneEq)
...     | false
          with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
...       | true  =
            _ , subs-shared {κ = κ} {below = below}
                  (slot-agree sl sched i ag slEq)
                  (slot-join {κ = κ} {below = below} doneEq connEq)
...       | false
            with subscribeE!
                   (rec (connect-edge sl (EvalSt.connectedShares st) i connEq ub))
                   sl d
                   (connect-entry
                     {U = unconn sl (toℕ i ∷ EvalSt.connectedShares st)}
                     sl i slEq)
                   (share-sink i ≤-refl) id now
                   sched ag
                   (register (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                   ≤-refl
...         | ((burst , sched₁ , st₂) , dv) with burstCompleted burst in compEq
...           | false =
                _ , subs-shared {κ = κ} {below = below}
                      (slot-agree sl sched i ag slEq)
                      (slot-connect doneEq connEq
                        (connect-live {κ = κ} {below = below} dv compEq))
...           | true  =
                _ , subs-shared {κ = κ} {below = below}
                      (slot-agree sl sched i ag slEq)
                      (slot-connect doneEq connEq
                        (connect-died {κ = κ} {below = below} dv compEq))

------------------------------------------------------------------
-- THE COMPLETION SIDE, WHICH THE CYCLE ABOVE CANNOT REACH.
------------------------------------------------------------------

-- THE QUEUED SUBSCRIBE IS AN ENTRY, SO IT NAMES ITS OWN RANK AND OWES
-- THE ORDER NOTHING.  A value the store has been holding sits under
-- whatever rank stood when it was put there, and the hop chain below
-- has lowered that rank since -- so a drain cannot descend on the rank
-- in force, and for as long as this lived inside the subscribe cycle
-- that read as an edge the order still owed a component for.  It owes
-- none.  Nothing a subscribe does reaches a completion: the inner's
-- frame is never PUSHED, only walked later by the instant loop, which
-- is what `srcFrame` says in a type.  So the drain enters the way the
-- root and an arrival do, at a rank set one above the observable it is
-- handing on -- `handed-below` at a one-element list discharges that
-- outright, and the share count is the state's own, so `≤-refl` closes
-- the other half.
queuedInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  (allNid : NodeId) (κ : Path Γ lo s t) (id : Id) (now : Tick)
  (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  InnerSubRuns {e = e} mergeAllᵒ allNid κ id now o sched st
queuedInner! {s = s} allNid κ id now o sched st =
  let sl = Sched.slots sched
      r  = suc (depᵛˢ (slotDepth sl) (obs s) (o ∷ []))
  in subscribeInner!
       (≺-wellFounded ( unconn sl (EvalSt.connectedShares st) , r , 0 ))
       sl mergeAllᵒ allNid κ id now o
       (handed-below {U = unconn sl (EvalSt.connectedShares st)}
                     {r = r} {sz = 0}
                     (slotDepth sl) (obs s) (o ∷ []) ≤-refl)
       sched refl st ≤-refl

mergeAllDrain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  (allNid : NodeId) (κ : Path Γ lo s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  DrainsQ {e = e} allNid κ id now lim act od q sched st
mergeAllDrain! allNid κ id now lim act od []      sched st = _ , drain-nil
mergeAllDrain! allNid κ id now lim act od (o ∷ q) sched st
  with hasRoom lim act in eqr
... | false = _ , drain-no-room eqr
... | true  =
  let ((inst , vs , bs , done , sched₁ , st₁) , s) =
        queuedInner! allNid κ id now o sched
          (record st
             { nodes = setNode allNid (mergeAll-st lim act q od)
                 (EvalSt.nodes st) })
      (_ , d) = mergeAllDrain! allNid κ id now lim
                  (if done then act else suc act) od q sched₁ st₁
  in _ , drain-room eqr s d

-- A FIN ONLY COMPLETES AN INNER ONCE NOTHING UNDER ITS EXIT FRAME CAN
-- DELIVER AGAIN, so the reaction reads the registry before it reads
-- the node: a live registration through this instance absorbs the
-- completion and the frame reports unfinished.  Only when nothing is
-- left does the operator's own finish run, and only a merge's finish
-- subscribes anything — it drains the queue the lane limit had held
-- back, which is the second place a value becomes a subscription and
-- the one the cycle above does not reach.
innerFinish! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ lo s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  FinishRuns {e = e} op allNid inst κ id now vals sched st ns

innerFinish! {s = s} mergeAllᵒ allNid inst κ id now vals sched st
             (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | no  _    = _ , finish-nil
... | yes refl =
      let (_ , d) = mergeAllDrain! allNid κ id now lim (pred act) od q sched st
      in _ , finish-all-drain d
innerFinish! switchᵒ allNid inst κ id now vals sched st
             (just (switch-st (just c) od)) with (c ≡ᵇ inst) in eqc
... | true  = _ , finish-switch-clear eqc
... | false = _ , finish-nil
innerFinish! exhaustᵒ allNid inst κ id now vals sched st
             (just (exhaust-st act od)) = _ , finish-exhaust-clear
innerFinish! op allNid inst κ id now vals sched st ns = _ , finish-nil

innerReact! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ lo s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
  InnerRuns {e = e} op allNid inst κ id now vals sched st fin

innerReact! op allNid inst κ id now vals sched st false = _ , react-false
innerReact! op allNid inst κ id now vals sched st true
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = _ , react-alive eqa
... | false =
      let (_ , f) = innerFinish! op allNid inst κ id now vals sched st
                      (lookupNode allNid (EvalSt.nodes st))
      in _ , react-dead eqa f

-- THE FRAME STEP OVER EVERY FRAME, WHICH IS THE SUBSCRIBE CYCLE'S OWN
-- PLUS THE ONE IT CANNOT BE GIVEN.  The instant loop walks a path it
-- read out of the registry, so it meets `from-inner` and nothing
-- restricts what it meets; the cycle above meets the other four and
-- never this one.  Splitting the two is what lets the completion side
-- be defined down here at all, and the split is checked rather than
-- asserted: the `()` up there is Agda refusing the frame, not a
-- convention about which caller passes what.
stepFrameAny! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (vals : List (Val Γ s)) → HandedOK (slotDepth sl) vals τ →
  (fin : Bool) (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  SharesUnder sl τ st →
  StepRuns {e = e} id now fr κ vals fin sched st
stepFrameAny! ac sl id now (from-inner op allNid inst) κ vals hk fin sched ag st ub =
  let (_ , r) = innerReact! op allNid inst κ id now vals sched st fin
  in _ , step-from-inner r
stepFrameAny! ac sl id now (map-f fn) κ vals hk fin sched ag st ub =
  stepFrame! ac sl id now (map-f fn) tt κ vals hk fin sched ag st ub
stepFrameAny! ac sl id now (take-f nid) κ vals hk fin sched ag st ub =
  stepFrame! ac sl id now (take-f nid) tt κ vals hk fin sched ag st ub
stepFrameAny! ac sl id now (scan-f fn nid) κ vals hk fin sched ag st ub =
  stepFrame! ac sl id now (scan-f fn nid) tt κ vals hk fin sched ag st ub
stepFrameAny! ac sl id now (thru-outer op nid) κ vals hk fin sched ag st ub =
  stepFrame! ac sl id now (thru-outer op nid) tt κ vals hk fin sched ag st ub

------------------------------------------------------------------
-- THE ARRIVAL CYCLE, WHICH IS A SECOND ENTRY AND NOT A CONTINUATION.
------------------------------------------------------------------

-- EVERY BUILDER OF THE SUBSCRIBE BLOCK QUANTIFIES OVER THE RANK, SO A
-- SITE ENTERING FROM OUTSIDE NAMES ITS OWN AND PAYS ALL FOUR PREMISES
-- ITSELF.  The slot agreement is `refl` because the table is read off
-- the schedule handed in; the share bound is `≤-refl` because the count
-- IS the state's; the rank is set one above the values being handed, so
-- `handed-below` discharges it outright; and the accessibility comes
-- from the order's own well-foundedness.  Nothing is carried in and no
-- field is owed — only a site INSIDE the descent is denied this, because
-- there the rank is the quantity the recursion is spending.
--
-- AND THE CYCLE'S OWN DESCENT IS THE FLOOR INDEX, READ OFF `share-sink`'s
-- ARGUMENT.  A chain registered on a share sinks STRICTLY above that
-- share, so the room left above the floor is what shrinks at every
-- fan-out and the term itself never has to.
--
-- RECOVERY: git show 80e527f9:agda/src/Rx/Evaluator/Run.agda restores the
--   predecessor's own `drain`, whose three arms over the schedule are the
--   shape the far end takes; what does not transport is the guard it
--   tested, since that obligation is now the derivation's.

monus-sink : ∀ {n lo} (i : Fin n) → lo ≤ toℕ i → n ∸ suc (toℕ i) < n ∸ lo
monus-sink i below = ∸-monoʳ-< (s≤s below) (toℕ<n i)

mutual

  foldPath! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    (ac : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick) (envSrc : Source)
    (κ : Path Γ lo u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    ∃ λ r → foldPath⇓ {e = e} id now envSrc κ vals evs fin sched st r

  dispatchShare! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {i : Fin n}
    (ac : Acc _<_ (n ∸ suc (toℕ i))) (below : lo ≤ toℕ i)
    (id : Id) (now : Tick) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    ∃ λ r → dispatchShare⇓ {e = e} id now i below vals fin sched st r

  shareGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {i : Fin n}
    (ac : Acc _<_ (n ∸ suc (toℕ i))) (id : Id) (now : Tick)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    ∃ λ r → shareGo⇓ {e = e} id now i vals fin ps sched st r

  foldPath! ac id now envSrc root vals evs fin sched st = _ , fold-root
  foldPath! (acc rec) id now envSrc (share-sink i below) vals evs fin sched st =
    let (_ , d) = dispatchShare! (rec (monus-sink i below)) below
                    id now vals fin sched st
    in _ , fold-sink d
  foldPath! {u = u} ac id now envSrc (fr ↠ κ) vals evs fin sched st =
    let sl = Sched.slots sched
        ((vals′ , evs′ , fin′ , sched₁ , st₁) , sf) =
          stepFrameAny!
            (≺-wellFounded ( unconn sl (EvalSt.connectedShares st)
                           , suc (depᵛˢ (slotDepth sl) u vals) , 0 ))
            sl id now fr κ vals
            (handed-below (slotDepth sl) u vals ≤-refl)
            fin sched refl st ≤-refl
        (_ , rest) =
          foldPath! ac id now envSrc κ vals′ (evs ++ evs′) fin′ sched₁ st₁
    in _ , fold-step sf rest

  dispatchShare! {i = i} ac below id now vals fin sched st =
    let (_ , g) = shareGo! ac id now vals fin
                    (shareAdmit i (EvalSt.registry st))
                    sched (shareLatch i fin st)
    in _ , disp g

  shareGo! ac id now vals fin [] sched st = _ , go-nil
  shareGo! {i = i} ac id now vals fin ((rid , p) ∷ ps) sched st
    with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
  ... | true  = let (_ , g) = shareGo! ac id now vals fin ps sched st
                in _ , go-cut eqc g
  ... | false =
    let ((emits , sched₁ , st₁) , f) =
          foldPath! ac id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
        (_ , g) = shareGo! ac id now vals fin ps sched₁ st₁
    in _ , go-live eqc f g

-- ONE ARRIVAL DOWN ONE REGISTERED CHAIN.
chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (c : AtFloor Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  ∃ λ r → chainStep⇓ {e = e} id a c sched st r
chainStep! {n = n} id a (lo , path) sched st =
  let (_ , f) = foldPath! (<-wellFounded-fast (n ∸ lo)) id (arrTick a)
                  (arrSource a) path (arrVal a ∷ [])
                  (if Arrival.isLast a
                     then close (arrSource a) exhausted ∷ [] else [])
                  (Arrival.isLast a) sched st
  in _ , chain-step f

-- AND DOWN EVERY CHAIN THE ARRIVAL'S SOURCE IS REGISTERED ON, IN ORDER,
-- THREADING THE SCHEDULE AND THE STATE.
cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × AtFloor Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  ∃ λ r → cascadeGo⇓ {e = e} a id chains sched st r
cascadeGo! a id []               sched st = _ , casc-nil
cascadeGo! a id ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (_ , g) = cascadeGo! a id cs sched st in _ , casc-cut eqc g
... | false =
  let ((emits , sched₁ , st₁) , s) =
        chainStep! id a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
      (_ , g) = cascadeGo! a id cs sched₁ st₁
  in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  ∃ λ r → cascade⇓ {e = e} a id sched st r
cascade! a id sched st =
  let (_ , g) = cascadeGo! a id (chainsOf a st) sched (cascadeLatch a st)
  in _ , casc-run g

-- THE FAR END OF THE RUN, WHICH SPENDS FUEL OVER THE SCHEDULE RATHER
-- THAN DESCENDING ON A TERM — so it is structural on the fuel and owes
-- the cycle above it nothing but the arrival it just popped.
drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  ∃ λ rest → drain⇓ {e = e} fuel id sched st rest
drain! zero    id sched st = _ , drain-done
drain! (suc k) id sched st with sched-next sched in eqn
... | inj₁ _            = _ , drain-empty eqn
... | inj₂ (a , sched′) =
  let ((out , sched″ , st′) , c) = cascade! a id sched′ st
      (_ , d) = drain! k (suc id) sched″ st′
  in _ , drain-step eqn c d

------------------------------------------------------------------
-- THE TOP LINE, AND WHAT IT STOPS SAYING.
------------------------------------------------------------------

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, AND THE RELATION
-- SAYS SO IN ONE CONSTRUCTOR — so this is the assembly and the two
-- builders are its leaves.  The root's entry invariant is discharged by
-- `evaluate`'s own seeding, exactly as it is today.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
  (ins : Slots Γ) → ∃ λ out → evaluate⇓ fuel e ins out
evaluate! {n = n} fuel e ins =
  let ((burst , sched₀ , st₀) , s) =
        subscribeE! {lo = n} (rootWitness e ins) ins e (≤-refl , m≤m⊔n _ _)
                    root 0 0 (sched-init e ins) refl (st-init e) ≤-refl
      (rest , d) = drain! fuel 1 sched₀ st₀
  in (burst ++ rest) , eval-run s d

-- AND THE EVALUATOR AFTER THE CUTOVER.  Not a new machine — the SAME
-- machine with three clauses' worth of question removed, reached
-- through the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
