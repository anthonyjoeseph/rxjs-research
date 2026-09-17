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
-- reading of a rank and every `<?` have left the evaluator entirely.
-- No constructor of the relation builds a dry emit — not because a
-- number came out large enough, but because no arm of the builder
-- produces one.
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
-- `Rx.Evaluator.Domain` and `Rx.Evaluator.Reducible`, all of which
-- check in seconds.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; _≡ᵇ_; _<?_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl; ≮⇒≥; ∸-monoʳ-<)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Rx.Prim using (Fuel; Id; Source; Tick; InstEmit; InstEvent; close;
  exhausted; hot; cold)
open import Rx.Exp using (Ctx; Closed; Val; _≟ᵗ_; obs; unfoldμ; evalTm; subΘExp; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; freshId; setAt; next)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId; NodeState; Frame; root; _↠_; take-f;
  scan-f; thru-outer; from-inner; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st;
  exhaust-st; take-st; batchSync-st; batchSync-f; cell-st; installNode; lookupNode; setNode; hasRoom; consumeUsable;
  switchKill; aliveThroughᶠ; splitEvents; splitBurst; sched-init; st-init; memberSource;
  share-sink; lowerFloor; register; atSlot; burstCompleted; Arrival; arrTick; arrSource; arrTy;
  arrVal; AtFloor; RegId; chainsOf; cascadeLatch; sched-next; shareAdmit; shareLatch)
open import Rx.Evaluator.Keeps-Slots using (subs-keeps; step-keeps;
  consume-keeps; switchKill-slots)
open import Rx.Evaluator.Domain using (srcFrame; subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  stepFrame⇓; innerReact⇓; innerFinish⇓; mergeAllDrain⇓; thruWalk⇓;
  thruConsume⇓; subscribeInner⇓;
  finish-all-drain; finish-switch-clear;
  finish-exhaust-clear; finish-nil; react-false; react-alive; react-dead;
  push-nil; push-cons; step-scan;
  step-take; step-batchSync; step-from-inner; step-thru-outer;
  walk-nil; walk-cons; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil; inner;
  foldPath⇓; shareGo⇓; dispatchShare⇓; chainStep⇓; cascadeGo⇓; cascade⇓;
  fold-root; fold-sink; fold-step; go-nil; go-cut; go-live; disp;
  chain-step; casc-nil; casc-cut; casc-live; casc-run;
  drain-done; drain-empty; drain-step;
  drain-nil; drain-no-room; drain-room;
  drain⇓; evaluate⇓; subs-of; subs-empty; subs-take-zero;
  subs-take-suc; subs-batchSync; subs-lift; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; subs-mint; sub-all; eval-run;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; slot-spent; slot-join; slot-connect; connect-live;
  connect-died)
open import Rx.Evaluator.Reducible using (reducible)

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
-- AND ALL THREE ARE PROVEN NEXT DOOR, as one structural induction over
-- the family's own SCC: no constructor writes the table, so each is
-- `refl` at a leaf and a recursion elsewhere.  They are imported rather
-- than restated because the walk needs every member of the block and
-- the block is not this module's.

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

-- EIGHT SIGNATURES BEFORE ANY BODY, AND WHAT THE BLOCK NO LONGER
-- CARRIES IS A MEASURE.  Every member here descends on a term or
-- shortens a list, which Agda reads for itself.  The four edges that
-- descend on NEITHER — the μ peel, the mint's substituted body, the hop
-- out of a burst, and a share's connect — leave the block entirely and are answered by
-- `reducible`, whose recursion is on the TYPE rather than on anything
-- this block can see.  So the premises a measure needed at every call
-- site are gone: what travels is the slot table, and it travels because
-- the arms genuinely dispatch on it.
--
-- AND ONLY ONE CYCLE SURVIVES THE FOUR LEAVING, which is sharper than
-- the block's size suggests: the flattener's outer subscribe re-enters
-- the term subscribe at the operator's own argument, and that is the
-- whole of the recursion here.  The other six members are in the block
-- for DEFINITION ORDER rather than for mutuality -- the push cycle, the
-- frame step and the burst walk are each entered once and reach nothing
-- that reaches them, because what used to close their loop was the hop.
--
-- STRUCTURAL SCC: subscribeAll! subscribeE!

subscribeE! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  (sl : Slots Γ) (b : Closed Γ u)
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  Runs {e = e} b κ id now sched st

subscribeE!-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
  (sl : Slots Γ) (i : Fin n)
  (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  Runs {e = e} (input i) κ id now sched st

subscribeAll! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  (sl : Slots Γ) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u))
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  AllRuns {e = e} op ns b κ id now sched st

pushBurst! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
  (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  → srcFrame fr →
  (κ : Path Γ lo u t) (bs : Stream Γ s)
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  PushRuns {e = e} id now fr κ bs sched st

stepFrame! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
  (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  → srcFrame fr →
  (κ : Path Γ lo u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  StepRuns {e = e} id now fr κ vals fin sched st

thruWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  (sl : Slots Γ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  WalkRuns {e = e} op nid κ id now os sched st

thruConsume! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  (sl : Slots Γ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  ConsumeRuns {e = e} op nid κ id now o sched st

subscribeInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  (sl : Slots Γ) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  InnerSubRuns {e = e} op allNid κ id now o sched st

-- EVERY OPERATOR CLAUSE DESCENDS ON THE TERM, so Agda reads the
-- recursion off the constructor and nothing has to be handed in
-- alongside it.  What still travels is the slot agreement, because the
-- input arm genuinely dispatches on the table and the relation speaks
-- of the schedule's own reading.
subscribeE! sl (input i) κ id now sched ag st =
  subscribeE!-input sl i κ id now sched ag st
subscribeE! sl (ofᵉ ts)  κ id now sched ag st = _ , subs-of refl
subscribeE! sl emptyᵉ    κ id now sched ag st = _ , subs-empty refl


subscribeE! sl (takeᵉ c b) κ id now sched ag st
  with evalTm c in eq
... | zero  = _ , subs-take-zero eq refl
... | suc k =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((burst , sched₂ , st₁) , d) =
        subscribeE! sl b (take-f nid ↠ κ) id now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }) ag
                    (installNode nid (take-st (suc k)) st)
      (r , p) = pushBurst! sl id now (take-f nid) tt κ burst sched₂
                  (trans (subs-keeps d) ag) st₁
  in r , subs-take-suc eq refl d p

subscribeE! sl (batchSyncᵉ b) κ id now sched ag st =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((burst , sched₂ , st₁) , d) =
        subscribeE! sl b (batchSync-f nid ↠ κ) id now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }) ag
                    (installNode nid (batchSync-st true) st)
      ((out , sched₃ , st₂) , p) =
        pushBurst! sl id now (batchSync-f nid) tt κ burst sched₂
          (trans (subs-keeps d) ag) st₁
  in ( out , sched₃
     , record st₂ { nodes = setNode nid (batchSync-st false) (EvalSt.nodes st₂) } )
     , subs-batchSync refl d p


subscribeE! sl (scanᵉ f i b) κ id now sched ag st =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((burst , sched₂ , st₁) , d) =
        subscribeE! sl b (scan-f f nid ↠ κ) id now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }) ag
                    (installNode nid (cell-st (evalTm i)) st)
      (r , p) = pushBurst! sl id now (scan-f f nid) tt κ burst sched₂
                  (trans (subs-keeps d) ag) st₁
  in r , subs-lift refl d p

subscribeE! sl (mergeAllᵉ lim b) κ id now sched ag st =
  let (r , a) = subscribeAll! sl mergeAllᵒ (mergeAll-st lim 0 [] false)
                              b κ id now sched ag st
  in r , subs-merge-all a
subscribeE! sl (switchAllᵉ b) κ id now sched ag st =
  let (r , a) = subscribeAll! sl switchᵒ (switch-st nothing false)
                              b κ id now sched ag st
  in r , subs-switch-all a
subscribeE! sl (exhaustAllᵉ b) κ id now sched ag st =
  let (r , a) = subscribeAll! sl exhaustᵒ (exhaust-st false false)
                              b κ id now sched ag st
  in r , subs-exhaust-all a

-- THE μ PEEL, WHICH IS THE FIRST OF THE THREE EDGES THIS BLOCK CANNOT
-- PAY FOR.  An unfolding is not a subterm of the fixpoint, so no
-- structural reading of the term reaches it; the reducibility candidate
-- does, because the unfolding sits at the SAME type and the candidate
-- recurses on the type rather than on the term.
subscribeE! sl (μᵉ body) κ id now sched ag st =
  let (r , d , _) = reducible (unfoldμ body) κ id now sched st
  in r , subs-μ d

subscribeE! sl (varᵉ ()) κ id now sched ag st
subscribeE! sl (deferᵉ body) κ id now sched ag st = _ , subs-defer refl refl refl refl
subscribeE! sl (mintᵉ body) κ id now sched ag st =
  let src    = freshId sourceᵏ (Sched.mint sched)
      sched' = record sched { mint = setAt sourceᵏ (suc src) (Sched.mint sched) }
      (r , d , _) = reducible (subΘExp [] (src ∷ᵃ []ᵃ) body) κ id now sched' st
  in r , subs-mint refl d

-- THE FLATTENER'S OUTER SUBSCRIBE, WHICH HAS EXACTLY ONE CLAUSE.  All
-- three `*All` operators install their own node state and then run the
-- same outer subscribe through a `thru-outer` frame, so the operator is
-- carried as a value and the shape is shared.
subscribeAll! sl op ns b κ id now sched ag st =
  let nid = freshId nodeᵏ (Sched.mint sched)
      ((burst , sched₂ , st₁) , d) =
        subscribeE! sl b (thru-outer op nid ↠ κ) id now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }) ag
                    (installNode nid ns st)
      (r , p) = pushBurst! sl id now (thru-outer op nid) tt κ burst sched₂
                  (trans (subs-keeps d) ag) st₁
  in r , sub-all refl d p

-- THE PUSH CYCLE STEPS ONE EMIT PER ITERATION, handing the frame that
-- emit's own values and threading the schedule and the state onward.
--
pushBurst! sl id now fr sv κ []         sched ag st = _ , push-nil
pushBurst! sl id now fr sv κ (em ∷ ems) sched ag st =
  let sp = splitEvents (InstEmit.events em)
      ((vals′ , evs , fin′ , sched₁ , st₁) , sf) =
        stepFrame! sl id now fr sv κ (proj₁ sp)
          (proj₂ (proj₂ sp)) sched ag st
      (_ , pb) = pushBurst! sl id now fr sv κ ems sched₁
                   (trans (step-keeps sf) ag) st₁
  in _ , push-cons refl sf pb

-- THE STORE READINGS COST THE BUILDER NOTHING BECAUSE EACH FRAME'S
-- RELATION IS PINNED TO THE MACHINE'S OWN DISPATCH.  A node table
-- carries its accumulator's type existentially, so the scan frame's
-- `u` has to be decided against what is installed and the take frame's
-- count may be missing entirely; both decisions live inside the
-- dispatch function the single constructor names, so no branch is
-- split here and none has to be proven unreachable.
stepFrame! sl id now (take-f nid) sv κ vals fin sched ag st = _ , step-take

stepFrame! sl id now (batchSync-f nid) sv κ vals fin sched ag st = _ , step-batchSync


stepFrame! sl id now (scan-f fn nid) sv κ vals fin sched ag st = _ , step-scan

stepFrame! sl id now (from-inner op allNid inst) () κ vals fin sched ag st

stepFrame! sl id now (thru-outer op nid) sv κ vals fin sched ag st =
  let ((vs , bs , sched′ , st′) , w) =
        thruWalk! sl op nid κ id now vals sched ag st
  in _ , step-thru-outer w

thruWalk! sl op nid κ id now []       sched ag st = _ , walk-nil
thruWalk! sl op nid κ id now (o ∷ os) sched ag st =
  let ((vs , bs , sched₁ , st₁) , c) =
        thruConsume! sl op nid κ id now o sched ag st
      (_ , w) = thruWalk! sl op nid κ id now os sched₁
                  (trans (consume-keeps c) ag) st₁
  in _ , walk-cons c w

-- WHAT A CONSUME CLAUSE DECIDES IS WHETHER THE OBSERVABLE IS TAKEN AT
-- ALL, AND EVERY OPERATOR ANSWERS IT OFF THE STORE.  A merge takes it
-- when the lane count leaves room and queues it otherwise, a switch
-- always takes it and kills whatever was running first, an exhaust
-- takes it only while nothing is running.  Every other reading of the
-- node — the wrong operator's state, the wrong accumulator type, no
-- node at all — collapses to the operator's own nil clause, which is
-- the same collapse the machine reaches through its catch-all.
thruConsume! {u = u} sl mergeAllᵒ nid κ id now o sched ag st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing              = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (cell-st _)     = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (take-st _)     = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (batchSync-st _) = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (switch-st _ _) = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (exhaust-st _ _) = _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u in eqw
...   | no  _    = _ , consume-all-nil
                        (trans (cong (consumeUsable mergeAllᵒ u) eq) (cong ⌊_⌋ eqw))
...   | yes refl with hasRoom lim act in eqr
...     | false = _ , consume-all-enqueue eq eqr
...     | true  =
          let (_ , i) = subscribeInner! sl mergeAllᵒ nid κ id now o sched ag st
          in _ , consume-all-sub eq eqr i

thruConsume! {u = u} sl switchᵒ nid κ id now o sched ag st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (cell-st _)           = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (take-st _)           = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (batchSync-st _)      = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (mergeAll-st _ _ _ _) = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (exhaust-st _ _)      = _ , consume-switch-nil (cong (consumeUsable switchᵒ _) eq)
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (closes , sched₁ , st₁) =
        let (_ , i) = subscribeInner! sl switchᵒ nid κ id now o sched₁
                        (trans (switchKill-slots cur sched st eqk) ag) st₁
        in _ , consume-switch-sub eq eqk i

thruConsume! {u = u} sl exhaustᵒ nid κ id now o sched ag st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (cell-st _)           = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (take-st _)           = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (batchSync-st _)      = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (mergeAll-st _ _ _ _) = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (switch-st _ _)       = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (exhaust-st true _)   = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ _) eq)
... | just (exhaust-st false od) =
      let (_ , i) = subscribeInner! sl exhaustᵒ nid κ id now o sched ag st
      in _ , consume-exhaust-sub eq i

-- THE HOP, WHICH IS THE SECOND EDGE THIS BLOCK CANNOT PAY FOR.  What
-- arrives here is a runtime VALUE taken out of a burst, so it stands in
-- no structural relation to the term that produced it and no report
-- about the burst can make it one.  It does stand at a strictly smaller
-- TYPE — the flattener's `obs (obs u)` has become `obs u` — which is
-- exactly the descent the candidate recurses on, so the hop is answered
-- by `reducible` and the block is left with nothing to carry.
subscribeInner! sl op allNid κ id now o sched ag st =
  let inst = freshId nodeᵏ (Sched.mint sched)
      ((burst , sched′ , st′) , d , _) =
        reducible o (from-inner op allNid inst ↠ κ) id now
                  (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st
      (vs , bs , done) = splitBurst burst
  in (inst , vs , bs , done , sched′ , st′) , inner refl d refl

-- THE SLOT TABLE'S SIX ARMS, AND THE ONE OF THEM THAT RECURSES — WHICH
-- IS THE THIRD EDGE THIS BLOCK CANNOT PAY FOR.  Five arms read the
-- table and hand back a burst the relation already names, so they are
-- the agreement transported and a constructor; the sixth CONNECTS a
-- share, and connecting subscribes the slot's own DEFINITION, which is
-- an arbitrary term standing in no relation to the `input` that named
-- it.  The candidate answers it, at the definition's own type.
--
-- AND NOTHING ABOUT THE STATE IS OWED AT THIS EDGE, WHICH IS WHY IT
-- COSTS ONE CALL RATHER THAN AN INVARIANT.  The candidate quantifies
-- over every schedule and every state, so the freshly-registered state
-- this arm hands down is one of them by construction, and the connected
-- set having just gained an index is not a premise anybody has to
-- transport.
subscribeE!-input {lo = lo} sl i κ id now sched ag st
  with toℕ i <? lo
... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below)
... | yes below  with sl i in slEq
...   | scripted (hot async)
        with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
...     | true  = _ , subs-hot-done below (slot-agree sl sched i ag slEq) doneEq
...     | false = _ , subs-hot-live below (slot-agree sl sched i ag slEq) doneEq refl
subscribeE!-input {lo = lo} sl i κ id now sched ag st
    | yes below | scripted (cold sync []) =
      _ , subs-cold-sync below (slot-agree sl sched i ag slEq) refl
subscribeE!-input {lo = lo} sl i κ id now sched ag st
    | yes below | scripted (cold sync (d ∷ ds)) =
      _ , subs-cold-async below (slot-agree sl sched i ag slEq) refl refl refl
subscribeE!-input {lo = lo} sl i κ id now sched ag st
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
                  (slot-join {κ = κ} {below = below} doneEq connEq refl)
...       | false
            with reducible d (share-sink i ≤-refl) id now
                   (record sched { mint = next regᵏ (Sched.mint sched) })
                   (register (freshId regᵏ (Sched.mint sched))
                     (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
...         | ((burst , sched₁ , st₂) , dv , _) with burstCompleted burst in compEq
...           | false =
                _ , subs-shared {κ = κ} {below = below}
                      (slot-agree sl sched i ag slEq)
                      (slot-connect doneEq connEq
                        (connect-live {κ = κ} {below = below} refl dv compEq))
...           | true  =
                _ , subs-shared {κ = κ} {below = below}
                      (slot-agree sl sched i ag slEq)
                      (slot-connect doneEq connEq
                        (connect-died {κ = κ} {below = below} refl dv compEq))

------------------------------------------------------------------
-- THE COMPLETION SIDE, WHICH THE CYCLE ABOVE CANNOT REACH.
------------------------------------------------------------------

-- THE QUEUED SUBSCRIBE IS AN ENTRY, AND AN ENTRY NOW COSTS NOTHING.
-- Nothing a subscribe does reaches a completion: the inner's frame is
-- never PUSHED, only walked later by the instant loop, which is what
-- `srcFrame` says in a type.  So the drain enters the block from
-- outside, and the only premise the block still has is the slot
-- agreement, which is `refl` because the table is read off the schedule
-- handed in.
queuedInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  (allNid : NodeId) (κ : Path Γ lo s t) (id : Id) (now : Tick)
  (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  InnerSubRuns {e = e} mergeAllᵒ allNid κ id now o sched st
queuedInner! allNid κ id now o sched st =
  subscribeInner! (Sched.slots sched) mergeAllᵒ allNid κ id now o sched refl st

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
             (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s in eqw
... | no  _    = _ , finish-nil (cong ⌊_⌋ eqw)
... | yes refl =
      let (_ , d) = mergeAllDrain! allNid κ id now lim (pred act) od q sched st
      in _ , finish-all-drain d
innerFinish! switchᵒ allNid inst κ id now vals sched st
             (just (switch-st (just c) od)) with (c ≡ᵇ inst) in eqc
... | true  = _ , finish-switch-clear eqc
... | false = _ , finish-nil eqc
innerFinish! exhaustᵒ allNid inst κ id now vals sched st
             (just (exhaust-st act od)) = _ , finish-exhaust-clear

-- EVERY OTHER READING IS THE COLLAPSE, AND IT IS SPELT OUT RATHER THAN
-- CAUGHT, because the fallback now carries a side condition and a
-- condition on two variables does not reduce.  One clause per operator
-- per shape the store can be in, each handing back the same `refl`.
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st nothing = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = _ , finish-nil refl
innerFinish! mergeAllᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st nothing = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (mergeAll-st _ _ _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = _ , finish-nil refl
innerFinish! switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st nothing = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st (just (cell-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st (just (take-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st (just (batchSync-st _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st (just (mergeAll-st _ _ _ _)) = _ , finish-nil refl
innerFinish! exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = _ , finish-nil refl

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
stepFrameAny! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
  (sl : Slots Γ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (vals : List (Val Γ s))
  (fin : Bool) (sched : Sched Γ) → Sched.slots sched ≡ sl → (st : EvalSt e) →
  StepRuns {e = e} id now fr κ vals fin sched st
stepFrameAny! sl id now (from-inner op allNid inst) κ vals fin sched ag st =
  let (_ , r) = innerReact! op allNid inst κ id now vals sched st fin
  in _ , step-from-inner r
stepFrameAny! sl id now (take-f nid) κ vals fin sched ag st =
  stepFrame! sl id now (take-f nid) tt κ vals fin sched ag st
stepFrameAny! sl id now (batchSync-f nid) κ vals fin sched ag st =
  stepFrame! sl id now (batchSync-f nid) tt κ vals fin sched ag st
stepFrameAny! sl id now (scan-f fn nid) κ vals fin sched ag st =
  stepFrame! sl id now (scan-f fn nid) tt κ vals fin sched ag st
stepFrameAny! sl id now (thru-outer op nid) κ vals fin sched ag st =
  stepFrame! sl id now (thru-outer op nid) tt κ vals fin sched ag st

------------------------------------------------------------------
-- THE ARRIVAL CYCLE, WHICH IS A SECOND ENTRY AND NOT A CONTINUATION.
------------------------------------------------------------------

-- A SITE ENTERING THE SUBSCRIBE BLOCK FROM OUTSIDE PAYS ONE PREMISE,
-- AND IT IS `refl`.  The slot agreement is the only thing the block
-- still carries, and the table is read off the schedule handed in.
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
          stepFrameAny! sl id now fr κ vals fin sched refl st
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
  let (_ , g) = cascadeGo! a id (chainsOf a st) sched (cascadeLatch a sched st)
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
  let ((burst , sched₀ , st₀) , s , _) =
        reducible e root 0 0 (sched-init e ins) (st-init e)
      (rest , d) = drain! fuel 1 sched₀ st₀
  in (burst ++ rest) , eval-run s d

-- AND THE EVALUATOR AFTER THE CUTOVER.  Not a new machine — the SAME
-- machine with three clauses' worth of question removed, reached
-- through the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
