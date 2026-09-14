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
-- SO THE EVALUATOR BECOMES A PROJECTION, AND THAT IS THE CUTOVER.
-- `evaluate` today is a recursion carrying `Acc _≺_ τ`; after, it is
-- `proj₁` of this, and every reading of a rank, every `<?`, every
-- `dryBurst` and the marker `dried` itself leave the evaluator
-- entirely.  `hasDry` then reads `false` of every run because no
-- constructor of the relation builds a dry emit — not because a number
-- came out large enough.
--
-- AND THE ORDER THIS FORCES IS THE ONE CONSTRAINT THE DEAD ROUTE IN
-- `Verify-Rank-Sufficient` NAMES.  A projection computes only if the
-- thing projected is a real body: leave any of the leaves below a
-- postulate and the bug cache, the oracle and every probe's `refl` get
-- stuck at the first match.  So the leaves land before `evaluate` is
-- re-pointed, and until then both machines exist side by side.
--
-- WHY IT SITS BELOW THE MACHINE RATHER THAN BESIDE THE PROOF THAT
-- CONSUMES IT.  Nothing here needs the recursion it replaces, and the
-- recursion does not compile — so a builder placed above it inherits a
-- cone the dev loop cannot warm and stops being iterable at exactly the
-- point where it is being written.  Below, the cone is `Rx.Evaluator`,
-- `Rx.Evaluator.Domain` and `Rx.Evaluator.Doorless`, all of which check
-- in seconds.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Fuel; Id; Tick; InstEmit)
open import Rx.Exp using (Ctx; Closed; Val; _≟ᵗ_; obs; unfoldμ; evalTm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId; NodeState; Frame; root; _↠_; map-f; take-f; scan-f;
  thru-outer; from-inner; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; take-st;
  scan-st; installNode; lookupNode; hasRoom; switchKill; splitEvents; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  stepFrame⇓; innerReact⇓; thruWalk⇓; thruConsume⇓; subscribeInner⇓;
  push-nil; push-cons; step-map; step-scan;
  step-scan-nil; step-take; step-from-inner; step-thru-outer;
  walk-nil; walk-cons; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil;
  drain⇓; evaluate⇓; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; sub-all; eval-run)
open import Rx.Evaluator.Doorless using (μ-edge; μ-entry; rootWitness;
  EntryOK; inner-ok; under-ok)

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

------------------------------------------------------------------
-- THE LEAVES, WHICH ARE WHAT MAKE THE ASSEMBLY CHECKABLE TODAY.
------------------------------------------------------------------

-- THE HOP, WHICH IS THE ONE LEAF THAT RE-ENTERS THE SUBSCRIBE CYCLE
-- AND THE ONE PLACE THE DELETED DOOR USED TO ASK ITS QUESTION.  Its
-- single constructor subscribes the handed observable under a
-- `from-inner` frame, so writing it is writing a call back into
-- `subscribeE!` — and it is the only descent in this module that moves
-- τ rather than carrying it, which is why it lands last and joins the
-- mutual block when it does.
--
-- RECOVERY: `git show 0bfaccc:agda/src/Verify-Rank-Sufficient/Doorless.agda`
--   holds `subscribeInner!` written out — four lines against the
--   machine's, the `with obsDepthᵉ o <? r` and its dry arm deleted and
--   the descent witness taken from the report instead.
postulate
  subscribeInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
    (ac : Acc _≺_ τ) (op : AllOp) (allNid : NodeId) (κ : Path Γ lo u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    InnerSubRuns {e = e} op allNid κ id now o sched st

-- AND THE INNER REACTION, WHOSE FINISHING ARM DRAINS A QUEUE THAT CAN
-- SUBSCRIBE FROM IT.  A leaf for the same reason and not the same
-- shape: what sits under it is the merge drain and the three
-- operators' completion arms, none of which the walk below reaches.
postulate
  innerReact! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {τ : Tri}
    (ac : Acc _≺_ τ) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ lo s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
    InnerRuns {e = e} op allNid inst κ id now vals sched st fin

------------------------------------------------------------------
-- THE OUTER WALK, THE FRAME STEP AND THE BURST PUSH, WHICH ARE NOW
-- BODIES.
------------------------------------------------------------------

-- WHAT A CONSUME CLAUSE DECIDES IS WHETHER THE OBSERVABLE IS TAKEN AT
-- ALL, AND EVERY OPERATOR ANSWERS IT OFF THE STORE.  A merge takes it
-- when the lane count leaves room and queues it otherwise, a switch
-- always takes it and kills whatever was running first, an exhaust
-- takes it only while nothing is running.  Every other reading of the
-- node — the wrong operator's state, the wrong accumulator type, no
-- node at all — collapses to the operator's own nil clause, which is
-- the same collapse the machine reaches through its catch-all.
thruConsume! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  ConsumeRuns {e = e} op nid κ id now o sched st

thruConsume! {u = u} ac mergeAllᵒ nid κ id now o sched st
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
          let (_ , i) = subscribeInner! ac mergeAllᵒ nid κ id now o sched st
          in _ , consume-all-sub eq eqr i

thruConsume! ac switchᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-switch-nil
... | just (scan-st _)           = _ , consume-switch-nil
... | just (take-st _)           = _ , consume-switch-nil
... | just (mergeAll-st _ _ _ _) = _ , consume-switch-nil
... | just (exhaust-st _ _)      = _ , consume-switch-nil
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (closes , sched₁ , st₁) =
        let (_ , i) = subscribeInner! ac switchᵒ nid κ id now o sched₁ st₁
        in _ , consume-switch-sub eq eqk i

thruConsume! ac exhaustᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , consume-exhaust-nil
... | just (scan-st _)           = _ , consume-exhaust-nil
... | just (take-st _)           = _ , consume-exhaust-nil
... | just (mergeAll-st _ _ _ _) = _ , consume-exhaust-nil
... | just (switch-st _ _)       = _ , consume-exhaust-nil
... | just (exhaust-st true _)   = _ , consume-exhaust-nil
... | just (exhaust-st false od) =
      let (_ , i) = subscribeInner! ac exhaustᵒ nid κ id now o sched st
      in _ , consume-exhaust-sub eq i

thruWalk! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  WalkRuns {e = e} op nid κ id now os sched st

thruWalk! ac op nid κ id now []       sched st = _ , walk-nil
thruWalk! ac op nid κ id now (o ∷ os) sched st =
  let ((vs , bs , sched₁ , st₁) , c) = thruConsume! ac op nid κ id now o sched st
      (_ , w) = thruWalk! ac op nid κ id now os sched₁ st₁
  in _ , walk-cons c w

-- THE SCAN CLAUSE IS THE ONLY ONE THAT LOOKS AT THE STORE, AND THE
-- RELATION SAYS WHAT TO DO WHEN THE READING DISAGREES.  A node table
-- carries its accumulator's type existentially, so the frame's own `u`
-- has to be decided against what is installed; every answer but `yes`
-- takes the nil clause, which is the same collapse the machine reaches
-- by its `dispatch`.  Nothing is owed here — the relation offers a
-- constructor at every reading, so the builder chooses rather than
-- having to prove a branch unreachable.
stepFrame! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  StepRuns {e = e} id now fr κ vals fin sched st

stepFrame! ac id now (map-f fn) κ vals fin sched st = _ , step-map
stepFrame! ac id now (take-f nid) κ vals fin sched st = _ , step-take

stepFrame! {u = u} ac id now (scan-f fn nid) κ vals fin sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = _ , step-scan-nil
... | just (take-st _)           = _ , step-scan-nil
... | just (mergeAll-st _ _ _ _) = _ , step-scan-nil
... | just (switch-st _ _)       = _ , step-scan-nil
... | just (exhaust-st _ _)      = _ , step-scan-nil
... | just (scan-st {w} a)       with w ≟ᵗ u
...   | no  _    = _ , step-scan-nil
...   | yes refl = _ , step-scan eq refl

stepFrame! ac id now (from-inner op allNid inst) κ vals fin sched st =
  let (r , ir) = innerReact! ac op allNid inst κ id now vals sched st fin
  in r , step-from-inner ir

stepFrame! ac id now (thru-outer op nid) κ vals fin sched st =
  let ((vs , bs , sched′ , st′) , w) = thruWalk! ac op nid κ id now vals sched st
  in _ , step-thru-outer w

pushBurst! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (bs : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  PushRuns {e = e} id now fr κ bs sched st

pushBurst! ac id now fr κ []         sched st = _ , push-nil
pushBurst! ac id now fr κ (em ∷ ems) sched st =
  let sp = splitEvents (InstEmit.events em)
      ((vals′ , evs , fin′ , sched₁ , st₁) , sf) =
        stepFrame! ac id now fr κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
      (_ , pb) = pushBurst! ac id now fr κ ems sched₁ st₁
  in _ , push-cons refl sf pb

-- AND THE TWO ENDS OF THE RUN.  An input's subscribe reads the slot
-- table and branches on what is registered there, and the drain spends
-- fuel over the schedule; neither is in the recursion this module is
-- for, so neither is written here.
postulate
  subscribeE!-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
    (ac : Acc _≺_ τ) (i : Fin n) → EntryOK {Γ = Γ} (input i) τ →
    (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    Runs {e = e} (input i) κ id now sched st

  drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    ∃ λ rest → drain⇓ {e = e} fuel id sched st rest

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE'S ENTRY, WITH THE μ PEEL'S TEST GONE.
------------------------------------------------------------------

-- EVERY OPERATOR CLAUSE DESCENDS ON THE TERM AND CARRIES THE SAME τ,
-- so the accessibility is passed through untouched and only the entry
-- invariant has to travel.  `inner-ok` and `under-ok` are that
-- travelling: the two measures read an operator as `suc (template +
-- source)` and `template ⊔ source` respectively, and what the source
-- needs is the right half of each.  The one clause that moves τ is the
-- μ peel below, and it is the only place a witness is spent.
subscribeE! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → Runs {e = e} b κ id now sched st

subscribeAll! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (op : AllOp) (ns : NodeState Γ) (b : Closed Γ (obs u)) →
  EntryOK b τ → (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  AllRuns {e = e} op ns b κ id now sched st

subscribeE! ac (input i) ok κ id now sched st =
  subscribeE!-input ac i ok κ id now sched st
subscribeE! ac (ofᵉ ts)  ok κ id now sched st = _ , subs-of refl
subscribeE! ac emptyᵉ    ok κ id now sched st = _ , subs-empty refl

subscribeE! ac (mapᵉ f b) ok κ id now sched st =
  let ((burst , sched₁ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (map-f f ↠ κ) id now sched st
      (r , p) = pushBurst! ac id now (map-f f) κ burst sched₁ st₁
  in r , subs-map d p

subscribeE! ac (takeᵉ c b) ok κ id now sched st
  with evalTm c in eq
... | zero  = _ , subs-take-zero eq refl
... | suc k =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (take-f nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid (take-st (suc k)) st)
      (r , p) = pushBurst! ac id now (take-f nid) κ burst sched₂ st₁
  in r , subs-take-suc eq refl d p

subscribeE! ac (scanᵉ f z b) ok κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (scan-f f nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid (scan-st (evalTm z)) st)
      (r , p) = pushBurst! ac id now (scan-f f nid) κ burst sched₂ st₁
  in r , subs-scan refl d p

subscribeE! ac (mergeAllᵉ lim b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac mergeAllᵒ (mergeAll-st lim 0 [] false)
                              b (under-ok ok) κ id now sched st
  in r , subs-merge-all a
subscribeE! ac (switchAllᵉ b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac switchᵒ (switch-st nothing false)
                              b (under-ok ok) κ id now sched st
  in r , subs-switch-all a
subscribeE! ac (exhaustAllᵉ b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac exhaustᵒ (exhaust-st false false)
                              b (under-ok ok) κ id now sched st
  in r , subs-exhaust-all a

-- THE μ PEEL.  Against the machine the deletion is the whole clause's
-- `with`: `unfoldμ-shrinks` is a fact about the term and needs no
-- number handed in, so `μ-edge` is the descent outright.  The entry
-- invariant travels with it through `μ-entry`, which is the same
-- composition the old totality proof wrote under `⊥-elim`.
subscribeE! (acc rec) (μᵉ body) (sz≤ , r≤) κ id now sched st =
  let (r , d) = subscribeE! (rec (μ-edge body sz≤ r≤)) (unfoldμ body)
                            (≤-refl , μ-entry body r≤) κ id now sched st
  in r , subs-μ d

subscribeE! ac (varᵉ ()) ok κ id now sched st
subscribeE! ac (deferᵉ body) ok κ id now sched st = _ , subs-defer refl refl refl

-- THE FLATTENER'S OUTER SUBSCRIBE, WHICH HAS EXACTLY ONE CLAUSE.  All
-- three `*All` operators install their own node state and then run the
-- same outer subscribe through a `thru-outer` frame, so the operator is
-- carried as a value and the shape is shared.
subscribeAll! ac op ns b ok κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b ok (thru-outer op nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid ns st)
      (r , p) = pushBurst! ac id now (thru-outer op nid) κ burst sched₂ st₁
  in r , sub-all refl d p

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
        subscribeE! {lo = n} (rootWitness e ins) e (≤-refl , m≤m⊔n _ _)
                    root 0 0 (sched-init e ins) (st-init e)
      (rest , d) = drain! fuel 1 sched₀ st₀
  in (burst ++ rest) , eval-run s d

-- AND THE EVALUATOR AFTER THE CUTOVER.  Not a new machine — the SAME
-- machine with three clauses' worth of question removed, reached
-- through the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
