-- NOTHING A SUBSCRIPTION OR A FAN-OUT DOES EVER RAISES THE UNCONNECTED
-- COUNT, PROVEN OVER THE TWO FIELDS THE COUNT READS.  The candidate
-- descends on that count, and the descent travels as a CEILING with its
-- accessibility beside it: only the connect peels the witness, and
-- every other step hands the same witness on and RE-PROVES the bound.
-- Re-proving it is what this family is, and `room-keeps` is where the
-- two meet.
--
-- IT IS STATED OVER THE FIELDS RATHER THAN OVER THE STATES, which is
-- what makes almost every clause reflexivity.  A step rebuilds its
-- schedule and its state by record update, and a record update is not
-- definitionally what it came from -- but the PROJECTION out of one
-- reduces, so a step writing nodes, registrations, the live set or the
-- cancelled list arrives at `keeps-refl` with nothing to transport.
--
-- ONLY ONE EDGE IN THE WHOLE EVALUATOR MOVES EITHER FIELD, and it moves
-- one of them by a cons: the connect adds its own slot's index to the
-- connected set before subscribing the definition.  `Sched.slots` has a
-- single writer, the schedule's own initialisation, so the table half
-- is reflexivity everywhere below.
module Rx.Evaluator.Keeps where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; obs; FnClo; _×ᵗ_; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; Segs; Stream;
  switchKill; scanDispatch; takeDispatch; batchDispatch; thruWrap; shareDying; shareSpend; shareFinish;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  lookupNode; takeVals)
open import Rx.Evaluator.Unconn-Arith using (KeepsC; keeps-refl; keeps-trans;
  keeps-cons)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; pushBurst⇓;
  pushSegs⇓; psegs-nil; psegs-cons;
  subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  foldPath⇓; foldVSegs⇓; dispatchShare⇓; shareWalk⇓; shareGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero; subs-take-suc;
  subs-batchSync; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; subs-mint;
  inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-batchSync; step-from-inner; step-thru-outer;
  push-nil; push-cons; sub-all; connect-live; connect-died;
  slot-spent; slot-join; slot-connect;
  disp; walk-end; walk-more; go-nil; go-cut; go-live;
  fold-root; fold-sink; fold-step; segs-nil; segs-last; segs-more)

-- THE PAIR OF FIELDS, NAMED ONCE.  Spelling both projections at every
-- one of the eighteen signatures below is what made the count's own
-- statements unreadable the first time they were written.
Keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Keeps sched st sched′ st′ =
  KeepsC (Sched.slots sched)  (EvalSt.connectedShares st)
         (Sched.slots sched′) (EvalSt.connectedShares st′)

-- the switch's cut sweeps live registrations and the cancelled list
switchKill-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                     (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                     {sched₁ st₁}
                 → switchKill {e = e} cur sched st ≡ (sched₁ , st₁)
                 → Keeps {e = e} sched st sched₁ st₁
switchKill-keeps nothing  sched st refl = keeps-refl _ _
switchKill-keeps (just v) sched st refl = keeps-refl _ _

-- the fold's dispatch rewrites its own node
scanDispatch-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                       (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                       (vals : List (Val Γ s)) (fin : Bool)
                       (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                   → Keeps {e = e} sched st
                       (proj₁ (proj₂ (proj₂
                         (scanDispatch {e = e} fn nid vals fin sched st m))))
                       (proj₂ (proj₂ (proj₂
                         (scanDispatch {e = e} fn nid vals fin sched st m))))
scanDispatch-keeps {u = u} fn nid vals fin sched st (just (cell-st {w} a))
  with w ≟ᵗ u
... | no  _    = keeps-refl _ _
... | yes refl = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st nothing                      = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st (just (take-st _))           = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st (just (batchSync-st _ _ _))      = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st (just (switch-st _ _))       = keeps-refl _ _
scanDispatch-keeps fn nid vals fin sched st (just (exhaust-st _ _))      = keeps-refl _ _

-- the truncation's cut severs registrations and rewrites its own node
takeDispatch-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                       (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                   → Keeps {e = e} sched st
                       (proj₁ (proj₂ (proj₂
                         (takeDispatch {e = e} nid vals fin sched st m))))
                       (proj₂ (proj₂ (proj₂
                         (takeDispatch {e = e} nid vals fin sched st m))))
takeDispatch-keeps nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = keeps-refl _ _
... | false = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st nothing                      = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st (just (cell-st _))           = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st (just (batchSync-st _ _ _))      = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st (just (mergeAll-st _ _ _ _)) = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st (just (switch-st _ _))       = keeps-refl _ _
takeDispatch-keeps nid vals fin sched st (just (exhaust-st _ _))      = keeps-refl _ _

-- the bracket writes its buffer while the bit is up and nothing after
batchDispatch-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                        (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                        (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                    → Keeps {e = e} sched st
                        (proj₁ (proj₂ (proj₂
                          (batchDispatch {e = e} nid vals fin sched st m))))
                        (proj₂ (proj₂ (proj₂
                          (batchDispatch {e = e} nid vals fin sched st m))))
batchDispatch-keeps {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done))
  with w ≟ᵗ s
... | no  _    = keeps-refl _ _
... | yes refl = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (batchSync-st false _ _)) = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st nothing                        = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (cell-st _))             = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (take-st _))             = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (mergeAll-st _ _ _ _))   = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (switch-st _ _))         = keeps-refl _ _
batchDispatch-keeps nid vals fin sched st (just (exhaust-st _ _))        = keeps-refl _ _

-- the flattener's wrap marks its own node done
thruWrap-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                   (op : AllOp) (nid : NodeId) (fin : Bool)
                   (sched′ : Sched Γ) (st′ : EvalSt e)
               → Keeps {e = e} sched′ st′
                   (proj₁ (proj₂ (thruWrap {e = e} op nid fin (sched′ , st′))))
                   (proj₂ (proj₂ (thruWrap {e = e} op nid fin (sched′ , st′))))
thruWrap-keeps op nid false sched′ st′ = keeps-refl _ _
thruWrap-keeps mergeAllᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = keeps-refl _ _
... | just (cell-st _)           = keeps-refl _ _
... | just (take-st _)           = keeps-refl _ _
... | just (batchSync-st _ _ _)  = keeps-refl _ _
... | just (switch-st _ _)       = keeps-refl _ _
... | just (exhaust-st _ _)      = keeps-refl _ _
... | nothing                    = keeps-refl _ _
thruWrap-keeps switchᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st _ _)       = keeps-refl _ _
... | just (cell-st _)           = keeps-refl _ _
... | just (take-st _)           = keeps-refl _ _
... | just (batchSync-st _ _ _)  = keeps-refl _ _
... | just (mergeAll-st _ _ _ _) = keeps-refl _ _
... | just (exhaust-st _ _)      = keeps-refl _ _
... | nothing                    = keeps-refl _ _
thruWrap-keeps exhaustᵒ nid true sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st _ _)      = keeps-refl _ _
... | just (cell-st _)           = keeps-refl _ _
... | just (take-st _)           = keeps-refl _ _
... | just (batchSync-st _ _ _)  = keeps-refl _ _
... | just (mergeAll-st _ _ _ _) = keeps-refl _ _
... | just (switch-st _ _)       = keeps-refl _ _
... | nothing                    = keeps-refl _ _

-- the share's dying mark, its closure, and its retirement touch neither
-- field
shareSpend-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                     (i : Fin n) (sched : Sched Γ) (st : EvalSt e)
                 → Keeps {e = e} sched st sched (shareSpend {e = e} i st)
shareSpend-keeps i sched st = keeps-refl _ _

shareDying-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                     (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
                 → Keeps {e = e} sched st sched (shareDying {e = e} i fin st)
shareDying-keeps i false sched st = keeps-refl _ _
shareDying-keeps i true  sched st = keeps-refl _ _

shareFinish-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                      (i : Fin n) (fin : Bool)
                      (r : Stream Γ t × Sched Γ × EvalSt e)
                  → Keeps {e = e} (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                      (proj₁ (proj₂ (shareFinish {e = e} i fin r)))
                      (proj₂ (proj₂ (shareFinish {e = e} i fin r)))
shareFinish-keeps i false r                 = keeps-refl _ _
shareFinish-keeps i true  (emits , sc , st) = keeps-refl _ _

-- THE EIGHTEEN-MEMBER INDUCTION, AND WHAT IT DESCENDS ON.  Every clause
-- below matches a constructor of the relation its member is stated over
-- and recurses on that constructor's own sub-derivations, so the block
-- peels no edge and carries no counter.  That is the one reading `make
-- recursion-cover` takes on the source's word, so it is written out
-- rather than left unlisted, and the check fails the day the names stop
-- naming a cycle.
-- STRUCTURAL SCC: subscribeE-keeps subscribeSharedSlot-keeps subscribeInner-keeps subscribeAll-keeps stepFrame-keeps pushBurst-keeps pushSegs-keeps thruWalk-keeps thruConsume-keeps innerReact-keeps innerFinish-keeps mergeAllDrain-keeps sharedConnect-keeps foldPath-keeps foldVSegs-keeps dispatchShare-keeps shareWalk-keeps shareGo-keeps
subscribeE-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                     {sched sched₂ : Sched Γ} {st st₁ : EvalSt e}
                     {segs : Segs Γ u t}
                 → subscribeE⇓ {e = e} b κ now sched st (segs , sched₂ , st₁)
                 → Keeps {e = e} sched st sched₂ st₁

pushBurst-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                    {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {burst}
                    {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
                → pushBurst⇓ {e = e} now fr κ burst sched st (out , sched₂ , st₁)
                → Keeps {e = e} sched st sched₂ st₁

pushSegs-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {segs}
                   {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
               → pushSegs⇓ {e = e} now fr κ segs sched st (out , sched₂ , st₁)
               → Keeps {e = e} sched st sched₂ st₁

stepFrame-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                    {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {vals fin}
                    {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {segs fin′}
                → stepFrame⇓ {e = e} now fr κ vals fin sched st
                    (segs , fin′ , sched₁ , st₁)
                → Keeps {e = e} sched st sched₁ st₁

subscribeAll-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                       {op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
                       {κ : Path Γ lo u t} {now}
                       {sched sched₂ : Sched Γ} {st st₁ : EvalSt e}
                       {segs : Segs Γ u t}
                   → subscribeAll⇓ {e = e} op ns b κ now sched st
                       (segs , sched₂ , st₁)
                   → Keeps {e = e} sched st sched₂ st₁

subscribeInner-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         {op} {allNid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                         {st st′ : EvalSt e} {inst segs done}
                     → subscribeInner⇓ {e = e} op allNid κ now o sched st
                         (inst , segs , done , sched′ , st′)
                     → Keeps {e = e} sched st sched′ st′

thruWalk-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {op} {nid} {κ : Path Γ lo u t} {now}
                   {vals : List (Val Γ (obs u))} {sched sched′ : Sched Γ}
                   {st st′ : EvalSt e} {out}
               → thruWalk⇓ {e = e} op nid κ now vals sched st (out , sched′ , st′)
               → Keeps {e = e} sched st sched′ st′

thruConsume-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                      {op} {nid} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                      {st st′ : EvalSt e} {out}
                  → thruConsume⇓ {e = e} op nid κ now o sched st (out , sched′ , st′)
                  → Keeps {e = e} sched st sched′ st′

mergeAllDrain-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                        {allNid} {κ : Path Γ lo s t} {now} {lim act od q}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                        {segs act′ q′}
                    → mergeAllDrain⇓ {e = e} allNid κ now lim act od q sched st
                        (segs , act′ , q′ , sched′ , st′)
                    → Keeps {e = e} sched st sched′ st′

innerFinish-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                      {op} {allNid inst} {κ : Path Γ lo s t} {now}
                      {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                      {st st′ : EvalSt e} {m} {segs fin}
                  → innerFinish⇓ {e = e} op allNid inst κ now vals sched st m
                      (segs , fin , sched′ , st′)
                  → Keeps {e = e} sched st sched′ st′

innerReact-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     {op} {allNid inst} {κ : Path Γ lo s t} {now}
                     {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {alive} {segs fin}
                 → innerReact⇓ {e = e} op allNid inst κ now vals sched st alive
                     (segs , fin , sched′ , st′)
                 → Keeps {e = e} sched st sched′ st′

sharedConnect-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                        {i} {d} {κ : Path Γ lo _ t} {below} {now}
                        {sched sched₁ : Sched Γ} {st st₂ : EvalSt e}
                        {segs : Segs Γ _ t}
                    → sharedConnect⇓ {e = e} i d κ below now sched st
                        (segs , sched₁ , st₂)
                    → Keeps {e = e} sched st sched₁ st₂

subscribeSharedSlot-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                              {i} {d} {κ : Path Γ lo _ t} {below} {now}
                              {sched sched₁ : Sched Γ} {st st₂ : EvalSt e}
                              {segs : Segs Γ _ t}
                          → subscribeSharedSlot⇓ {e = e} i d κ below now sched st
                              (segs , sched₁ , st₂)
                          → Keeps {e = e} sched st sched₁ st₂

-- THE FOLD SIDE, WHICH THE CONNECT DREW INTO THIS CYCLE.  A fold walks
-- a registered chain sinkward and meets a frame step on the way, so it
-- reaches the subscribe side; the connect reaches it back.  Neither
-- direction connects anything: the root assembles a burst, the sink
-- transposes a delivery, and the writes on the way are to the node
-- table, the live set and the registry.
foldPath-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now} {vals} {fin}
                   {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
               → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched₁ , st₁)
               → Keeps {e = e} sched st sched₁ st₁

foldVSegs-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                    {κ : Path Γ lo u t} {now} {segs} {fin}
                    {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
                → foldVSegs⇓ {e = e} now κ segs fin sched st (emits , sched₁ , st₁)
                → Keeps {e = e} sched st sched₁ st₁

dispatchShare-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                        {i} {below} {now} {vals} {fin}
                        {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
                    → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st
                        (emits , sched₁ , st₁)
                    → Keeps {e = e} sched st sched₁ st₁

shareWalk-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    {i} {now} {vals} {fin}
                    {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
                → shareWalk⇓ {e = e} now i vals fin sched st (emits , sched₁ , st₁)
                → Keeps {e = e} sched st sched₁ st₁

shareGo-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                  {i} {now} {v} {fin} {ps}
                  {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {emits}
              → shareGo⇓ {e = e} {lo = lo} now i v fin ps sched st
                  (emits , sched₁ , st₁)
              → Keeps {e = e} sched st sched₁ st₁

subscribeE-keeps (subs-floor _)              = keeps-refl _ _
subscribeE-keeps (subs-shared _ slot)        = subscribeSharedSlot-keeps slot
subscribeE-keeps (subs-hot-done _ _ _)       = keeps-refl _ _
subscribeE-keeps (subs-hot-live _ _ _ _)     = keeps-refl _ _
subscribeE-keeps (subs-cold-sync _ _)        = keeps-refl _ _
subscribeE-keeps (subs-cold-async _ _ _ _ _) = keeps-refl _ _
subscribeE-keeps subs-of                     = keeps-refl _ _
subscribeE-keeps subs-empty                  = keeps-refl _ _
subscribeE-keeps (subs-take-zero _)          = keeps-refl _ _
subscribeE-keeps (subs-map sub push) =
  keeps-trans (subscribeE-keeps sub) (pushSegs-keeps push)
subscribeE-keeps (subs-take-suc _ refl sub push) =
  keeps-trans (subscribeE-keeps sub) (pushSegs-keeps push)
subscribeE-keeps (subs-batchSync refl sub push) =
  keeps-trans (subscribeE-keeps sub) (pushSegs-keeps push)
subscribeE-keeps (subs-scan refl sub push) =
  keeps-trans (subscribeE-keeps sub) (pushSegs-keeps push)
subscribeE-keeps (subs-merge-all sa)         = subscribeAll-keeps sa
subscribeE-keeps (subs-switch-all sa)        = subscribeAll-keeps sa
subscribeE-keeps (subs-exhaust-all sa)       = subscribeAll-keeps sa
subscribeE-keeps (subs-μ sub)                = subscribeE-keeps sub
subscribeE-keeps (subs-defer refl _ _ _)     = keeps-refl _ _
subscribeE-keeps (subs-mint _ sub)           = subscribeE-keeps sub

pushBurst-keeps push-nil              = keeps-refl _ _
pushBurst-keeps (push-cons _ st rest) =
  keeps-trans (stepFrame-keeps st) (pushBurst-keeps rest)

pushSegs-keeps psegs-nil          = keeps-refl _ _
pushSegs-keeps (psegs-cons pb ps) =
  keeps-trans (pushBurst-keeps pb) (pushSegs-keeps ps)

stepFrame-keeps step-map       = keeps-refl _ _
stepFrame-keeps (step-batchSync {nid = nid} {vals = vals} {fin} {sched} {st}) =
  batchDispatch-keeps nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-keeps (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scanDispatch-keeps fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-keeps (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) =
  takeDispatch-keeps nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-keeps (step-from-inner r) = innerReact-keeps r
stepFrame-keeps (step-thru-outer {op = op} {nid} {fin = fin} w) =
  keeps-trans (thruWalk-keeps w) (thruWrap-keeps op nid fin _ _)

subscribeAll-keeps (sub-all refl sub push) =
  keeps-trans (subscribeE-keeps sub) (pushSegs-keeps push)

subscribeInner-keeps (inner refl sub _) = subscribeE-keeps sub

thruWalk-keeps walk-nil        = keeps-refl _ _
thruWalk-keeps (walk-cons c w) =
  keeps-trans (thruConsume-keeps c) (thruWalk-keeps w)

thruConsume-keeps (consume-all-sub _ _ si r fv)  =
  keeps-trans (subscribeInner-keeps si)
    (keeps-trans (innerReact-keeps r) (foldVSegs-keeps fv))
thruConsume-keeps (consume-all-enqueue _ _) = keeps-refl _ _
thruConsume-keeps (consume-all-nil _)       = keeps-refl _ _
thruConsume-keeps
  (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl _ si r fv) =
  keeps-trans (switchKill-keeps cur sched₀ st₀ kl)
    (keeps-trans (subscribeInner-keeps si)
      (keeps-trans (innerReact-keeps r) (foldVSegs-keeps fv)))
thruConsume-keeps (consume-switch-nil _)     = keeps-refl _ _
thruConsume-keeps (consume-exhaust-sub _ si r fv) =
  keeps-trans (subscribeInner-keeps si)
    (keeps-trans (innerReact-keeps r) (foldVSegs-keeps fv))
thruConsume-keeps (consume-exhaust-nil _)    = keeps-refl _ _

mergeAllDrain-keeps drain-nil            = keeps-refl _ _
mergeAllDrain-keeps (drain-no-room _)    = keeps-refl _ _
mergeAllDrain-keeps (drain-room _ si dr) =
  keeps-trans (subscribeInner-keeps si) (mergeAllDrain-keeps dr)

innerReact-keeps react-false      = keeps-refl _ _
innerReact-keeps (react-alive _)  = keeps-refl _ _
innerReact-keeps (react-dead _ f) = innerFinish-keeps f

innerFinish-keeps (finish-all-drain dr)   = mergeAllDrain-keeps dr
innerFinish-keeps (finish-switch-clear _) = keeps-refl _ _
innerFinish-keeps finish-exhaust-clear    = keeps-refl _ _
innerFinish-keeps (finish-nil _)          = keeps-refl _ _

-- THE ONE EDGE THAT MOVES A FIELD.  The connect conses its own slot's
-- index onto the connected set and registers the chain that triggered
-- it, both in the state it hands the definition's subscription; the
-- cons is what the candidate's descent is paid out of.
sharedConnect-keeps (connect-live {i = i} {sched = sched} {st = st} refl sub _ fv) =
  keeps-trans (keeps-trans (keeps-cons _ _ _) (subscribeE-keeps sub))
              (foldVSegs-keeps fv)
sharedConnect-keeps (connect-died {i = i} {sched = sched} {st = st} refl sub _ fv) =
  keeps-trans (keeps-trans (keeps-cons _ _ _) (subscribeE-keeps sub))
              (foldVSegs-keeps fv)

subscribeSharedSlot-keeps (slot-spent _)        = keeps-refl _ _
subscribeSharedSlot-keeps (slot-join _ _ _)     = keeps-refl _ _
subscribeSharedSlot-keeps (slot-connect _ _ sc) = sharedConnect-keeps sc

foldPath-keeps fold-root        = keeps-refl _ _
foldPath-keeps (fold-sink d)    = dispatchShare-keeps d
foldPath-keeps (fold-step sf r) =
  keeps-trans (stepFrame-keeps sf) (foldVSegs-keeps r)

foldVSegs-keeps (segs-nil f)    = foldPath-keeps f
foldVSegs-keeps (segs-last f)   = foldPath-keeps f
foldVSegs-keeps (segs-more f r) =
  keeps-trans (foldPath-keeps f) (foldVSegs-keeps r)

dispatchShare-keeps (disp {i = i} {fin = fin} {sched = sched} {st = st} w) =
  keeps-trans (keeps-trans (shareDying-keeps i fin sched st) (shareWalk-keeps w))
              (shareFinish-keeps i fin _)

shareWalk-keeps walk-nil        = keeps-refl _ _
shareWalk-keeps (walk-end g)    = shareGo-keeps g
shareWalk-keeps (walk-more g w) =
  keeps-trans (shareGo-keeps g) (shareWalk-keeps w)

shareGo-keeps go-nil          = keeps-refl _ _
shareGo-keeps (go-cut _ g)    = shareGo-keeps g
shareGo-keeps (go-live _ f g) =
  keeps-trans (foldPath-keeps f) (shareGo-keeps g)
