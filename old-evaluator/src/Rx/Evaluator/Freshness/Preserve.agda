-- A SUBSCRIPTION WRITES NO NODE BELOW THE COUNTER IT STARTED AT, PROVEN
-- OVER THE TWELVE RELATIONS ITS CYCLE PASSES THROUGH.  The floor is an
-- argument rather than a reading of the scheduler, so every recursive
-- premise is this same statement at the same floor; what an advanced
-- premise costs is re-establishing the floor hypothesis, and that is
-- what the companion monotonicity family is spent on.
--
-- THE ONLY NODE A SUBSCRIPTION WRITES WITHOUT MINTING IT IS ONE ITS
-- CALLER NAMED, WHICH IS WHY THE FRAME-LEVEL MEMBERS CARRY A
-- HYPOTHESIS AND THE ROOT DOES NOT.  A frame is stepped only by the
-- burst push directly above it, never through an inherited
-- continuation, so at every site inside the subscribe cycle the frame
-- was built out of the counter one line earlier and the hypothesis
-- discharges to the floor bound already in hand.  The members reached
-- through a flattener take the operator's own identifier the same way.
--
-- EVERY CLAUSE IS REFLEXIVITY, A COMPOSITION, OR A WRITE AT OR ABOVE
-- THE FLOOR.  The arms that touch no table are the first, the arms
-- that thread premises are the second, and the five writers -- the
-- fold's dispatch, the truncation's, the flattener's wrap, the merge's
-- bump and the plain install -- are the third.  Nothing here is
-- delicate; it is long because the relation is wide.
module Rx.Evaluator.Freshness.Preserve where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; obs; Fn; _×ᵗ_; _≟ᵗ_)
open import Rx.Prim using (InstEvent)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ;
  switchKill; scanDispatch; takeDispatch; thruWrap; mergeAllBump; scanVals; takeVals; scan-st;
  take-st; mergeAll-st; switch-st; exhaust-st; lookupNode)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; pushBurst⇓;
  subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero; subs-take-suc;
  subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer;
  inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-from-inner; step-thru-outer;
  push-nil; push-cons; sub-all; connect-live; connect-died;
  slot-spent; slot-join; slot-connect)
open import Rx.Evaluator.Freshness using (PreservedBelow; FrameAbove;
  pres-same; pres-trans; pres-write)
open import Rx.Evaluator.Freshness.Mono using (subscribeE-mono; stepFrame-mono; subscribeInner-mono; thruConsume-mono; switchKill-node)

-- the fold's dispatch rewrites its own node and nothing else
scan-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {f}
              (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
              (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
          → f ≤ nid
          → PreservedBelow f st (proj₂ (proj₂ (proj₂ (proj₂
              (scanDispatch {e = e} fn nid vals fin sched st m)))))
scan-pres {u = u} fn nid vals fin sched st (just (scan-st {w} a)) f≤nid
  with w ≟ᵗ u
... | no  _    = pres-same _ _ refl
... | yes refl = pres-write _ _ (scan-st (proj₂ (scanVals fn a vals))) refl f≤nid
scan-pres fn nid vals fin sched st nothing                    f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (take-st _))         f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (switch-st _ _))     f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (exhaust-st _ _))    f≤nid = pres-same _ _ refl

-- the truncation's cut severs registrations and rewrites its own node
take-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {f}
              (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
          → f ≤ nid
          → PreservedBelow f st (proj₂ (proj₂ (proj₂ (proj₂
              (takeDispatch {e = e} nid vals fin sched st m)))))
take-pres nid vals fin sched st (just (take-st k)) f≤nid
  with proj₂ (proj₂ (takeVals k vals))
... | true  = pres-write _ _ (take-st zero) refl f≤nid
... | false = pres-write _ _ (take-st (proj₁ (proj₂ (takeVals k vals)))) refl f≤nid
take-pres nid vals fin sched st nothing                     f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (scan-st _))          f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (mergeAll-st _ _ _ _)) f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (switch-st _ _))      f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (exhaust-st _ _))     f≤nid = pres-same _ _ refl

-- the flattener's wrap marks its own node done
wrap-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {f}
              (op : AllOp) (nid : NodeId) (fin : Bool)
              (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
              (sched′ : Sched Γ) (st′ : EvalSt e)
          → f ≤ nid
          → PreservedBelow f st′ (proj₂ (proj₂ (proj₂ (proj₂
              (thruWrap {e = e} op nid fin (vs , bs , sched′ , st′))))))
wrap-pres op nid false vs bs sched′ st′ f≤nid = pres-same _ _ refl
wrap-pres mergeAllᵒ nid true vs bs sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st lim act q _) = pres-write _ _ (mergeAll-st lim act q true) refl f≤nid
... | just (scan-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (switch-st _ _)           = pres-same _ _ refl
... | just (exhaust-st _ _)          = pres-same _ _ refl
... | nothing                        = pres-same _ _ refl
wrap-pres switchᵒ nid true vs bs sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur _)         = pres-write _ _ (switch-st cur true) refl f≤nid
... | just (scan-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (mergeAll-st _ _ _ _)     = pres-same _ _ refl
... | just (exhaust-st _ _)          = pres-same _ _ refl
... | nothing                        = pres-same _ _ refl
wrap-pres exhaustᵒ nid true vs bs sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act _)        = pres-write _ _ (exhaust-st act true) refl f≤nid
... | just (scan-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (mergeAll-st _ _ _ _)     = pres-same _ _ refl
... | just (switch-st _ _)           = pres-same _ _ refl
... | nothing                        = pres-same _ _ refl

-- the merge's bump rewrites its own node, or reads a shape it cannot use
bump-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f} {nid} {done}
              (st : EvalSt e)
          → f ≤ nid
          → PreservedBelow f st
              (record st { nodes = mergeAllBump nid done (EvalSt.nodes st) })
bump-pres {nid = nid} st f≤nid with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st _ _ _ _) = pres-write _ _ _ refl f≤nid
... | just (scan-st _)           = pres-same _ _ refl
... | just (take-st _)           = pres-same _ _ refl
... | just (switch-st _ _)       = pres-same _ _ refl
... | just (exhaust-st _ _)      = pres-same _ _ refl
... | nothing                    = pres-same _ _ refl

-- the switch's cut sweeps registrations, never the table
kill-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f}
              (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
              {closes sched₁ st₁}
          → switchKill {e = e} cur sched st ≡ (closes , sched₁ , st₁)
          → PreservedBelow f st st₁
kill-pres nothing  sched st refl = pres-same _ _ refl
kill-pres (just v) sched st refl = pres-same _ _ refl

subscribeE-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         (f : ℕ) {b : Closed Γ u} {κ : Path Γ lo u t} {id now}
                         {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                     → f ≤ Sched.nextNode sched
                     → subscribeE⇓ {e = e} b κ id now sched st
                         (burst , sched₂ , st₁)
                     → PreservedBelow f st st₁

pushBurst-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                        (f : ℕ) {fr : Frame Γ s u} {κ : Path Γ lo u t}
                        {id now} {ems}
                        {sched sched₂ : Sched Γ} {st st₂ : EvalSt e} {rest}
                    → f ≤ Sched.nextNode sched
                    → FrameAbove f fr
                    → pushBurst⇓ {e = e} id now fr κ ems sched st
                        (rest , sched₂ , st₂)
                    → PreservedBelow f st st₂

stepFrame-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                        (f : ℕ) {fr : Frame Γ s u} {κ : Path Γ lo u t}
                        {id now} {vals : List (Val Γ s)} {fin}
                        {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
                        {vals′ evs fin′}
                    → f ≤ Sched.nextNode sched
                    → FrameAbove f fr
                    → stepFrame⇓ {e = e} id now fr κ vals fin sched st
                        (vals′ , evs , fin′ , sched₁ , st₁)
                    → PreservedBelow f st st₁

subscribeAll-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                           (f : ℕ) {op} {ns : NodeState Γ}
                           {b : Closed Γ (obs u)} {κ : Path Γ lo u t} {id now}
                           {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                       → f ≤ Sched.nextNode sched
                       → subscribeAll⇓ {e = e} op ns b κ id now sched st
                           (burst , sched₂ , st₁)
                       → PreservedBelow f st st₁

subscribeInner-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                             (f : ℕ) {op} {allNid} {κ : Path Γ lo u t} {id now}
                             {o : Val Γ (obs u)}
                             {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                             {inst vs bs done}
                         → f ≤ Sched.nextNode sched
                         → subscribeInner⇓ {e = e} op allNid κ id now o sched st
                             (inst , vs , bs , done , sched′ , st′)
                         → PreservedBelow f st st′

thruWalk-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                       (f : ℕ) {op} {nid} {κ : Path Γ lo u t} {id now} {os}
                       {sched₀ sched₂ : Sched Γ} {st₀ st₂ : EvalSt e} {vs bs}
                   → f ≤ Sched.nextNode sched₀
                   → f ≤ nid
                   → thruWalk⇓ {e = e} op nid κ id now os sched₀ st₀
                       (vs , bs , sched₂ , st₂)
                   → PreservedBelow f st₀ st₂

thruConsume-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                          (f : ℕ) {op} {nid} {κ : Path Γ lo u t} {id now}
                          {o : Val Γ (obs u)}
                          {sched₀ sched₁ : Sched Γ} {st₀ st₁ : EvalSt e} {vs bs}
                      → f ≤ Sched.nextNode sched₀
                      → f ≤ nid
                      → thruConsume⇓ {e = e} op nid κ id now o sched₀ st₀
                          (vs , bs , sched₁ , st₁)
                      → PreservedBelow f st₀ st₁

mergeAllDrain-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                            (f : ℕ) {allNid} {κ : Path Γ lo u t} {id now}
                            {lim act od q}
                            {sched₀ sched₂ : Sched Γ} {st₀ st₂ : EvalSt e}
                            {vs bs act′ q′}
                        → f ≤ Sched.nextNode sched₀
                        → f ≤ allNid
                        → mergeAllDrain⇓ {e = e} allNid κ id now lim act od q
                            sched₀ st₀ (vs , bs , act′ , q′ , sched₂ , st₂)
                        → PreservedBelow f st₀ st₂

innerFinish-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                          (f : ℕ) {op} {allNid} {inst} {κ : Path Γ lo u t}
                          {id now} {vals : List (Val Γ u)}
                          {sched sched′ : Sched Γ} {st st′ : EvalSt e} {ns}
                          {vals′ bs done}
                      → f ≤ Sched.nextNode sched
                      → f ≤ allNid
                      → innerFinish⇓ {e = e} op allNid inst κ id now vals sched st
                          ns (vals′ , bs , done , sched′ , st′)
                      → PreservedBelow f st st′

innerReact-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         (f : ℕ) {op} {allNid} {inst} {κ : Path Γ lo u t}
                         {id now} {vals : List (Val Γ u)}
                         {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {fin}
                         {vals′ evs fin′}
                     → f ≤ Sched.nextNode sched
                     → f ≤ allNid
                     → innerReact⇓ {e = e} op allNid inst κ id now vals sched st
                         fin (vals′ , evs , fin′ , sched₁ , st₁)
                     → PreservedBelow f st st₁

sharedConnect-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                            (f : ℕ) {i} {d} {κ : Path Γ lo _ t} {below}
                            {id now} {sched sched₁ : Sched Γ}
                            {st st₂ : EvalSt e} {burst}
                        → f ≤ Sched.nextNode sched
                        → sharedConnect⇓ {e = e} i d κ below id now sched st
                            (burst , sched₁ , st₂)
                        → PreservedBelow f st st₂

subscribeSharedSlot-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                                  (f : ℕ) {i} {d} {κ : Path Γ lo _ t} {below}
                                  {id now} {sched sched₁ : Sched Γ}
                                  {st st₂ : EvalSt e} {burst}
                              → f ≤ Sched.nextNode sched
                              → subscribeSharedSlot⇓ {e = e} i d κ below id now
                                  sched st (burst , sched₁ , st₂)
                              → PreservedBelow f st st₂

subscribeE-preserves f le (subs-floor _)         = pres-same _ _ refl
subscribeE-preserves f le (subs-shared _ slot)   = subscribeSharedSlot-preserves f le slot
subscribeE-preserves f le (subs-hot-done _ _ _)  = pres-same _ _ refl
subscribeE-preserves f le (subs-hot-live _ _ _)  = pres-same _ _ refl
subscribeE-preserves f le (subs-cold-sync _ _ _) = pres-same _ _ refl
subscribeE-preserves f le (subs-cold-async _ _ _ _) = pres-same _ _ refl
subscribeE-preserves f le (subs-of _)            = pres-same _ _ refl
subscribeE-preserves f le (subs-empty _)         = pres-same _ _ refl
subscribeE-preserves f le (subs-take-zero _ _)   = pres-same _ _ refl
subscribeE-preserves f le (subs-map sub push) =
  pres-trans (subscribeE-preserves f le sub)
             (pushBurst-preserves f (≤-trans le (subscribeE-mono sub)) _ push)
subscribeE-preserves f le (subs-take-suc {k = k} _ refl sub push) =
  pres-trans (pres-trans (pres-write _ _ (take-st (suc k)) refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushBurst-preserves f
                (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push)
subscribeE-preserves f le (subs-scan {seed = seed} refl sub push) =
  pres-trans (pres-trans (pres-write _ _ _ refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushBurst-preserves f
                (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push)
subscribeE-preserves f le (subs-merge-all sa)    = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-switch-all sa)   = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-exhaust-all sa)  = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-μ sub)           = subscribeE-preserves f le sub
subscribeE-preserves f le (subs-defer refl _ _)  = pres-write _ _ _ refl le

pushBurst-preserves f le fa push-nil = pres-same _ _ refl
pushBurst-preserves f le fa (push-cons _ stp rest) =
  pres-trans (stepFrame-preserves f le fa stp)
             (pushBurst-preserves f (≤-trans le (stepFrame-mono stp)) fa rest)

stepFrame-preserves f le fa step-map = pres-same _ _ refl
stepFrame-preserves f le fa
  (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scan-pres fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) fa
stepFrame-preserves f le fa
  (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) =
  take-pres nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) fa
stepFrame-preserves f le fa (step-from-inner r) =
  innerReact-preserves f le (proj₁ fa) r
stepFrame-preserves f le fa
  (step-thru-outer {op = op} {nid} {fin = fin} {vs = vs} {bs} {sched′} {st′} w) =
  pres-trans (thruWalk-preserves f le fa w)
             (wrap-pres op nid fin vs bs sched′ st′ fa)

subscribeAll-preserves f le (sub-all refl sub push) =
  pres-trans (pres-trans (pres-write _ _ _ refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushBurst-preserves f
                (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push)

subscribeInner-preserves f le (inner refl sub _) =
  subscribeE-preserves f (≤-trans le (n≤1+n _)) sub

thruWalk-preserves f le fn walk-nil = pres-same _ _ refl
thruWalk-preserves f le fn (walk-cons c w) =
  pres-trans (thruConsume-preserves f le fn c)
             (thruWalk-preserves f (≤-trans le (thruConsume-mono c)) fn w)

thruConsume-preserves f le fn (consume-all-sub _ _ si) =
  pres-trans (subscribeInner-preserves f le si) (bump-pres _ fn)
thruConsume-preserves f le fn (consume-all-enqueue _ _)  = pres-write _ _ _ refl fn
thruConsume-preserves f le fn (consume-all-nil _)        = pres-same _ _ refl
thruConsume-preserves f le fn
  (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl si) =
  pres-trans (pres-trans (kill-pres cur sched₀ st₀ kl)
                         (subscribeInner-preserves f
                            (≤-trans le (switchKill-node cur sched₀ st₀ kl)) si))
             (pres-write _ _ _ refl fn)
thruConsume-preserves f le fn (consume-switch-nil _)     = pres-same _ _ refl
thruConsume-preserves f le fn (consume-exhaust-sub _ si) =
  pres-trans (subscribeInner-preserves f le si) (pres-write _ _ _ refl fn)
thruConsume-preserves f le fn (consume-exhaust-nil _)    = pres-same _ _ refl

mergeAllDrain-preserves f le fn drain-nil          = pres-same _ _ refl
mergeAllDrain-preserves f le fn (drain-no-room _)  = pres-same _ _ refl
mergeAllDrain-preserves f le fn (drain-room _ si dr) =
  pres-trans (pres-write _ _ _ refl fn)
             (pres-trans (subscribeInner-preserves f le si)
                         (mergeAllDrain-preserves f
                            (≤-trans le (subscribeInner-mono si)) fn dr))

innerFinish-preserves f le fn (finish-all-drain dr) =
  pres-trans (mergeAllDrain-preserves f le fn dr) (pres-write _ _ _ refl fn)
innerFinish-preserves f le fn (finish-switch-clear _) = pres-write _ _ _ refl fn
innerFinish-preserves f le fn finish-exhaust-clear    = pres-write _ _ _ refl fn
innerFinish-preserves f le fn (finish-nil _)          = pres-same _ _ refl

innerReact-preserves f le fn react-false       = pres-same _ _ refl
innerReact-preserves f le fn (react-alive _)   = pres-same _ _ refl
innerReact-preserves f le fn (react-dead _ fi) = innerFinish-preserves f le fn fi

sharedConnect-preserves f le (connect-live sub _) =
  pres-trans (pres-same _ _ refl) (subscribeE-preserves f le sub)
sharedConnect-preserves f le (connect-died sub _) =
  pres-trans (pres-same _ _ refl)
             (pres-trans (subscribeE-preserves f le sub) (pres-same _ _ refl))

subscribeSharedSlot-preserves f le (slot-spent _)        = pres-same _ _ refl
subscribeSharedSlot-preserves f le (slot-join _ _)       = pres-same _ _ refl
subscribeSharedSlot-preserves f le (slot-connect _ _ sc) =
  sharedConnect-preserves f le sc
