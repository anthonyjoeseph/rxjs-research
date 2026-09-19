-- THE NODE COUNTER ONLY EVER GOES UP, PROVEN OVER THE SUBSCRIBE CYCLE.
-- This is the companion the preservation statement cannot do without.
-- Preservation is stated at a FLOOR, so each recursive premise is the
-- same statement at the same floor -- but a premise that runs at a
-- scheduler the previous premise handed back needs that scheduler's
-- counter to still be above the floor, and nothing but monotonicity
-- says so.  It is its own module because it is its own mutual block:
-- the two families recurse over the same twelve relations and neither
-- is a member of the other's cycle.
--
-- EVERY CLAUSE IS ONE OF THREE SHAPES, WHICH IS WHY THE BLOCK IS LONG
-- RATHER THAN HARD.  An arm that hands its scheduler back untouched is
-- reflexivity; an arm that threads through premises is transitivity
-- along them; an arm that ALLOCATES advances the counter by one and
-- pays the step.  The only arms needing anything else are the three
-- whose scheduler comes back out of a helper -- the one-shot burst's
-- mint and the switch's kill -- and both leave the node counter alone,
-- so each is a case split that ends in reflexivity.
module Rx.Evaluator.Freshness.Mono where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; obs; Fn; _×ᵗ_; _≟ᵗ_)
open import Rx.Prim using (Id; InstEvent)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ;
  oneShotBurst; switchKill; scanDispatch; takeDispatch; thruWrap; scan-st; take-st;
  mergeAll-st; switch-st; exhaust-st; lookupNode; takeVals)
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

-- the one-shot burst mints a SOURCE, never a node
oneShot-node : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (id : Id)
                 (sched : Sched Γ) {burst sched₁}
             → oneShotBurst vals id sched ≡ (burst , sched₁)
             → Sched.nextNode sched ≤ Sched.nextNode sched₁
oneShot-node vals id sched refl = ≤-refl

-- the switch's cut sweeps live registrations, never the node counter
switchKill-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                    {closes sched₁ st₁}
                → switchKill {e = e} cur sched st ≡ (closes , sched₁ , st₁)
                → Sched.nextNode sched ≤ Sched.nextNode sched₁
switchKill-node nothing  sched st refl = ≤-refl
switchKill-node (just v) sched st refl = ≤-refl

-- the fold's dispatch rewrites its own node and nothing else
scanDispatch-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                      (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
                      (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                  → Sched.nextNode sched
                    ≤ Sched.nextNode (proj₁ (proj₂ (proj₂ (proj₂
                        (scanDispatch {e = e} fn nid vals fin sched st m)))))
scanDispatch-node {u = u} fn nid vals fin sched st (just (scan-st {w} a))
  with w ≟ᵗ u
... | no  _    = ≤-refl
... | yes refl = ≤-refl
scanDispatch-node fn nid vals fin sched st nothing              = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (take-st _))   = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (switch-st _ _))  = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (exhaust-st _ _)) = ≤-refl

-- the truncation's cut sweeps registrations, never the node counter
takeDispatch-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                      (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                  → Sched.nextNode sched
                    ≤ Sched.nextNode (proj₁ (proj₂ (proj₂ (proj₂
                        (takeDispatch {e = e} nid vals fin sched st m)))))
takeDispatch-node nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = ≤-refl
... | false = ≤-refl
takeDispatch-node nid vals fin sched st nothing                 = ≤-refl
takeDispatch-node nid vals fin sched st (just (scan-st _))      = ≤-refl
takeDispatch-node nid vals fin sched st (just (mergeAll-st _ _ _ _)) = ≤-refl
takeDispatch-node nid vals fin sched st (just (switch-st _ _))   = ≤-refl
takeDispatch-node nid vals fin sched st (just (exhaust-st _ _))  = ≤-refl

-- the flattener's wrap marks its own node done and hands the walk's
-- scheduler straight back
thruWrap-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                  (op : AllOp) (nid : NodeId) (fin : Bool)
                  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
                  (sched′ : Sched Γ) (st′ : EvalSt e)
              → Sched.nextNode sched′
                ≤ Sched.nextNode (proj₁ (proj₂ (proj₂ (proj₂
                    (thruWrap {e = e} op nid fin (vs , bs , sched′ , st′))))))
thruWrap-node op nid false vs bs sched′ st′ = ≤-refl
thruWrap-node mergeAllᵒ nid true vs bs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (scan-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-node switchᵒ nid true vs bs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st _ _)       = ≤-refl
... | just (scan-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-node exhaustᵒ nid true vs bs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st _ _)      = ≤-refl
... | just (scan-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | nothing                    = ≤-refl

subscribeE-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                    {b : Closed Γ u} {κ : Path Γ lo u t} {id now}
                    {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                → subscribeE⇓ {e = e} b κ id now sched st (burst , sched₂ , st₁)
                → Sched.nextNode sched ≤ Sched.nextNode sched₂

pushBurst-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {id now} {burst}
                   {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
               → pushBurst⇓ {e = e} id now fr κ burst sched st (out , sched₂ , st₁)
               → Sched.nextNode sched ≤ Sched.nextNode sched₂

stepFrame-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {id now} {vals fin}
                   {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {vals′ evs fin′}
               → stepFrame⇓ {e = e} id now fr κ vals fin sched st
                   (vals′ , evs , fin′ , sched₁ , st₁)
               → Sched.nextNode sched ≤ Sched.nextNode sched₁

subscribeAll-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                      {op} {ns : NodeState Γ} {b : Closed Γ (obs u)}
                      {κ : Path Γ lo u t} {id now}
                      {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                  → subscribeAll⇓ {e = e} op ns b κ id now sched st
                      (burst , sched₂ , st₁)
                  → Sched.nextNode sched ≤ Sched.nextNode sched₂

subscribeInner-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                        {op} {allNid} {κ : Path Γ lo u t} {id now}
                        {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                        {st st′ : EvalSt e} {inst vs bs done}
                    → subscribeInner⇓ {e = e} op allNid κ id now o sched st
                        (inst , vs , bs , done , sched′ , st′)
                    → Sched.nextNode sched ≤ Sched.nextNode sched′

thruWalk-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {op} {nid} {κ : Path Γ lo u t} {id now}
                  {vals : List (Val Γ (obs u))} {sched sched′ : Sched Γ}
                  {st st′ : EvalSt e} {vs bs}
              → thruWalk⇓ {e = e} op nid κ id now vals sched st
                  (vs , bs , sched′ , st′)
              → Sched.nextNode sched ≤ Sched.nextNode sched′

thruConsume-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {op} {nid} {κ : Path Γ lo u t} {id now}
                     {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {vs bs}
                 → thruConsume⇓ {e = e} op nid κ id now o sched st
                     (vs , bs , sched′ , st′)
                 → Sched.nextNode sched ≤ Sched.nextNode sched′

mergeAllDrain-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                       {allNid} {κ : Path Γ lo s t} {id now} {lim act od q}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                       {vs bs act′ q′}
                   → mergeAllDrain⇓ {e = e} allNid κ id now lim act od q sched st
                       (vs , bs , act′ , q′ , sched′ , st′)
                   → Sched.nextNode sched ≤ Sched.nextNode sched′

innerFinish-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     {op} {allNid inst} {κ : Path Γ lo s t} {id now}
                     {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {m} {vs bs fin}
                 → innerFinish⇓ {e = e} op allNid inst κ id now vals sched st m
                     (vs , bs , fin , sched′ , st′)
                 → Sched.nextNode sched ≤ Sched.nextNode sched′

innerReact-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                    {op} {allNid inst} {κ : Path Γ lo s t} {id now}
                    {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                    {st st′ : EvalSt e} {alive} {vs bs fin}
                → innerReact⇓ {e = e} op allNid inst κ id now vals sched st alive
                    (vs , bs , fin , sched′ , st′)
                → Sched.nextNode sched ≤ Sched.nextNode sched′

sharedConnect-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                       {i} {d} {κ : Path Γ lo _ t} {below} {id now}
                       {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                   → sharedConnect⇓ {e = e} i d κ below id now sched st
                       (burst , sched₁ , st₂)
                   → Sched.nextNode sched ≤ Sched.nextNode sched₁

subscribeSharedSlot-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                             {i} {d} {κ : Path Γ lo _ t} {below} {id now}
                             {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                         → subscribeSharedSlot⇓ {e = e} i d κ below id now sched st
                             (burst , sched₁ , st₂)
                         → Sched.nextNode sched ≤ Sched.nextNode sched₁

subscribeE-mono (subs-floor _)              = ≤-refl
subscribeE-mono (subs-shared _ slot)        = subscribeSharedSlot-mono slot
subscribeE-mono (subs-hot-done _ _ _)       = ≤-refl
subscribeE-mono (subs-hot-live _ _ _)       = ≤-refl
subscribeE-mono (subs-cold-sync {sync = sync} {id = id} {sched = sched} _ _ eq) =
  oneShot-node sync id sched eq
subscribeE-mono (subs-cold-async _ _ _ _)   = ≤-refl
subscribeE-mono (subs-of {id = id} {sched = sched} eq)           = oneShot-node _ id sched eq
subscribeE-mono (subs-empty {u = u} {id = id} {sched = sched} eq) =
  oneShot-node ([] {A = Val _ u}) id sched eq
subscribeE-mono (subs-map sub push)         = ≤-trans (subscribeE-mono sub) (pushBurst-mono push)
subscribeE-mono (subs-take-zero {u = u} {id = id} {sched = sched} _ eq) =
  oneShot-node ([] {A = Val _ u}) id sched eq
subscribeE-mono (subs-take-suc _ refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)
subscribeE-mono (subs-scan refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)
subscribeE-mono (subs-merge-all sa)         = subscribeAll-mono sa
subscribeE-mono (subs-switch-all sa)        = subscribeAll-mono sa
subscribeE-mono (subs-exhaust-all sa)       = subscribeAll-mono sa
subscribeE-mono (subs-μ sub)                = subscribeE-mono sub
subscribeE-mono (subs-defer refl _ _)       = n≤1+n _

pushBurst-mono push-nil            = ≤-refl
pushBurst-mono (push-cons _ st rest) = ≤-trans (stepFrame-mono st) (pushBurst-mono rest)

stepFrame-mono step-map              = ≤-refl
stepFrame-mono (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scanDispatch-node fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-mono (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) =
  takeDispatch-node nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-mono (step-from-inner r)   = innerReact-mono r
stepFrame-mono (step-thru-outer {op = op} {nid} {fin = fin} w) =
  ≤-trans (thruWalk-mono w) (thruWrap-node op nid fin _ _ _ _)

subscribeAll-mono (sub-all refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)

subscribeInner-mono (inner refl sub _) = ≤-trans (n≤1+n _) (subscribeE-mono sub)

thruWalk-mono walk-nil          = ≤-refl
thruWalk-mono (walk-cons c w)   = ≤-trans (thruConsume-mono c) (thruWalk-mono w)

thruConsume-mono (consume-all-sub _ _ si)      = subscribeInner-mono si
thruConsume-mono (consume-all-enqueue _ _)     = ≤-refl
thruConsume-mono (consume-all-nil _)           = ≤-refl
thruConsume-mono (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl si) =
  ≤-trans (switchKill-node cur sched₀ st₀ kl) (subscribeInner-mono si)
thruConsume-mono (consume-switch-nil _)        = ≤-refl
thruConsume-mono (consume-exhaust-sub _ si)    = subscribeInner-mono si
thruConsume-mono (consume-exhaust-nil _)       = ≤-refl

mergeAllDrain-mono drain-nil             = ≤-refl
mergeAllDrain-mono (drain-no-room _)     = ≤-refl
mergeAllDrain-mono (drain-room _ si dr)  =
  ≤-trans (subscribeInner-mono si) (mergeAllDrain-mono dr)

innerReact-mono react-false        = ≤-refl
innerReact-mono (react-alive _)    = ≤-refl
innerReact-mono (react-dead _ f)   = innerFinish-mono f

innerFinish-mono (finish-all-drain dr)     = mergeAllDrain-mono dr
innerFinish-mono (finish-switch-clear _)   = ≤-refl
innerFinish-mono finish-exhaust-clear      = ≤-refl
innerFinish-mono (finish-nil _)            = ≤-refl

sharedConnect-mono (connect-live sub _) = subscribeE-mono sub
sharedConnect-mono (connect-died sub _) = subscribeE-mono sub

subscribeSharedSlot-mono (slot-spent _)        = ≤-refl
subscribeSharedSlot-mono (slot-join _ _)       = ≤-refl
subscribeSharedSlot-mono (slot-connect _ _ sc) = sharedConnect-mono sc
