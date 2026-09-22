-- THE NODE COUNTER ONLY EVER GOES UP, PROVEN OVER THE SUBSCRIBE CYCLE.
-- This is the companion the preservation statement cannot do without.
-- Preservation is stated at a FLOOR, so each recursive premise is the
-- same statement at the same floor -- but a premise that runs at a mint
-- the previous premise handed back needs that mint's counter to still
-- be above the floor, and nothing but monotonicity says so.  It is its
-- own module because it is its own mutual block: the two families
-- recurse over the same relations and neither is a member of the
-- other's cycle.
--
-- EVERY CLAUSE IS ONE OF THREE SHAPES, WHICH IS WHY THE BLOCK IS LONG
-- RATHER THAN HARD.  An arm that hands its mint back untouched is
-- reflexivity; an arm that threads through premises is transitivity
-- along them; an arm that ALLOCATES A NODE advances the counter by one
-- and pays the step.  An arm that allocates at ANY OTHER KEY is
-- reflexivity too, and it is reflexivity by REDUCTION rather than by
-- argument: the keyed ledger's setter leaves every other key pointwise
-- alone, so the off-diagonal writes simply are not there to be argued
-- about.
module Rx.Evaluator.Freshness.Mono where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; obs; FnClo; _×ᵗ_; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; Stream;
  switchKill; scanDispatch; takeDispatch; thruWrap; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; lookupNode; takeVals)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; pushBurst⇓;
  subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓;
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
  slot-spent; slot-join; slot-connect)

-- the switch's cut sweeps live registrations, never the node counter
switchKill-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                    {sched₁ st₁}
                → switchKill {e = e} cur sched st ≡ (sched₁ , st₁)
                → nodeCt sched ≤ nodeCt sched₁
switchKill-node nothing  sched st refl = ≤-refl
switchKill-node (just v) sched st refl = ≤-refl

-- the fold's dispatch rewrites its own node and nothing else
scanDispatch-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                      (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                      (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                  → nodeCt sched
                    ≤ nodeCt (proj₁ (proj₂ (proj₂
                        (scanDispatch {e = e} fn nid vals fin sched st m))))
scanDispatch-node {u = u} fn nid vals fin sched st (just (cell-st {w} a))
  with w ≟ᵗ u
... | no  _    = ≤-refl
... | yes refl = ≤-refl
scanDispatch-node fn nid vals fin sched st nothing                     = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (take-st _))          = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (batchSync-st _))     = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (switch-st _ _))      = ≤-refl
scanDispatch-node fn nid vals fin sched st (just (exhaust-st _ _))     = ≤-refl

-- the truncation's cut sweeps registrations, never the node counter
takeDispatch-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                      (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                  → nodeCt sched
                    ≤ nodeCt (proj₁ (proj₂ (proj₂
                        (takeDispatch {e = e} nid vals fin sched st m))))
takeDispatch-node nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = ≤-refl
... | false = ≤-refl
takeDispatch-node nid vals fin sched st nothing                      = ≤-refl
takeDispatch-node nid vals fin sched st (just (cell-st _))           = ≤-refl
takeDispatch-node nid vals fin sched st (just (batchSync-st _))      = ≤-refl
takeDispatch-node nid vals fin sched st (just (mergeAll-st _ _ _ _)) = ≤-refl
takeDispatch-node nid vals fin sched st (just (switch-st _ _))       = ≤-refl
takeDispatch-node nid vals fin sched st (just (exhaust-st _ _))      = ≤-refl

-- the flattener's wrap marks its own node done and hands the walk's
-- mint straight back
thruWrap-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                  (op : AllOp) (nid : NodeId) (fin : Bool)
                  (vs : List (Val Γ u))
                  (sched′ : Sched Γ) (st′ : EvalSt e)
              → nodeCt sched′
                ≤ nodeCt (proj₁ (proj₂ (proj₂
                    (thruWrap {e = e} op nid fin (vs , sched′ , st′)))))
thruWrap-node op nid false vs sched′ st′ = ≤-refl
thruWrap-node mergeAllᵒ nid true vs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-node switchᵒ nid true vs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st _ _)       = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-node exhaustᵒ nid true vs sched′ st′
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st _ _)      = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | nothing                    = ≤-refl

subscribeE-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                    {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                    {sched sched₂ : Sched Γ} {st st₁ : EvalSt e}
                    {burst : Stream Γ u} {roots : Stream Γ t}
                → subscribeE⇓ {e = e} b κ now sched st (burst , roots , sched₂ , st₁)
                → nodeCt sched ≤ nodeCt sched₂

pushBurst-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {burst}
                   {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out} {roots : Stream Γ t}
               → pushBurst⇓ {e = e} now fr κ burst sched st (out , roots , sched₂ , st₁)
               → nodeCt sched ≤ nodeCt sched₂

stepFrame-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {now} {vals fin}
                   {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {vals′ fin′}
                   {roots : Stream Γ t}
               → stepFrame⇓ {e = e} now fr κ vals fin sched st
                   (vals′ , fin′ , roots , sched₁ , st₁)
               → nodeCt sched ≤ nodeCt sched₁

subscribeAll-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                      {op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
                      {κ : Path Γ lo u t} {now}
                      {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                      {roots : Stream Γ t}
                  → subscribeAll⇓ {e = e} op ns b κ now sched st
                      (burst , roots , sched₂ , st₁)
                  → nodeCt sched ≤ nodeCt sched₂

subscribeInner-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                        {op} {allNid} {κ : Path Γ lo u t} {now}
                        {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                        {st st′ : EvalSt e} {inst vs done}
                        {roots : Stream Γ t}
                    → subscribeInner⇓ {e = e} op allNid κ now o sched st
                        (inst , vs , done , roots , sched′ , st′)
                    → nodeCt sched ≤ nodeCt sched′

thruWalk-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {op} {nid} {κ : Path Γ lo u t} {now}
                  {vals : List (Val Γ (obs u))} {sched sched′ : Sched Γ}
                  {st st′ : EvalSt e} {vs} {roots : Stream Γ t}
              → thruWalk⇓ {e = e} op nid κ now vals sched st (vs , roots , sched′ , st′)
              → nodeCt sched ≤ nodeCt sched′

thruConsume-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {op} {nid} {κ : Path Γ lo u t} {now}
                     {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {vs} {roots : Stream Γ t}
                 → thruConsume⇓ {e = e} op nid κ now o sched st (vs , roots , sched′ , st′)
                 → nodeCt sched ≤ nodeCt sched′

mergeAllDrain-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                       {allNid} {κ : Path Γ lo s t} {now} {lim act od q}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                       {vs act′ q′} {roots : Stream Γ t}
                   → mergeAllDrain⇓ {e = e} allNid κ now lim act od q sched st
                       (vs , act′ , q′ , roots , sched′ , st′)
                   → nodeCt sched ≤ nodeCt sched′

innerFinish-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     {op} {allNid inst} {κ : Path Γ lo s t} {now}
                     {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {m} {vs fin} {roots : Stream Γ t}
                 → innerFinish⇓ {e = e} op allNid inst κ now vals sched st m
                     (vs , fin , roots , sched′ , st′)
                 → nodeCt sched ≤ nodeCt sched′

innerReact-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                    {op} {allNid inst} {κ : Path Γ lo s t} {now}
                    {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                    {st st′ : EvalSt e} {alive} {vs fin} {roots : Stream Γ t}
                → innerReact⇓ {e = e} op allNid inst κ now vals sched st alive
                    (vs , fin , roots , sched′ , st′)
                → nodeCt sched ≤ nodeCt sched′

sharedConnect-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                       {i} {d} {κ : Path Γ lo _ t} {below} {now}
                       {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                       {roots : Stream Γ t}
                   → sharedConnect⇓ {e = e} i d κ below now sched st
                       (burst , roots , sched₁ , st₂)
                   → nodeCt sched ≤ nodeCt sched₁

subscribeSharedSlot-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                             {i} {d} {κ : Path Γ lo _ t} {below} {now}
                             {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                             {roots : Stream Γ t}
                         → subscribeSharedSlot⇓ {e = e} i d κ below now sched st
                             (burst , roots , sched₁ , st₂)
                         → nodeCt sched ≤ nodeCt sched₁

subscribeE-mono (subs-floor _)                = ≤-refl
subscribeE-mono (subs-shared _ slot)          = subscribeSharedSlot-mono slot
subscribeE-mono (subs-hot-done _ _ _)         = ≤-refl
subscribeE-mono (subs-hot-live _ _ _ _)       = ≤-refl
subscribeE-mono (subs-cold-sync _ _)          = ≤-refl
subscribeE-mono (subs-cold-async _ _ _ _ _)   = ≤-refl
subscribeE-mono subs-of                       = ≤-refl
subscribeE-mono subs-empty                    = ≤-refl
subscribeE-mono (subs-take-zero _)            = ≤-refl
subscribeE-mono (subs-map sub push) =
  ≤-trans (subscribeE-mono sub) (pushBurst-mono push)
subscribeE-mono (subs-take-suc _ refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)
subscribeE-mono (subs-batchSync refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)
subscribeE-mono (subs-scan refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)
subscribeE-mono (subs-merge-all sa)           = subscribeAll-mono sa
subscribeE-mono (subs-switch-all sa)          = subscribeAll-mono sa
subscribeE-mono (subs-exhaust-all sa)         = subscribeAll-mono sa
subscribeE-mono (subs-μ sub)                  = subscribeE-mono sub
subscribeE-mono (subs-defer refl _ _ _)       = n≤1+n _
subscribeE-mono (subs-mint _ sub)             = subscribeE-mono sub

pushBurst-mono push-nil              = ≤-refl
pushBurst-mono (push-cons _ st rest) = ≤-trans (stepFrame-mono st) (pushBurst-mono rest)

stepFrame-mono step-map              = ≤-refl
stepFrame-mono step-batchSync        = ≤-refl
stepFrame-mono (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scanDispatch-node fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-mono (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) =
  takeDispatch-node nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-mono (step-from-inner r)   = innerReact-mono r
stepFrame-mono (step-thru-outer {op = op} {nid} {fin = fin} w) =
  ≤-trans (thruWalk-mono w) (thruWrap-node op nid fin _ _ _)

subscribeAll-mono (sub-all refl sub push) =
  ≤-trans (≤-trans (n≤1+n _) (subscribeE-mono sub)) (pushBurst-mono push)

subscribeInner-mono (inner refl sub _) = ≤-trans (n≤1+n _) (subscribeE-mono sub)

thruWalk-mono walk-nil        = ≤-refl
thruWalk-mono (walk-cons c w) = ≤-trans (thruConsume-mono c) (thruWalk-mono w)

thruConsume-mono (consume-all-sub _ _ si)  = subscribeInner-mono si
thruConsume-mono (consume-all-enqueue _ _) = ≤-refl
thruConsume-mono (consume-all-nil _)       = ≤-refl
thruConsume-mono (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl si) =
  ≤-trans (switchKill-node cur sched₀ st₀ kl) (subscribeInner-mono si)
thruConsume-mono (consume-switch-nil _)     = ≤-refl
thruConsume-mono (consume-exhaust-sub _ si) = subscribeInner-mono si
thruConsume-mono (consume-exhaust-nil _)    = ≤-refl

mergeAllDrain-mono drain-nil            = ≤-refl
mergeAllDrain-mono (drain-no-room _)    = ≤-refl
mergeAllDrain-mono (drain-room _ si dr) =
  ≤-trans (subscribeInner-mono si) (mergeAllDrain-mono dr)

innerReact-mono react-false      = ≤-refl
innerReact-mono (react-alive _)  = ≤-refl
innerReact-mono (react-dead _ f) = innerFinish-mono f

innerFinish-mono (finish-all-drain dr)   = mergeAllDrain-mono dr
innerFinish-mono (finish-switch-clear _) = ≤-refl
innerFinish-mono finish-exhaust-clear    = ≤-refl
innerFinish-mono (finish-nil _)          = ≤-refl

sharedConnect-mono (connect-live refl sub _) = subscribeE-mono sub
sharedConnect-mono (connect-died refl sub _) = subscribeE-mono sub

subscribeSharedSlot-mono (slot-spent _)        = ≤-refl
subscribeSharedSlot-mono (slot-join _ _ _)     = ≤-refl
subscribeSharedSlot-mono (slot-connect _ _ sc) = sharedConnect-mono sc
