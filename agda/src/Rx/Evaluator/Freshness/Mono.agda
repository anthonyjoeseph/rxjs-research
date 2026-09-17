-- NO COUNTER EVER GOES DOWN, AT AN ARBITRARY KEY, PROVEN OVER THE
-- SUBSCRIBE CYCLE.
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
-- pays the step at ITS key, which is a step at the asked-for key when
-- the two agree and reflexivity when they do not -- one lemma either
-- way.  The only arms needing anything else are the three whose
-- scheduler comes back out of a helper, the one-shot burst's mint and
-- the switch's kill, and each is a case split that ends in the same
-- two shapes.
module Rx.Evaluator.Freshness.Mono where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Mint using (MintKey; ordinalᵏ; sourceᵏ; nodeᵏ; regᵏ; freshId; next; next-mono)
open import Rx.Exp using (Ctx; Closed; Val; obs; Fn; _×ᵗ_; listᵗ; _≟ᵗ_)
open import Rx.Prim using (Id; InstEvent)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ;
  oneShotBurst; switchKill; scanDispatch; takeDispatch; batchSyncDispatch; thruWrap; cell-st; take-st; batchSync-st;
  mergeAll-st; switch-st; exhaust-st; lookupNode; takeVals)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; pushBurst⇓;
  subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-take-zero; subs-take-suc;
  subs-batchSync; subs-map; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer; subs-mint;
  inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-batchSync; step-from-inner; step-thru-outer;
  push-nil; push-cons; sub-all; connect-live; connect-died;
  slot-spent; slot-join; slot-connect)

-- the one-shot burst mints at the SOURCE key and at no other
oneShot-mint : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (id : Id)
                 (sched : Sched Γ) {burst sched₁}
             → oneShotBurst vals id sched ≡ (burst , sched₁)
             → (k : MintKey)
             → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₁)
oneShot-mint vals id sched refl k = next-mono sourceᵏ k _

-- the switch's cut sweeps live registrations, never the mint
switchKill-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                    {closes sched₁ st₁}
                → switchKill {e = e} cur sched st ≡ (closes , sched₁ , st₁)
                → (k : MintKey)
                → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₁)
switchKill-mint nothing  sched st refl k = ≤-refl
switchKill-mint (just v) sched st refl k = ≤-refl

-- the scanning step rewrites its own cell and nothing else
scanDispatch-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                      (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
                      (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                      (k : MintKey)
                  → freshId k (Sched.mint sched)
                    ≤ freshId k (Sched.mint (proj₁ (proj₂ (proj₂ (proj₂
                        (scanDispatch {e = e} fn nid vals fin sched st m))))))
scanDispatch-mint {u = u} fn nid vals fin sched st (just (cell-st {v} a)) k
  with v ≟ᵗ u
... | no  _    = ≤-refl
... | yes refl = ≤-refl
scanDispatch-mint fn nid vals fin sched st nothing k = ≤-refl
scanDispatch-mint fn nid vals fin sched st (just (take-st _)) k = ≤-refl
scanDispatch-mint fn nid vals fin sched st (just (batchSync-st _)) k = ≤-refl
scanDispatch-mint fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) k = ≤-refl
scanDispatch-mint fn nid vals fin sched st (just (switch-st _ _)) k = ≤-refl
scanDispatch-mint fn nid vals fin sched st (just (exhaust-st _ _)) k = ≤-refl

-- the truncation's cut sweeps registrations, never the mint
takeDispatch-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                      (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                      (k : MintKey)
                  → freshId k (Sched.mint sched)
                    ≤ freshId k (Sched.mint (proj₁ (proj₂ (proj₂ (proj₂
                        (takeDispatch {e = e} nid vals fin sched st m))))))
takeDispatch-mint nid vals fin sched st (just (take-st cap)) k
  with proj₂ (proj₂ (takeVals cap vals))
... | true  = ≤-refl
... | false = ≤-refl
takeDispatch-mint nid vals fin sched st nothing k = ≤-refl
takeDispatch-mint nid vals fin sched st (just (cell-st _)) k = ≤-refl
takeDispatch-mint nid vals fin sched st (just (mergeAll-st _ _ _ _)) k = ≤-refl
takeDispatch-mint nid vals fin sched st (just (switch-st _ _)) k = ≤-refl
takeDispatch-mint nid vals fin sched st (just (exhaust-st _ _)) k = ≤-refl
takeDispatch-mint nid vals fin sched st (just (batchSync-st _)) k = ≤-refl

-- the grouping reads one bit and re-brackets the arriving column; it
-- hands the scheduler straight back, so every arm is `≤-refl`
batchSyncDispatch-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                      (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
                      (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                      (k : MintKey)
                  → freshId k (Sched.mint sched)
                    ≤ freshId k (Sched.mint (proj₁ (proj₂ (proj₂ (proj₂
                        (batchSyncDispatch {e = e} nid vals fin sched st m))))))
batchSyncDispatch-mint nid vals fin sched st (just (batchSync-st _)) k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st nothing k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st (just (cell-st _)) k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st (just (take-st _)) k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st (just (mergeAll-st _ _ _ _)) k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st (just (switch-st _ _)) k = ≤-refl
batchSyncDispatch-mint nid vals fin sched st (just (exhaust-st _ _)) k = ≤-refl

-- the flattener's wrap marks its own node done and hands the walk's
-- scheduler straight back
thruWrap-mint : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                  (op : AllOp) (nid : NodeId) (fin : Bool)
                  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
                  (sched′ : Sched Γ) (st′ : EvalSt e) (k : MintKey)
              → freshId k (Sched.mint sched′)
                ≤ freshId k (Sched.mint (proj₁ (proj₂ (proj₂ (proj₂
                    (thruWrap {e = e} op nid fin (vs , bs , sched′ , st′)))))))
thruWrap-mint op nid false vs bs sched′ st′ k = ≤-refl
thruWrap-mint mergeAllᵒ nid true vs bs sched′ st′ k
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-mint switchᵒ nid true vs bs sched′ st′ k
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st _ _)       = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (exhaust-st _ _)      = ≤-refl
... | nothing                    = ≤-refl
thruWrap-mint exhaustᵒ nid true vs bs sched′ st′ k
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st _ _)      = ≤-refl
... | just (cell-st _)           = ≤-refl
... | just (take-st _)           = ≤-refl
... | just (batchSync-st _)      = ≤-refl
... | just (mergeAll-st _ _ _ _) = ≤-refl
... | just (switch-st _ _)       = ≤-refl
... | nothing                    = ≤-refl

subscribeE-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                    {b : Closed Γ u} {κ : Path Γ lo u t} {id now}
                    {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                → subscribeE⇓ {e = e} b κ id now sched st (burst , sched₂ , st₁)
                → (k : MintKey)
                → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₂)

pushBurst-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {id now} {burst}
                   {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {out}
               → pushBurst⇓ {e = e} id now fr κ burst sched st (out , sched₂ , st₁)
               → (k : MintKey)
               → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₂)

stepFrame-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                   {fr : Frame Γ s u} {κ : Path Γ lo u t} {id now} {vals fin}
                   {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {vals′ evs fin′}
               → stepFrame⇓ {e = e} id now fr κ vals fin sched st
                   (vals′ , evs , fin′ , sched₁ , st₁)
               → (k : MintKey)
               → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₁)

subscribeAll-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                      {op} {ns : NodeState Γ} {b : Closed Γ (obs u)}
                      {κ : Path Γ lo u t} {id now}
                      {sched sched₂ : Sched Γ} {st st₁ : EvalSt e} {burst}
                  → subscribeAll⇓ {e = e} op ns b κ id now sched st
                      (burst , sched₂ , st₁)
                  → (k : MintKey)
                  → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₂)

subscribeInner-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                        {op} {allNid} {κ : Path Γ lo u t} {id now}
                        {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                        {st st′ : EvalSt e} {inst vs bs done}
                    → subscribeInner⇓ {e = e} op allNid κ id now o sched st
                        (inst , vs , bs , done , sched′ , st′)
                    → (k : MintKey)
                    → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

thruWalk-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {op} {nid} {κ : Path Γ lo u t} {id now}
                  {vals : List (Val Γ (obs u))} {sched sched′ : Sched Γ}
                  {st st′ : EvalSt e} {vs bs}
              → thruWalk⇓ {e = e} op nid κ id now vals sched st
                  (vs , bs , sched′ , st′)
              → (k : MintKey)
              → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

thruConsume-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {op} {nid} {κ : Path Γ lo u t} {id now}
                     {o : Val Γ (obs u)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {vs bs}
                 → thruConsume⇓ {e = e} op nid κ id now o sched st
                     (vs , bs , sched′ , st′)
                 → (k : MintKey)
                 → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

mergeAllDrain-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                       {allNid} {κ : Path Γ lo s t} {id now} {lim act od q}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                       {vs bs act′ q′}
                   → mergeAllDrain⇓ {e = e} allNid κ id now lim act od q sched st
                       (vs , bs , act′ , q′ , sched′ , st′)
                   → (k : MintKey)
                   → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

innerFinish-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                     {op} {allNid inst} {κ : Path Γ lo s t} {id now}
                     {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                     {st st′ : EvalSt e} {m} {vs bs fin}
                 → innerFinish⇓ {e = e} op allNid inst κ id now vals sched st m
                     (vs , bs , fin , sched′ , st′)
                 → (k : MintKey)
                 → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

innerReact-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                    {op} {allNid inst} {κ : Path Γ lo s t} {id now}
                    {vals : List (Val Γ s)} {sched sched′ : Sched Γ}
                    {st st′ : EvalSt e} {alive} {vs bs fin}
                → innerReact⇓ {e = e} op allNid inst κ id now vals sched st alive
                    (vs , bs , fin , sched′ , st′)
                → (k : MintKey)
                → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched′)

sharedConnect-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                       {i} {d} {κ : Path Γ lo _ t} {below} {id now}
                       {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                   → sharedConnect⇓ {e = e} i d κ below id now sched st
                       (burst , sched₁ , st₂)
                   → (k : MintKey)
                   → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₁)

subscribeSharedSlot-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                             {i} {d} {κ : Path Γ lo _ t} {below} {id now}
                             {sched sched₁ : Sched Γ} {st st₂ : EvalSt e} {burst}
                         → subscribeSharedSlot⇓ {e = e} i d κ below id now sched st
                             (burst , sched₁ , st₂)
                         → (k : MintKey)
                         → freshId k (Sched.mint sched) ≤ freshId k (Sched.mint sched₁)

subscribeE-mono (subs-floor _)              k = ≤-refl
subscribeE-mono (subs-shared _ slot)        k = subscribeSharedSlot-mono slot k
subscribeE-mono (subs-hot-done _ _ _)       k = ≤-refl
subscribeE-mono (subs-hot-live {sched = sched} _ _ _ refl) k =
  next-mono regᵏ k (Sched.mint sched)
subscribeE-mono (subs-cold-sync {sync = sync} {id = id} {sched = sched} _ _ eq) k =
  oneShot-mint sync id sched eq k
subscribeE-mono (subs-cold-async {sched = sched} _ _ refl refl refl) k =
  ≤-trans (next-mono ordinalᵏ k (Sched.mint sched))
          (≤-trans (next-mono sourceᵏ k (next ordinalᵏ (Sched.mint sched)))
                   (next-mono regᵏ k (next sourceᵏ (next ordinalᵏ (Sched.mint sched)))))
subscribeE-mono (subs-of {id = id} {sched = sched} eq)           k = oneShot-mint _ id sched eq k
subscribeE-mono (subs-empty {u = u} {id = id} {sched = sched} eq) k =
  oneShot-mint ([] {A = Val _ u}) id sched eq k
subscribeE-mono (subs-take-zero {u = u} {id = id} {sched = sched} _ eq) k =
  oneShot-mint ([] {A = Val _ u}) id sched eq k
subscribeE-mono (subs-take-suc {sched = sched} _ refl sub push) k =
  ≤-trans (≤-trans (next-mono nodeᵏ k (Sched.mint sched)) (subscribeE-mono sub k))
          (pushBurst-mono push k)
subscribeE-mono (subs-batchSync {sched = sched} refl sub push) k =
  ≤-trans (≤-trans (next-mono nodeᵏ k (Sched.mint sched)) (subscribeE-mono sub k))
          (pushBurst-mono push k)
subscribeE-mono (subs-map sub push) k =
  ≤-trans (subscribeE-mono sub k) (pushBurst-mono push k)
subscribeE-mono (subs-scan {sched = sched} refl sub push) k =
  ≤-trans (≤-trans (next-mono nodeᵏ k (Sched.mint sched)) (subscribeE-mono sub k))
          (pushBurst-mono push k)
subscribeE-mono (subs-merge-all sa)         k = subscribeAll-mono sa k
subscribeE-mono (subs-switch-all sa)        k = subscribeAll-mono sa k
subscribeE-mono (subs-exhaust-all sa)       k = subscribeAll-mono sa k
subscribeE-mono (subs-μ sub)                k = subscribeE-mono sub k
subscribeE-mono (subs-defer {sched = sched} refl refl refl refl) k =
  ≤-trans (next-mono ordinalᵏ k (Sched.mint sched))
          (≤-trans (next-mono sourceᵏ k (next ordinalᵏ (Sched.mint sched)))
                   (≤-trans (next-mono nodeᵏ k (next sourceᵏ (next ordinalᵏ (Sched.mint sched))))
                            (next-mono regᵏ k (next nodeᵏ (next sourceᵏ (next ordinalᵏ (Sched.mint sched)))))))
subscribeE-mono (subs-mint {sched = sched} refl sub) k =
  ≤-trans (next-mono sourceᵏ k (Sched.mint sched)) (subscribeE-mono sub k)

pushBurst-mono push-nil              k = ≤-refl
pushBurst-mono (push-cons _ st rest) k = ≤-trans (stepFrame-mono st k) (pushBurst-mono rest k)

stepFrame-mono step-map k = ≤-refl
stepFrame-mono (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) k =
  scanDispatch-mint fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) k
stepFrame-mono (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) k =
  takeDispatch-mint nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) k
stepFrame-mono (step-batchSync {nid = nid} {vals = vals} {fin} {sched} {st}) k =
  batchSyncDispatch-mint nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) k
stepFrame-mono (step-from-inner r)   k = innerReact-mono r k
stepFrame-mono (step-thru-outer {op = op} {nid} {fin = fin} w) k =
  ≤-trans (thruWalk-mono w k) (thruWrap-mint op nid fin _ _ _ _ k)

subscribeAll-mono (sub-all {sched = sched} refl sub push) k =
  ≤-trans (≤-trans (next-mono nodeᵏ k (Sched.mint sched)) (subscribeE-mono sub k))
          (pushBurst-mono push k)

subscribeInner-mono (inner {sched = sched} refl sub _) k =
  ≤-trans (next-mono nodeᵏ k (Sched.mint sched)) (subscribeE-mono sub k)

thruWalk-mono walk-nil          k = ≤-refl
thruWalk-mono (walk-cons c w)   k = ≤-trans (thruConsume-mono c k) (thruWalk-mono w k)

thruConsume-mono (consume-all-sub _ _ si)      k = subscribeInner-mono si k
thruConsume-mono (consume-all-enqueue _ _)     k = ≤-refl
thruConsume-mono (consume-all-nil _)           k = ≤-refl
thruConsume-mono (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur} _ kl si) k =
  ≤-trans (switchKill-mint cur sched₀ st₀ kl k) (subscribeInner-mono si k)
thruConsume-mono (consume-switch-nil _)        k = ≤-refl
thruConsume-mono (consume-exhaust-sub _ si)    k = subscribeInner-mono si k
thruConsume-mono (consume-exhaust-nil _)       k = ≤-refl

mergeAllDrain-mono drain-nil             k = ≤-refl
mergeAllDrain-mono (drain-no-room _)     k = ≤-refl
mergeAllDrain-mono (drain-room _ si dr)  k =
  ≤-trans (subscribeInner-mono si k) (mergeAllDrain-mono dr k)

innerReact-mono react-false        k = ≤-refl
innerReact-mono (react-alive _)    k = ≤-refl
innerReact-mono (react-dead _ f)   k = innerFinish-mono f k

innerFinish-mono (finish-all-drain dr)     k = mergeAllDrain-mono dr k
innerFinish-mono (finish-switch-clear _)   k = ≤-refl
innerFinish-mono finish-exhaust-clear      k = ≤-refl
innerFinish-mono (finish-nil _)            k = ≤-refl

sharedConnect-mono (connect-live {sched = sched} refl sub _) k =
  ≤-trans (next-mono regᵏ k (Sched.mint sched)) (subscribeE-mono sub k)
sharedConnect-mono (connect-died {sched = sched} refl sub _) k =
  ≤-trans (next-mono regᵏ k (Sched.mint sched)) (subscribeE-mono sub k)

subscribeSharedSlot-mono (slot-spent _)        k = ≤-refl
subscribeSharedSlot-mono (slot-join {sched = sched} _ _ refl) k =
  next-mono regᵏ k (Sched.mint sched)
subscribeSharedSlot-mono (slot-connect _ _ sc) k = sharedConnect-mono sc k
