-- A SUBSCRIPTION WRITES NO NODE BELOW THE COUNTER IT STARTED AT, PROVEN
-- OVER THE RELATIONS ITS CYCLE PASSES THROUGH.  The floor is an
-- argument rather than a reading of the mint, so every recursive
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
-- that thread premises are the second, and the writers -- the fold's
-- dispatch, the truncation's, the bracket's two ends, the flattener's
-- wrap, the merge's bump and the plain install -- are the third.
-- Nothing here is delicate; it is long because the relation is wide.
module Rx.Evaluator.Freshness.Preserve where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; obs; FnClo; _×ᵗ_; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; NodeId; NodeState; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; Segs;
  switchKill; scanDispatch; takeDispatch; thruWrap; mergeAllBump; scanVals; takeVals; cell-st;
  take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st; lookupNode)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓;
  thruWalk⇓; mergeAllDrain⇓; innerFinish⇓; innerReact⇓; stepFrame⇓; pushBurst⇓;
  pushSegs⇓; psegs-nil; psegs-cons;
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
open import Rx.Evaluator.Freshness using (nodeCt; PreservedBelow; FrameAbove;
  pres-same; pres-trans; pres-write)
open import Rx.Evaluator.Freshness.Mono using (subscribeE-mono; stepFrame-mono;
  subscribeInner-mono; thruConsume-mono; switchKill-node; pushBurst-mono)

-- the fold's dispatch rewrites its own node and nothing else
scan-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {f}
              (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
              (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
          → f ≤ nid
          → PreservedBelow f st (proj₂ (proj₂ (proj₂
              (scanDispatch {e = e} fn nid vals fin sched st m))))
scan-pres {u = u} fn nid vals fin sched st (just (cell-st {w} a)) f≤nid
  with w ≟ᵗ u
... | no  _    = pres-same _ _ refl
... | yes refl = pres-write _ _ (cell-st (proj₂ (scanVals fn a vals))) refl f≤nid
scan-pres fn nid vals fin sched st nothing                      f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (take-st _))           f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (batchSync-st _))      f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (switch-st _ _))       f≤nid = pres-same _ _ refl
scan-pres fn nid vals fin sched st (just (exhaust-st _ _))      f≤nid = pres-same _ _ refl

-- the truncation's cut severs registrations and rewrites its own node
take-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {f}
              (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
          → f ≤ nid
          → PreservedBelow f st (proj₂ (proj₂ (proj₂
              (takeDispatch {e = e} nid vals fin sched st m))))
take-pres nid vals fin sched st (just (take-st k)) f≤nid
  with proj₂ (proj₂ (takeVals k vals))
... | true  = pres-write _ _ (take-st zero) refl f≤nid
... | false = pres-write _ _ (take-st (proj₁ (proj₂ (takeVals k vals)))) refl f≤nid
take-pres nid vals fin sched st nothing                      f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (cell-st _))           f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (batchSync-st _))      f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (mergeAll-st _ _ _ _)) f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (switch-st _ _))       f≤nid = pres-same _ _ refl
take-pres nid vals fin sched st (just (exhaust-st _ _))      f≤nid = pres-same _ _ refl

-- the flattener's wrap marks its own node done
wrap-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f}
              (op : AllOp) (nid : NodeId) (fin : Bool)
              (sched′ : Sched Γ) (st′ : EvalSt e)
          → f ≤ nid
          → PreservedBelow f st′ (proj₂ (proj₂
              (thruWrap {e = e} op nid fin (sched′ , st′))))
wrap-pres op nid false sched′ st′ f≤nid = pres-same _ _ refl
wrap-pres mergeAllᵒ nid true sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st lim act q _) = pres-write _ _ (mergeAll-st lim act q true) refl f≤nid
... | just (cell-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (batchSync-st _)          = pres-same _ _ refl
... | just (switch-st _ _)           = pres-same _ _ refl
... | just (exhaust-st _ _)          = pres-same _ _ refl
... | nothing                        = pres-same _ _ refl
wrap-pres switchᵒ nid true sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur _)         = pres-write _ _ (switch-st cur true) refl f≤nid
... | just (cell-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (batchSync-st _)          = pres-same _ _ refl
... | just (mergeAll-st _ _ _ _)     = pres-same _ _ refl
... | just (exhaust-st _ _)          = pres-same _ _ refl
... | nothing                        = pres-same _ _ refl
wrap-pres exhaustᵒ nid true sched′ st′ f≤nid
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act _)        = pres-write _ _ (exhaust-st act true) refl f≤nid
... | just (cell-st _)               = pres-same _ _ refl
... | just (take-st _)               = pres-same _ _ refl
... | just (batchSync-st _)          = pres-same _ _ refl
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
... | just (cell-st _)           = pres-same _ _ refl
... | just (take-st _)           = pres-same _ _ refl
... | just (batchSync-st _)      = pres-same _ _ refl
... | just (switch-st _ _)       = pres-same _ _ refl
... | just (exhaust-st _ _)      = pres-same _ _ refl
... | nothing                    = pres-same _ _ refl

-- the switch's cut sweeps registrations, never the table
kill-pres : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f}
              (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
              {sched₁ st₁}
          → switchKill {e = e} cur sched st ≡ (sched₁ , st₁)
          → PreservedBelow f st st₁
kill-pres nothing  sched st refl = pres-same _ _ refl
kill-pres (just v) sched st refl = pres-same _ _ refl

-- THE THIRTEEN-MEMBER INDUCTION, AND WHAT IT DESCENDS ON.  Every
-- clause below matches a constructor of the relation its member is
-- stated over and recurses on that constructor's own sub-derivations,
-- so the block peels no edge and carries no counter.  That is the one
-- reading `make recursion-cover` takes on the source's word, so it is
-- written out rather than left unlisted, and the check fails the day
-- the names stop naming a cycle.
-- STRUCTURAL SCC: subscribeE-preserves subscribeSharedSlot-preserves subscribeInner-preserves subscribeAll-preserves stepFrame-preserves pushBurst-preserves pushSegs-preserves thruWalk-preserves thruConsume-preserves innerReact-preserves innerFinish-preserves mergeAllDrain-preserves sharedConnect-preserves
subscribeE-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         (f : ℕ) {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                         {sched sched₂ : Sched Γ} {st st₁ : EvalSt e}
                         {segs : Segs Γ u t}
                     → f ≤ nodeCt sched
                     → subscribeE⇓ {e = e} b κ now sched st
                         (segs , sched₂ , st₁)
                     → PreservedBelow f st st₁

pushBurst-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                        (f : ℕ) {fr : Frame Γ s u} {κ : Path Γ lo u t}
                        {now} {ems}
                        {sched sched₂ : Sched Γ} {st st₂ : EvalSt e} {rest}
                    → f ≤ nodeCt sched
                    → FrameAbove f fr
                    → pushBurst⇓ {e = e} now fr κ ems sched st
                        (rest , sched₂ , st₂)
                    → PreservedBelow f st st₂

pushSegs-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                       (f : ℕ) {fr : Frame Γ s u} {κ : Path Γ lo u t}
                       {now} {segs}
                       {sched sched₂ : Sched Γ} {st st₂ : EvalSt e} {out}
                   → f ≤ nodeCt sched
                   → FrameAbove f fr
                   → pushSegs⇓ {e = e} now fr κ segs sched st
                       (out , sched₂ , st₂)
                   → PreservedBelow f st st₂

stepFrame-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
                        (f : ℕ) {fr : Frame Γ s u} {κ : Path Γ lo u t}
                        {now} {vals : List (Val Γ s)} {fin}
                        {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
                        {segs fin′}
                    → f ≤ nodeCt sched
                    → FrameAbove f fr
                    → stepFrame⇓ {e = e} now fr κ vals fin sched st
                        (segs , fin′ , sched₁ , st₁)
                    → PreservedBelow f st st₁

subscribeAll-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                           (f : ℕ) {op} {ns : NodeState Γ}
                           {b : Val Γ (obs (obs u))} {κ : Path Γ lo u t} {now}
                           {sched sched₂ : Sched Γ} {st st₁ : EvalSt e}
                           {segs : Segs Γ u t}
                       → f ≤ nodeCt sched
                       → subscribeAll⇓ {e = e} op ns b κ now sched st
                           (segs , sched₂ , st₁)
                       → PreservedBelow f st st₁

subscribeInner-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                             (f : ℕ) {op} {allNid} {κ : Path Γ lo u t} {now}
                             {o : Val Γ (obs u)}
                             {sched sched′ : Sched Γ} {st st′ : EvalSt e}
                             {inst segs done}
                         → f ≤ nodeCt sched
                         → subscribeInner⇓ {e = e} op allNid κ now o sched st
                             (inst , segs , done , sched′ , st′)
                         → PreservedBelow f st st′

thruWalk-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                       (f : ℕ) {op} {nid} {κ : Path Γ lo u t} {now} {os}
                       {sched₀ sched₂ : Sched Γ} {st₀ st₂ : EvalSt e} {segs}
                   → f ≤ nodeCt sched₀
                   → f ≤ nid
                   → thruWalk⇓ {e = e} op nid κ now os sched₀ st₀
                       (segs , sched₂ , st₂)
                   → PreservedBelow f st₀ st₂

thruConsume-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                          (f : ℕ) {op} {nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)}
                          {sched₀ sched₁ : Sched Γ} {st₀ st₁ : EvalSt e} {segs}
                      → f ≤ nodeCt sched₀
                      → f ≤ nid
                      → thruConsume⇓ {e = e} op nid κ now o sched₀ st₀
                          (segs , sched₁ , st₁)
                      → PreservedBelow f st₀ st₁

mergeAllDrain-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                            (f : ℕ) {allNid} {κ : Path Γ lo u t} {now}
                            {lim act od q}
                            {sched₀ sched₂ : Sched Γ} {st₀ st₂ : EvalSt e}
                            {segs act′ q′}
                        → f ≤ nodeCt sched₀
                        → f ≤ allNid
                        → mergeAllDrain⇓ {e = e} allNid κ now lim act od q
                            sched₀ st₀ (segs , act′ , q′ , sched₂ , st₂)
                        → PreservedBelow f st₀ st₂

innerFinish-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                          (f : ℕ) {op} {allNid} {inst} {κ : Path Γ lo u t}
                          {now} {vals : List (Val Γ u)}
                          {sched sched′ : Sched Γ} {st st′ : EvalSt e} {ns}
                          {segs done}
                      → f ≤ nodeCt sched
                      → f ≤ allNid
                      → innerFinish⇓ {e = e} op allNid inst κ now vals sched st
                          ns (segs , done , sched′ , st′)
                      → PreservedBelow f st st′

innerReact-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                         (f : ℕ) {op} {allNid} {inst} {κ : Path Γ lo u t}
                         {now} {vals : List (Val Γ u)}
                         {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {fin}
                         {segs fin′}
                     → f ≤ nodeCt sched
                     → f ≤ allNid
                     → innerReact⇓ {e = e} op allNid inst κ now vals sched st
                         fin (segs , fin′ , sched₁ , st₁)
                     → PreservedBelow f st st₁

sharedConnect-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                            (f : ℕ) {i} {d} {κ : Path Γ lo _ t} {below}
                            {now} {sched sched₁ : Sched Γ}
                            {st st₂ : EvalSt e} {segs : Segs Γ _ t}
                        → f ≤ nodeCt sched
                        → sharedConnect⇓ {e = e} i d κ below now sched st
                            (segs , sched₁ , st₂)
                        → PreservedBelow f st st₂

subscribeSharedSlot-preserves : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                                  (f : ℕ) {i} {d} {κ : Path Γ lo _ t} {below}
                                  {now} {sched sched₁ : Sched Γ}
                                  {st st₂ : EvalSt e} {segs : Segs Γ _ t}
                              → f ≤ nodeCt sched
                              → subscribeSharedSlot⇓ {e = e} i d κ below now
                                  sched st (segs , sched₁ , st₂)
                              → PreservedBelow f st st₂

subscribeE-preserves f le (subs-floor _)            = pres-same _ _ refl
subscribeE-preserves f le (subs-shared _ slot)      = subscribeSharedSlot-preserves f le slot
subscribeE-preserves f le (subs-hot-done _ _ _)     = pres-same _ _ refl
subscribeE-preserves f le (subs-hot-live _ _ _ _)   = pres-same _ _ refl
subscribeE-preserves f le (subs-cold-sync _ _)      = pres-same _ _ refl
subscribeE-preserves f le (subs-cold-async _ _ _ _ _) = pres-same _ _ refl
subscribeE-preserves f le subs-of                   = pres-same _ _ refl
subscribeE-preserves f le subs-empty                = pres-same _ _ refl
subscribeE-preserves f le (subs-take-zero _)        = pres-same _ _ refl
subscribeE-preserves f le (subs-map sub push) =
  pres-trans (subscribeE-preserves f le sub)
             (pushSegs-preserves f (≤-trans le (subscribeE-mono sub)) _ push)
subscribeE-preserves f le (subs-take-suc {k = k} _ refl sub push) =
  pres-trans (pres-trans (pres-write _ _ (take-st (suc k)) refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushSegs-preserves f
                (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push)
subscribeE-preserves f le (subs-batchSync refl sub push) =
  pres-trans
    (pres-trans (pres-trans (pres-write _ _ (batchSync-st true) refl le)
                            (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
                (pushSegs-preserves f
                   (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push))
    (pres-write _ _ (batchSync-st false) refl le)
subscribeE-preserves f le (subs-scan refl sub push) =
  pres-trans (pres-trans (pres-write _ _ _ refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushSegs-preserves f
                (≤-trans (≤-trans le (n≤1+n _)) (subscribeE-mono sub)) le push)
subscribeE-preserves f le (subs-merge-all sa)       = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-switch-all sa)      = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-exhaust-all sa)     = subscribeAll-preserves f le sa
subscribeE-preserves f le (subs-μ sub)              = subscribeE-preserves f le sub
subscribeE-preserves f le (subs-defer refl _ _ _)   = pres-write _ _ _ refl le
subscribeE-preserves f le (subs-mint _ sub)         = subscribeE-preserves f le sub

pushBurst-preserves f le fa push-nil = pres-same _ _ refl
pushBurst-preserves f le fa (push-cons _ stp rest) =
  pres-trans (stepFrame-preserves f le fa stp)
             (pushBurst-preserves f (≤-trans le (stepFrame-mono stp)) fa rest)

pushSegs-preserves f le fa psegs-nil = pres-same _ _ refl
pushSegs-preserves f le fa (psegs-cons pb ps) =
  pres-trans (pushBurst-preserves f le fa pb)
             (pushSegs-preserves f (≤-trans le (pushBurst-mono pb)) fa ps)

stepFrame-preserves f le fa step-map       = pres-same _ _ refl
stepFrame-preserves f le fa step-batchSync = pres-same _ _ refl
stepFrame-preserves f le fa
  (step-scan {fn = fn} {nid} {vals = vals} {fin} {sched} {st}) =
  scan-pres fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) fa
stepFrame-preserves f le fa
  (step-take {nid = nid} {vals = vals} {fin} {sched} {st}) =
  take-pres nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) fa
stepFrame-preserves f le fa (step-from-inner r) =
  innerReact-preserves f le (proj₁ fa) r
stepFrame-preserves f le fa
  (step-thru-outer {op = op} {nid} {fin = fin} {sched′ = sched′} {st′ = st′} w) =
  pres-trans (thruWalk-preserves f le fa w)
             (wrap-pres op nid fin sched′ st′ fa)

subscribeAll-preserves f le (sub-all refl sub push) =
  pres-trans (pres-trans (pres-write _ _ _ refl le)
                         (subscribeE-preserves f (≤-trans le (n≤1+n _)) sub))
             (pushSegs-preserves f
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

mergeAllDrain-preserves f le fn drain-nil         = pres-same _ _ refl
mergeAllDrain-preserves f le fn (drain-no-room _) = pres-same _ _ refl
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

sharedConnect-preserves f le (connect-live refl sub _) =
  pres-trans (pres-same _ _ refl) (subscribeE-preserves f le sub)
sharedConnect-preserves f le (connect-died refl sub _) =
  pres-trans (pres-same _ _ refl)
             (pres-trans (subscribeE-preserves f le sub) (pres-same _ _ refl))

subscribeSharedSlot-preserves f le (slot-spent _)        = pres-same _ _ refl
subscribeSharedSlot-preserves f le (slot-join _ _ _)     = pres-same _ _ refl
subscribeSharedSlot-preserves f le (slot-connect _ _ sc) = sharedConnect-preserves f le sc
