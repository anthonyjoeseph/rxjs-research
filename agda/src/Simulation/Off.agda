------------------------------------------------------------------
-- A FOLD OFF A NODE IS FRAMED BY IT.  Run from a table holding the
-- node, rewritten, a derivation is the one from the table as it was,
-- constructor for constructor, with the rewrite laid over where it
-- ends.  Every read a run makes is at a walked frame's own node or at
-- the counter, and the floor's watch says neither is the node; every
-- write is at one of those too, and a write elsewhere commutes with
-- the rewrite while the node is present.
------------------------------------------------------------------

module Simulation.Off where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Decide using (≡ᵇ→≡)
open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Val; obs; FnClo; boolᵗ; _×ᵗ_; _+ᵗ_; listᵗ; _≟ᵗ_)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f; batchSync-f;
  from-inner; thru-outer; NodeState; NodeId; RegId; RegSrc; regFloor; lookupNode; setNode;
  pathHasNode; installNode; lowerFloor; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st;
  mergeAll-st; switch-st; exhaust-st; batchSync-st; thruWrap; switchKill; shareDying;
  shareFinish; spentOn; register; scanDispatch; takeDispatch; batchDispatch; takeVals; echoᵗ;
  atSlot; atDyn; markDlv; drainSt; consumeUsable; batchDown; shareSpend)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above; <→≢ᵇ)
open import Rx.Evaluator.Unconn-Arith using (KeepsC; keeps-refl; keeps-trans; keeps-cons)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓; thruWalk⇓; mergeAllDrain⇓;
  innerFinish⇓; innerReact⇓; stepFrame⇓; subscribeAll⇓; subscribeSharedSlot⇓; foldPath⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-takeWhile; subs-batchSync; subs-map; subs-scan;
  subs-flatten; subs-μ; subs-defer; subs-mint; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil; walk-echo; walk-cons;
  drain-spent; drain-nil; drain-no-room; drain-room; finish-all-drain; finish-switch-clear; finish-exhaust-clear;
  finish-nil; react-false; react-alive; react-dead; step-map; step-scan; step-take; step-batchSync;
  step-from-inner; step-thru-outer; sub-all; connect; slot-spent; slot-join; slot-connect; disp; walk-end;
  walk-more; go-nil; go-cut; go-live; fold-root; fold-sink; fold-step; injectRoot)
open import Rx.Evaluator.Reducible.Support using (endOf; waiting; ∨-T; ∨-Tˡ; ∨-Tʳ; lower-nodes; scanOff; takeOff; batchOff;
  wrap-facts; Wrapped; at-end; node-below; off-path; linked; ruled; Linked; linked-keeps; rowSrc)
open import Rx.Evaluator.Reducible.Floor using (module Watch; clear-self; notIn₁; notIn₂; ≢ᵇ)
open import Simulation.Arm using (Clear)
open import Simulation.Size using (sz-subscribeE; sz-subscribeInner; sz-thruConsume; sz-thruWalk; sz-mergeAllDrain;
  sz-innerFinish; sz-innerReact; sz-stepFrame; sz-subscribeAll; sz-subscribeSharedSlot; sz-dispatchShare;
  sz-shareWalk; sz-shareGo; sz-foldPath)

≢ᵇ-sym : ∀ {a b : ℕ} → (a ≡ᵇ b) ≡ false → (b ≡ᵇ a) ≡ false
≢ᵇ-sym {a} {b} ne with b ≡ᵇ a in eq
... | false = refl
... | true  = ⊥-elim (≢ᵇ ne (sym (≡ᵇ→≡ b a eq)))

if-false : ∀ {A : Set} {b : Bool} {x z : A} → b ≡ false → (if b then x else z) ≡ z
if-false refl = refl

if-true : ∀ {A : Set} {b : Bool} {x z : A} → b ≡ true → (if b then x else z) ≡ x
if-true refl = refl

-- TWO WRITES AT DIFFERENT KEYS COMMUTE WHERE THE SECOND KEY IS PRESENT.
-- An absent key is appended, and two appends land in the order made.
set-comm : ∀ {n} {Γ : Ctx n} (c k : NodeId) (v y : NodeState Γ) (ts : List (NodeId × NodeState Γ)) {z}
         → (c ≡ᵇ k) ≡ false → lookupNode k ts ≡ just z
         → setNode c v (setNode k y ts) ≡ setNode k y (setNode c v ts)
set-comm c k v y [] ne ()
set-comm c k v y ((j , s) ∷ r) ne h with j ≡ᵇ k in jk | j ≡ᵇ c in jc
... | true  | true  = ⊥-elim (≢ᵇ ne (trans (sym (≡ᵇ→≡ j c jc)) (≡ᵇ→≡ j k jk)))
... | true  | false = trans (if-false (≢ᵇ-sym {c} {k} ne)) (sym (if-true jk))
... | false | true  = trans (if-true jc) (sym (if-false ne))
... | false | false = trans (if-false jc) (trans (cong ((j , s) ∷_) (set-comm c k v y r ne h)) (sym (if-false jk)))

------------------------------------------------------------------
-- THE TRANSPORT, AT ONE REWRITTEN NODE `k` HOLDING `y`, watched as
-- the floor watches a node written by nothing.
------------------------------------------------------------------
module Off {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (k : NodeId) (y : NodeState Γ) (x₀ : Maybe (Fin n)) (sl₀ : Slots Γ) (cs₀ : List Source) where

  open Watch {e = e} false k x₀ (waiting (just y)) (just y) sl₀ cs₀

  -- the table with the rewrite laid over
  ov : EvalSt e → EvalSt e
  ov st = record st { nodes = setNode k y (EvalSt.nodes st) }

  ov3 : ∀ {A B : Set} → A × B × EvalSt e → A × B × EvalSt e
  ov3 r = proj₁ r , proj₁ (proj₂ r) , ov (proj₂ (proj₂ r))

  ov4 : ∀ {A B C : Set} → A × B × C × EvalSt e → A × B × C × EvalSt e
  ov4 r = proj₁ r , ov3 (proj₂ r)

  ov5 : ∀ {A B C D : Set} → A × B × C × D × EvalSt e → A × B × C × D × EvalSt e
  ov5 r = proj₁ r , ov4 (proj₂ r)

  end3 : ∀ {A B : Set} → A × B × EvalSt e → EvalSt e
  end3 r = proj₂ (proj₂ r)

  end4 : ∀ {A B C : Set} → A × B × C × EvalSt e → EvalSt e
  end4 r = end3 (proj₂ r)

  end5 : ∀ {A B C D : Set} → A × B × C × D × EvalSt e → EvalSt e
  end5 r = end4 (proj₂ r)

  -- the rewrite moves no reader's link
  linked-ov : ∀ {sched : Sched Γ} {st : EvalSt e} → Linked sched st → Linked sched (ov st)
  linked-ov {sched} {st} lk {r} r∈ =
    linked-keeps {sched = sched} {sched′ = sched} {st = st} {st′ = ov st} (rowSrc r) (keeps-refl _ _) (lk r∈)

  under₂ : ∀ {A B C : Set} {a : A} {b : B} {x x′ : C} → x ≡ x′ → (a , b , x) ≡ (a , b , x′)
  under₂ refl = refl

  -- the node is in the table
  record HasIn (ns : List (NodeId × NodeState Γ)) : Set where
    constructor has
    field
      cell : NodeState Γ
      read : lookupNode k ns ≡ just cell

  Has : EvalSt e → Set
  Has st = HasIn (EvalSt.nodes st)

  has-via : ∀ {ns ns′} → lookupNode k ns′ ≡ lookupNode k ns → HasIn ns → HasIn ns′
  has-via eq (has z h) = has z (trans eq h)

  has-set : ∀ (st : EvalSt e) (c : NodeId) (v : NodeState Γ) → (c ≡ᵇ k) ≡ false → Has st → Has (installNode c v st)
  has-set st c v ne = has-via (set-above c k v (EvalSt.nodes st) ne)

  -- a write off the node commutes with the rewrite
  ov-set : ∀ (st : EvalSt e) (c : NodeId) (v : NodeState Γ) → (c ≡ᵇ k) ≡ false → Has st
         → installNode c v (ov st) ≡ ov (installNode c v st)
  ov-set st c v ne (has z h) = cong (λ ns → record st { nodes = ns }) (set-comm c k v y (EvalSt.nodes st) ne h)

  -- and a read off the node reads the table as it was
  look-ov : ∀ (st : EvalSt e) (c : NodeId) → (c ≡ᵇ k) ≡ false
          → lookupNode c (EvalSt.nodes (ov st)) ≡ lookupNode c (EvalSt.nodes st)
  look-ov st c ne = set-above k c y (EvalSt.nodes st) (≢ᵇ-sym {c} {k} ne)

  -- A WALKED PATH STANDS ON NO FRAME AT THE NODE
  frame-off : ∀ {s u} (f : Frame Γ s u) → FrameOK f → NotIn f
  frame-off (map-f _)          fo = fo
  frame-off (scan-f _ _)       fo = fo
  frame-off (take-f _ _)       fo = fo
  frame-off (batchSync-f _)    fo = fo
  frame-off (from-inner _ _ _) fo = fo refl
  frame-off (thru-outer _ _)   fo = fo

  ok-off : ∀ {lo u} (κ : Path Γ lo u t) → PathOK κ → T (pathHasNode k κ) → ⊥
  ok-off root             ok ()
  ok-off (share-sink _ _) ok ()
  ok-off (f ↠[ _ ] κ)     (fo , ok) h = [ frame-off f fo , ok-off κ ok ]′ (∨-T h)

  pi-off : ∀ {lo u} {κ : Path Γ lo u t} → PI κ → T (pathHasNode k κ) → ⊥
  pi-off {κ = κ} ph = ok-off κ (PI.pok ph)

  lower-off : ∀ {lo lo′ u} (le : lo′ ≤ lo) (κ : Path Γ lo u t) → PI κ → T (pathHasNode k (lowerFloor le κ)) → ⊥
  lower-off le κ ph th = pi-off ph (subst T (lower-nodes le κ k) th)

  -- so it reads the same spent takes, and registers the same rows
  spent-ov : ∀ {lo s} (p : Path Γ lo s t) (ns : List (NodeId × NodeState Γ))
           → (T (pathHasNode k p) → ⊥) → spentOn p (setNode k y ns) ≡ spentOn p ns
  spent-ov root                  ns off = refl
  spent-ov (share-sink _ _)      ns off = refl
  spent-ov (map-f _ ↠[ _ ] p)    ns off = spent-ov p ns (λ h → off (∨-Tʳ h))
  spent-ov (scan-f _ _ ↠[ _ ] p) ns off = spent-ov p ns (λ h → off (∨-Tʳ h))
  spent-ov (batchSync-f _ ↠[ _ ] p) ns off = spent-ov p ns (λ h → off (∨-Tʳ h))
  spent-ov (from-inner _ _ _ ↠[ _ ] p) ns off = spent-ov p ns (λ h → off (∨-Tʳ h))
  spent-ov (thru-outer _ _ ↠[ _ ] p) ns off = spent-ov p ns (λ h → off (∨-Tʳ h))
  spent-ov (take-f _ c ↠[ _ ] p) ns off
    rewrite set-above k c y ns (≢ᵇ-sym {c} {k} (notIn₁ {c} {k} (λ h → off (∨-Tˡ h))))
          | spent-ov p ns (λ h → off (∨-Tʳ {b = pathHasNode k p} h)) = refl

  register-ov : ∀ (st : EvalSt e) {u} (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
              → (T (pathHasNode k p) → ⊥) → register rid rs p (ov st) ≡ ov (register rid rs p st)
  register-ov st {u} rid rs p off =
    cong (λ b → record (ov st) { registry = if b then EvalSt.registry st else EvalSt.registry st ++ (rid , rs , u , p) ∷ [] })
         (spent-ov p (EvalSt.nodes st) off)

  -- THE STEPS THAT READ A NODE, read off it
  scan-ov : ∀ {s u} (fn : FnClo Γ (u ×ᵗ s) u) (c : NodeId) (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ)) → (c ≡ᵇ k) ≡ false → Has st
          → scanDispatch fn c vals fin sched (ov st) m ≡ ov4 (scanDispatch fn c vals fin sched st m)
  scan-ov {u = u} fn c vals fin sched st (just (cell-st {w} a)) ne (has z h) with w ≟ᵗ u
  ... | no  _    = refl
  ... | yes refl = cong (λ w → _ , _ , _ , w) (ov-set st c (cell-st (proj₂ (Rx.Evaluator.scanVals fn a vals))) ne (has z h))
  scan-ov fn c vals fin sched st (just (take-st _))           ne h = refl
  scan-ov fn c vals fin sched st (just (batchSync-st _ _ _))  ne h = refl
  scan-ov fn c vals fin sched st (just (mergeAll-st _ _ _ _)) ne h = refl
  scan-ov fn c vals fin sched st (just (switch-st _ _))       ne h = refl
  scan-ov fn c vals fin sched st (just (exhaust-st _ _))      ne h = refl
  scan-ov fn c vals fin sched st nothing                      ne h = refl

  take-ov : ∀ {s} (w : Maybe (FnClo Γ s boolᵗ)) (c : NodeId) (vals : List (Val Γ s)) (fin : Bool)
              (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ)) → (c ≡ᵇ k) ≡ false → Has st
          → takeDispatch w c vals fin sched (ov st) m ≡ ov4 (takeDispatch w c vals fin sched st m)
  take-ov w c vals fin sched st (just (take-st j)) ne (has z h) with proj₂ (proj₂ (takeVals w j vals))
  ... | true  = cong (λ ns → _ , _ , _ , record st { registry = _ ; cancelled = _ ; nodes = ns })
                     (set-comm c k (take-st zero) y (EvalSt.nodes st) ne h)
  ... | false = cong (λ w′ → _ , _ , _ , w′) (ov-set st c (take-st (proj₁ (proj₂ (takeVals w j vals)))) ne (has z h))
  take-ov w c vals fin sched st (just (cell-st _))           ne h = refl
  take-ov w c vals fin sched st (just (batchSync-st _ _ _))  ne h = refl
  take-ov w c vals fin sched st (just (mergeAll-st _ _ _ _)) ne h = refl
  take-ov w c vals fin sched st (just (switch-st _ _))       ne h = refl
  take-ov w c vals fin sched st (just (exhaust-st _ _))      ne h = refl
  take-ov w c vals fin sched st nothing                      ne h = refl

  batch-ov : ∀ {s} (c : NodeId) (vals : List (Val Γ s)) (fin : Bool)
               (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ)) → (c ≡ᵇ k) ≡ false → Has st
           → batchDispatch c vals fin sched (ov st) m ≡ ov4 (batchDispatch c vals fin sched st m)
  batch-ov {s = s} c vals fin sched st (just (batchSync-st {w} true bur done)) ne (has z h) with w ≟ᵗ s
  ... | no  _    = refl
  ... | yes refl = cong (λ w′ → _ , _ , _ , w′) (ov-set st c (batchSync-st true (bur ++ vals) (Data.Bool._∨_ done fin)) ne (has z h))
  batch-ov {s = s} c vals fin sched st (just (batchSync-st {w} false bur done)) ne (has z h) with w ≟ᵗ s
  ... | no  _    = refl
  ... | yes refl = cong (λ w′ → _ , _ , _ , w′) (ov-set st c (batchSync-st {s = s} false [] false) ne (has z h))
  batch-ov c vals fin sched st (just (cell-st _))           ne h = refl
  batch-ov c vals fin sched st (just (take-st _))           ne h = refl
  batch-ov c vals fin sched st (just (mergeAll-st _ _ _ _)) ne h = refl
  batch-ov c vals fin sched st (just (switch-st _ _))       ne h = refl
  batch-ov c vals fin sched st (just (exhaust-st _ _))      ne h = refl
  batch-ov c vals fin sched st nothing                      ne h = refl

  wrap-ov : ∀ (op : AllOp) (c : NodeId) (fin : Bool) (sc : Sched Γ) (st : EvalSt e) → (c ≡ᵇ k) ≡ false → Has st
          → thruWrap {e = e} op c fin (sc , ov st) ≡ ov3 (thruWrap op c fin (sc , st))
  wrap-ov op c false sc st ne h = refl
  wrap-ov mergeAllᵒ c true sc st ne (has z h) rewrite look-ov st c ne with lookupNode c (EvalSt.nodes st)
  ... | just (mergeAll-st lim act q _) = cong (λ w → _ , _ , w) (ov-set st c (mergeAll-st lim act q true) ne (has z h))
  ... | just (cell-st _)           = refl
  ... | just (take-st _)           = refl
  ... | just (batchSync-st _ _ _)  = refl
  ... | just (switch-st _ _)       = refl
  ... | just (exhaust-st _ _)      = refl
  ... | nothing                    = refl
  wrap-ov switchᵒ c true sc st ne (has z h) rewrite look-ov st c ne with lookupNode c (EvalSt.nodes st)
  ... | just (switch-st cur _) = cong (λ w → _ , _ , w) (ov-set st c (switch-st cur true) ne (has z h))
  ... | just (cell-st _)           = refl
  ... | just (take-st _)           = refl
  ... | just (batchSync-st _ _ _)  = refl
  ... | just (mergeAll-st _ _ _ _) = refl
  ... | just (exhaust-st _ _)      = refl
  ... | nothing                    = refl
  wrap-ov exhaustᵒ c true sc st ne (has z h) rewrite look-ov st c ne with lookupNode c (EvalSt.nodes st)
  ... | just (exhaust-st act _) = cong (λ w → _ , _ , w) (ov-set st c (exhaust-st act true) ne (has z h))
  ... | just (cell-st _)           = refl
  ... | just (take-st _)           = refl
  ... | just (batchSync-st _ _ _)  = refl
  ... | just (mergeAll-st _ _ _ _) = refl
  ... | just (switch-st _ _)       = refl
  ... | nothing                    = refl

  -- AND THE STEPS THAT READ NO NODE commute outright
  kill-ov : ∀ (cur : Maybe NodeId) (sc : Sched Γ) (st : EvalSt e)
          → switchKill cur sc (ov st) ≡ (proj₁ (switchKill cur sc st) , ov (proj₂ (switchKill cur sc st)))
  kill-ov nothing  sc st = refl
  kill-ov (just _) sc st = refl

  kill-has : ∀ (cur : Maybe NodeId) (sc : Sched Γ) (st : EvalSt e) → Has st → Has (proj₂ (switchKill cur sc st))
  kill-has nothing  sc st (has z h) = has z h
  kill-has (just _) sc st (has z h) = has z h

  dying-ov : ∀ (i : Fin n) (fin : Bool) (st : EvalSt e) → shareDying i fin (ov st) ≡ ov (shareDying i fin st)
  dying-ov i false st = refl
  dying-ov i true  st = refl

  dying-has : ∀ (i : Fin n) (fin : Bool) (st : EvalSt e) → Has st → Has (shareDying i fin st)
  dying-has i false st (has z h) = has z h
  dying-has i true  st (has z h) = has z h

  finish-ov : ∀ (i : Fin n) (fin : Bool) r → shareFinish {e = e} i fin (ov3 r) ≡ ov3 (shareFinish i fin r)
  finish-ov i false r = refl
  finish-ov i true  r = refl

  finish-has : ∀ (i : Fin n) (fin : Bool) r → Has (proj₂ (proj₂ r)) → Has (proj₂ (proj₂ (shareFinish {e = e} i fin r)))
  finish-has i false r (has z h) = has z h
  finish-has i true  r (has z h) = has z h

  -- a react whose finish read the table as it was
  dead-at : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)} {sched : Sched Γ} {st : EvalSt e} {m r}
          → m ≡ lookupNode a (EvalSt.nodes st)
          → Data.Bool.ListAction.any (Rx.Evaluator.aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
          → (f : innerFinish⇓ {e = e} op a inst κ now vals sched st m r)
          → Σ (innerReact⇓ op a inst κ now vals sched st true r) λ d′ → sz-innerReact d′ ≡ suc (sz-innerFinish f)
  dead-at refl al f = react-dead al f , refl

  -- THE FOURTEEN-MEMBER TRANSPORT.  Every clause matches a constructor,
  -- rebuilds it from the table as it was, and recurses on its
  -- sub-derivations, so the block descends structurally.
  -- STRUCTURAL SCC: subscribeE-off subscribeSharedSlot-off subscribeAll-off subscribeInner-off stepFrame-off thruWalk-off thruConsume-off innerReact-off innerFinish-off mergeAllDrain-off foldPath-off dispatchShare-off shareWalk-off shareGo-off
  subscribeE-off : ∀ {u lo} {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now} {sched : Sched Γ} {sty : EvalSt e} {r}
                 → (d : subscribeE⇓ {e = e} b κ now sched sty r) (st : EvalSt e) → sty ≡ ov st
                 → PI κ → SI sched sty → Has st
                 → Σ _ λ r′ → Σ (subscribeE⇓ b κ now sched st r′) λ d′
                     → sz-subscribeE d′ ≡ sz-subscribeE d × r ≡ ov3 r′ × Has (end3 r′)

  subscribeSharedSlot-off : ∀ {lo} {i : Fin n} {d} {ok} {κ : Path Γ lo (lookup Γ i) t} {below} {now}
                              {sched : Sched Γ} {sty : EvalSt e} {r}
                          → Sched.slots sched i ≡ shared d {ok = ok}
                          → (dv : subscribeSharedSlot⇓ {e = e} i d κ below now sched sty r) (st : EvalSt e) → sty ≡ ov st
                          → PI κ → SI sched sty → Has st
                          → Σ _ λ r′ → Σ (subscribeSharedSlot⇓ i d κ below now sched st r′) λ d′
                              → sz-subscribeSharedSlot d′ ≡ sz-subscribeSharedSlot dv × r ≡ ov3 r′ × Has (end3 r′)

  subscribeAll-off : ∀ {u lo} {op} {ns : NodeState Γ} {b : Val Γ (obs (echoᵗ u))} {κ : Path Γ lo u t} {now}
                       {sched : Sched Γ} {sty : EvalSt e} {r}
                   → (d : subscribeAll⇓ {e = e} op ns b κ now sched sty r) (st : EvalSt e) → sty ≡ ov st
                   → PI κ → SI sched sty → Has st
                   → Σ _ λ r′ → Σ (subscribeAll⇓ op ns b κ now sched st r′) λ d′
                       → sz-subscribeAll d′ ≡ sz-subscribeAll d × r ≡ ov3 r′ × Has (end3 r′)

  subscribeInner-off : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                         {sched : Sched Γ} {sty : EvalSt e} {r}
                     → (d : subscribeInner⇓ {e = e} op a κ now o sched sty r) (st : EvalSt e) → sty ≡ ov st
                     → PA a κ → SI sched sty → Has st
                     → Σ _ λ r′ → Σ (subscribeInner⇓ op a κ now o sched st r′) λ d′
                         → sz-subscribeInner d′ ≡ sz-subscribeInner d × r ≡ ov4 r′ × Has (end4 r′)

  stepFrame-off : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now vals fin}
                    {sched : Sched Γ} {sty : EvalSt e} {r}
                → (d : stepFrame⇓ {e = e} now f κ vals fin sched sty r) (st : EvalSt e) → sty ≡ ov st
                → PF f κ → SI sched sty → Has st
                → Σ _ λ r′ → Σ (stepFrame⇓ now f κ vals fin sched st r′) λ d′
                    → sz-stepFrame d′ ≡ sz-stepFrame d × r ≡ ov5 r′ × Has (end5 r′)

  thruWalk-off : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {vals : List (Val Γ (u +ᵗ obs u))}
                   {sched : Sched Γ} {sty : EvalSt e} {r}
               → (d : thruWalk⇓ {e = e} op a κ now vals sched sty r) (st : EvalSt e) → sty ≡ ov st
               → (a ≡ᵇ k) ≡ false → PI κ → SI sched sty → Has st
               → Σ _ λ r′ → Σ (thruWalk⇓ op a κ now vals sched st r′) λ d′
                   → sz-thruWalk d′ ≡ sz-thruWalk d × r ≡ ov3 r′ × Has (end3 r′)

  thruConsume-off : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o : Val Γ (obs u)}
                      {sched : Sched Γ} {sty : EvalSt e} {r}
                  → (d : thruConsume⇓ {e = e} op a κ now o sched sty r) (st : EvalSt e) → sty ≡ ov st
                  → (a ≡ᵇ k) ≡ false → PI κ → SI sched sty → Has st
                  → Σ _ λ r′ → Σ (thruConsume⇓ op a κ now o sched st r′) λ d′
                      → sz-thruConsume d′ ≡ sz-thruConsume d × r ≡ ov3 r′ × Has (end3 r′)

  innerReact-off : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                     {sched : Sched Γ} {sty : EvalSt e} {alive} {r}
                 → (d : innerReact⇓ {e = e} op a inst κ now vals sched sty alive r) (st : EvalSt e) → sty ≡ ov st
                 → PF (from-inner op a inst) κ → SI sched sty → Has st
                 → Σ _ λ r′ → Σ (innerReact⇓ op a inst κ now vals sched st alive r′) λ d′
                     → sz-innerReact d′ ≡ sz-innerReact d × r ≡ ov5 r′ × Has (end5 r′)

  innerFinish-off : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals : List (Val Γ s)}
                      {sched : Sched Γ} {sty : EvalSt e} {m} {r}
                  → (d : innerFinish⇓ {e = e} op a inst κ now vals sched sty m r) (st : EvalSt e) → sty ≡ ov st
                  → PF (from-inner op a inst) κ → (a ≡ k → waiting m ≤ waiting (just y)) → SI sched sty → Has st
                  → Σ _ λ r′ → Σ (innerFinish⇓ op a inst κ now vals sched st m r′) λ d′
                      → sz-innerFinish d′ ≡ sz-innerFinish d × r ≡ ov5 r′ × Has (end5 r′)

  mergeAllDrain-off : ∀ {s lo} {a} {κ : Path Γ lo s t} {now} {fuel lim act od} {q : List (Val Γ (obs s))}
                        {sched : Sched Γ} {sty : EvalSt e} {r}
                    → (d : mergeAllDrain⇓ {e = e} a κ now fuel lim act od q sched sty r) (st : EvalSt e) → sty ≡ ov st
                    → PA a κ → DQ a (length q) sched sty → Has st
                    → Σ _ λ r′ → Σ (mergeAllDrain⇓ a κ now fuel lim act od q sched st r′) λ d′
                        → sz-mergeAllDrain d′ ≡ sz-mergeAllDrain d × r ≡ ov5 r′ × Has (end5 r′)

  foldPath-off : ∀ {u lo} {κ : Path Γ lo u t} {now vals fin}
                   {sched : Sched Γ} {sty : EvalSt e} {r}
               → (d : foldPath⇓ {e = e} now κ vals fin sched sty r) (st : EvalSt e) → sty ≡ ov st
               → PI κ → SI sched sty → Has st
               → Σ _ λ r′ → Σ (foldPath⇓ now κ vals fin sched st r′) λ d′
                   → sz-foldPath d′ ≡ sz-foldPath d × r ≡ ov3 r′ × Has (end3 r′)

  dispatchShare-off : ∀ {lo} {i : Fin n} {below} {now vals fin} {sched : Sched Γ} {sty : EvalSt e} {r}
                    → (d : dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched sty r) (st : EvalSt e) → sty ≡ ov st
                    → Sink i → SI sched sty → Has st
                    → Σ _ λ r′ → Σ (dispatchShare⇓ {lo = lo} now i below vals fin sched st r′) λ d′
                        → sz-dispatchShare d′ ≡ sz-dispatchShare d × r ≡ ov3 r′ × Has (end3 r′)

  shareWalk-off : ∀ {i : Fin n} {now vals fin} {sched : Sched Γ} {sty : EvalSt e} {r}
                → (d : shareWalk⇓ {e = e} now i vals fin sched sty r) (st : EvalSt e) → sty ≡ ov st
                → Sink i → SI sched sty → Has st
                → Σ _ λ r′ → Σ (shareWalk⇓ now i vals fin sched st r′) λ d′
                    → sz-shareWalk d′ ≡ sz-shareWalk d × r ≡ ov3 r′ × Has (end3 r′)

  shareGo-off : ∀ {lo} {i : Fin n} {now vals fin} {ps : List (RegId × Path Γ lo (lookup Γ i) t)}
                  {sched : Sched Γ} {sty : EvalSt e} {r}
              → (d : shareGo⇓ {e = e} {lo = lo} now i vals fin ps sched sty r) (st : EvalSt e) → sty ≡ ov st
              → (∀ {a} → a ∈ ps → PI (proj₂ a)) → SI sched sty → Has st
              → Σ _ λ r′ → Σ (shareGo⇓ {lo = lo} now i vals fin ps sched st r′) λ d′
                  → sz-shareGo d′ ≡ sz-shareGo d × r ≡ ov3 r′ × Has (end3 r′)

  subscribeE-off (subs-floor le f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , subs-floor le d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-shared sl slot) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeSharedSlot-off sl slot st refl ph s h in r′ , subs-shared sl d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-hot-done lt′ sl m f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , subs-hot-done lt′ sl m d′ , cong suc e₁ , eq , h′
  subscribeE-off {κ = κ} (subs-hot-live {i = i} {rid = rid} below sl m fr) st refl ph s h =
    _ , subs-hot-live below sl m fr , refl
      , under₂ (register-ov st rid (atSlot i) (lowerFloor below κ) (lower-off below κ ph)) , h
  subscribeE-off (subs-cold-sync lt′ sl f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , subs-cold-sync lt′ sl d′ , cong suc e₁ , eq , h′
  subscribeE-off {lo = lo} {κ = κ} (subs-cold-async {src = src} {rid = rid} lt′ sl fs fo fr f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f (register rid (atDyn src lo) κ st)
                                     (register-ov st rid (atDyn src lo) κ (pi-off ph)) ph
                                     (si (ni s) (ea-reg (ea s) ph) (lt s) (rm s)) h
    in r′ , subs-cold-async lt′ sl fs fo fr d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-of f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , subs-of d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-empty f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , subs-empty d′ , cong suc e₁ , eq , h′
  subscribeE-off {sched = sched} (subs-takeWhile refl sub) st refl ph s h =
    let ne = <→≢ᵇ (lt s)
        (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub (installNode (nodeCt sched) (take-st (suc zero)) st)
                                     (ov-set st (nodeCt sched) (take-st (suc zero)) ne h)
                                     (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
                                     (has-set st (nodeCt sched) (take-st (suc zero)) ne h)
    in r′ , subs-takeWhile refl d′ , cong suc e₁ , eq , h′
  subscribeE-off {sched = sched} (subs-batchSync {u = u} refl sub f) st refl ph s h
    with subscribeE-off sub (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st)
           (ov-set st (nodeCt sched) (batchSync-st true [] false) (<→≢ᵇ (lt s)) h)
           (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
           (has-set st (nodeCt sched) (batchSync-st true [] false) (<→≢ᵇ (lt s)) h)
  ... | (o₁ , sc₁ , s₁) , d₁ , e₁ , refl , h₁
    with foldPath-off f (installNode (nodeCt sched) (batchDown u (lookupNode (nodeCt sched) (EvalSt.nodes s₁))) s₁)
           (trans (cong (λ m → installNode (nodeCt sched) (batchDown u m) (ov s₁)) (look-ov s₁ (nodeCt sched) (<→≢ᵇ (lt s))))
                  (ov-set s₁ (nodeCt sched) _ (<→≢ᵇ (lt s)) h₁))
           (push (fresh-off (lt s)) (fresh-off (lt s)) ph)
           (let s₂ = subscribeE-floor sub (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
            in si (NI-fresh (lt s) (ni s₂)) (ea s₂) (lt s₂) (rm s₂))
           (has-set s₁ (nodeCt sched) _ (<→≢ᵇ (lt s)) h₁)
  ...   | (o₂ , sc₂ , s₂) , d₂ , e₂ , refl , h₂ =
    _ , subs-batchSync refl d₁ d₂ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂
  subscribeE-off (subs-map sub) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub st refl (push (λ ()) (λ ()) ph) s h in r′ , subs-map d′ , cong suc e₁ , eq , h′
  subscribeE-off {sched = sched} (subs-scan refl sub) st refl ph s h =
    let ne = <→≢ᵇ (lt s)
        (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub (installNode (nodeCt sched) _ st)
                                     (ov-set st (nodeCt sched) _ ne h)
                                     (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
                                     (has-set st (nodeCt sched) _ ne h)
    in r′ , subs-scan refl d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-flatten sa) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeAll-off sa st refl ph s h in r′ , subs-flatten d′ , cong suc e₁ , eq , h′
  subscribeE-off (subs-μ sub) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub st refl ph s h in r′ , subs-μ d′ , cong suc e₁ , eq , h′
  subscribeE-off {lo = lo} {κ = κ} {sched = sched} (subs-defer {src = src} {rid = rid} refl f₂ f₃ f₄) st refl ph s h =
    _ , subs-defer refl f₂ f₃ f₄ , refl
      , under₂
          (trans (cong (register rid (atDyn src lo) p) (ov-set st (nodeCt sched) (mergeAll-st nothing 0 [] false) ne h))
                 (register-ov (installNode (nodeCt sched) (mergeAll-st nothing 0 [] false) st) rid (atDyn src lo) p
                   (pi-off (push {f = thru-outer mergeAllᵒ (nodeCt sched)} {le = ≤-refl} (fresh-off (lt s)) (fresh-off (lt s)) ph))))
      , has-set st (nodeCt sched) _ ne h
    where
    ne = <→≢ᵇ (lt s)
    p  = thru-outer mergeAllᵒ (nodeCt sched) ↠[ ≤-refl ] κ
  subscribeE-off (subs-mint fr sub) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub st refl ph (si (ni s) (ea s) (lt s) (rm s)) h
    in r′ , subs-mint fr d′ , cong suc e₁ , eq , h′

  subscribeSharedSlot-off sl (slot-spent m f) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = foldPath-off f st refl ph s h in r′ , slot-spent m d′ , cong suc e₁ , eq , h′
  subscribeSharedSlot-off {i = i} {κ = κ} {below = below} sl (slot-join {rid = rid} m₁ m₂ fr) st refl ph s h =
    _ , slot-join m₁ m₂ fr , refl
      , under₂ (register-ov st rid (atSlot i) (lowerFloor below κ) (lower-off below κ ph)) , h
  subscribeSharedSlot-off {i = i} {d = dd} {ok = ok} {κ = κ} {below = below} sl
                          (slot-connect m₁ nm (connect {rid = rid} fr sub)) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) =
          subscribeE-off sub st₂ (register-ov st₁ rid (atSlot i) (lowerFloor below κ) (lower-off below κ ph))
            (pᵢ tt (λ ()) λ { _ refl → inj₂ fr′ })
            (si (ni s) (ea-reg (ea s) (lower-PI below κ ph)) (lt s) (keeps-trans (rm s) (keeps-cons _ _ _))) h
    in r′ , slot-connect m₁ nm (connect fr d′) , cong (λ z → suc (suc z)) e₁ , eq , h′
    where
    st₁ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
    st₂ = register rid (atSlot i) (lowerFloor below κ) st₁
    fr′ : Fresh i
    fr′ = dd , ok , trans (cong (λ f → f i) (sym (KeepsC.table (rm s)))) sl
        , still-out {cs = EvalSt.connectedShares st} (toℕ i) (KeepsC.mem (rm s)) nm

  subscribeAll-off {ns = ns} {sched = sched} (sub-all refl sub) st refl ph s h =
    let ne = <→≢ᵇ (lt s)
        (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub (installNode (nodeCt sched) ns st) (ov-set st (nodeCt sched) ns ne h)
                                     (push (fresh-off (lt s)) (fresh-off (lt s)) ph) (fresh-SI _ s)
                                     (has-set st (nodeCt sched) ns ne h)
    in r′ , sub-all refl d′ , cong suc e₁ , eq , h′

  subscribeInner-off (inner refl sub) st refl pa s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeE-off sub st refl (fresh-PI (lt s) pa)
                                     (si (ni s) (ea s) (<-≤-trans (lt s) (n≤1+n _)) (rm s)) h
    in _ , inner refl d′ , cong suc e₁ , cong (λ z → _ , z) eq , h′

  stepFrame-off step-map st refl pf s h = _ , step-map , refl , refl , h
  stepFrame-off (step-scan {fn = fn} {nid = c} {vals = vals} {fin} {sched}) st refl pf s h =
    _ , step-scan , refl
      , trans (cong (λ m → injectRoot (scanDispatch fn c vals fin sched (ov st) m)) (look-ov st c ne))
              (cong injectRoot (scan-ov fn c vals fin sched st (lookupNode c (EvalSt.nodes st)) ne h))
      , has-via (scanOff fn c vals fin sched st (lookupNode c (EvalSt.nodes st)) k ne) h
    where ne = notIn₁ {c} {k} (proj₁ pf)
  stepFrame-off (step-take {w = w} {nid = c} {vals = vals} {fin} {sched}) st refl pf s h =
    _ , step-take , refl
      , trans (cong (λ m → injectRoot (takeDispatch w c vals fin sched (ov st) m)) (look-ov st c ne))
              (cong injectRoot (take-ov w c vals fin sched st (lookupNode c (EvalSt.nodes st)) ne h))
      , has-via (takeOff w c (lookupNode c (EvalSt.nodes st)) vals fin sched st k ne) h
    where ne = notIn₁ {c} {k} (proj₁ pf)
  stepFrame-off (step-batchSync {s = u} {nid = c} {vals = vals} {fin} {sched}) st refl pf s h =
    _ , step-batchSync , refl
      , trans (cong (λ m → injectRoot {u = u ×ᵗ listᵗ u} (batchDispatch {s = u} c vals fin sched (ov st) m)) (look-ov st c ne))
              (cong (injectRoot {u = u ×ᵗ listᵗ u}) (batch-ov {s = u} c vals fin sched st (lookupNode c (EvalSt.nodes st)) ne h))
      , has-via (batchOff c vals fin sched st (lookupNode c (EvalSt.nodes st)) k ne) h
    where ne = notIn₁ {c} {k} (proj₁ pf)
  stepFrame-off (step-from-inner rr) st refl pf s h =
    let (r′ , d′ , e₁ , eq , h′) = innerReact-off rr st refl pf s h in r′ , step-from-inner d′ , cong suc e₁ , eq , h′
  stepFrame-off (step-thru-outer {op = op} {nid = c} {fin = fin} w) st refl pf s h
    with thruWalk-off w st refl (notIn₁ {c} {k} (proj₁ pf)) (proj₂ (proj₂ pf)) s h
  ... | (o , sc , s′) , w′ , e₁ , refl , h′ =
    _ , step-thru-outer w′ , cong suc e₁
      , cong (λ z → o , [] , z) (wrap-ov op c fin sc s′ (notIn₁ {c} {k} (proj₁ pf)) h′)
      , has-via (Wrapped.off (wrap-facts op c fin sc s′) k (notIn₁ {c} {k} (proj₁ pf))) h′

  thruWalk-off walk-nil st refl ne ph s h = _ , walk-nil , refl , refl , h
  thruWalk-off (walk-echo f w) st refl ne ph s h
    with foldPath-off f st refl ph s h
  ... | (o₁ , sc₁ , s₁) , f′ , e₁ , refl , h₁
    with thruWalk-off w s₁ refl ne ph (foldPath-floor f ph s) h₁
  ...   | (o₂ , sc₂ , s₂) , w′ , e₂ , refl , h₂ =
    _ , walk-echo f′ w′ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂
  thruWalk-off (walk-cons c w) st refl ne ph s h
    with thruConsume-off c st refl ne ph s h
  ... | (o₁ , sc₁ , s₁) , c′ , e₁ , refl , h₁
    with thruWalk-off w s₁ refl ne ph (thruConsume-floor c ne ph s) h₁
  ...   | (o₂ , sc₂ , s₂) , w′ , e₂ , refl , h₂ =
    _ , walk-cons c′ w′ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂

  thruConsume-off {a = a} (consume-all-sub lk room c) st refl ne ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeInner-off c (installNode a _ st) (ov-set st a _ ne h) (thru-PA ne ph)
                                     (si (NI-off {a} ne (ni s)) (ea s) (lt s) (rm s)) (has-set st a _ ne h)
    in _ , consume-all-sub (trans (sym (look-ov st a ne)) lk) room d′ , cong suc e₁ , cong proj₂ eq , h′
  thruConsume-off {a = a} (consume-all-enqueue lk room) st refl ne ph s h =
    _ , consume-all-enqueue (trans (sym (look-ov st a ne)) lk) room , refl
      , under₂ (ov-set st a _ ne h) , has-set st a _ ne h
  thruConsume-off {a = a} (consume-all-nil u) st refl ne ph s h =
    _ , consume-all-nil (trans (cong (consumeUsable mergeAllᵒ _) (sym (look-ov st a ne))) u) , refl , refl , h
  thruConsume-off {a = a} {sched = sched} (consume-switch-sub {cur = cur} lk kl fr c) st refl ne ph s h
    with trans (sym kl) (kill-ov cur sched st)
  ... | refl
    with subscribeInner-off c (installNode a _ (proj₂ (switchKill cur sched st)))
           (ov-set (proj₂ (switchKill cur sched st)) a _ ne (kill-has cur sched st h)) (thru-PA ne ph)
           (let s₁ = subst (λ p → SI (proj₁ p) (proj₂ p)) kl (kill-SI cur s)
            in si (NI-off {a} ne (ni s₁)) (ea s₁) (lt s₁) (rm s₁))
           (has-set (proj₂ (switchKill cur sched st)) a _ ne (kill-has cur sched st h))
  ...   | (i₁ , o₁ , sc₁ , s₁) , d′ , e₁ , refl , h′ =
    _ , consume-switch-sub (trans (sym (look-ov st a ne)) lk) refl fr d′ , cong suc e₁ , refl , h′
  thruConsume-off {a = a} (consume-switch-nil u) st refl ne ph s h =
    _ , consume-switch-nil (trans (cong (consumeUsable switchᵒ _) (sym (look-ov st a ne))) u) , refl , refl , h
  thruConsume-off {a = a} (consume-exhaust-sub lk c) st refl ne ph s h =
    let (r′ , d′ , e₁ , eq , h′) = subscribeInner-off c (installNode a _ st) (ov-set st a _ ne h) (thru-PA ne ph)
                                     (si (NI-off {a} ne (ni s)) (ea s) (lt s) (rm s)) (has-set st a _ ne h)
    in _ , consume-exhaust-sub (trans (sym (look-ov st a ne)) lk) d′ , cong suc e₁ , cong proj₂ eq , h′
  thruConsume-off {a = a} (consume-exhaust-nil u) st refl ne ph s h =
    _ , consume-exhaust-nil (trans (cong (consumeUsable exhaustᵒ _) (sym (look-ov st a ne))) u) , refl , refl , h

  innerReact-off react-false st refl pf s h = _ , react-false , refl , refl , h
  innerReact-off (react-alive al) st refl pf s h = _ , react-alive al , refl , refl , h
  innerReact-off {a = a} {inst = inst} (react-dead al f) st refl pf s h =
    let (r′ , f′ , e₁ , eq , h′) =
          innerFinish-off f st refl pf
            (λ eq → subst (λ k′ → waiting (lookupNode k′ (EvalSt.nodes (ov st))) ≤ waiting (just y)) (sym eq) (NI.nw (ni s))) s h
        (d′ , e₂) = dead-at (look-ov st a (notIn₂ {a} {inst} {k} (proj₁ pf refl))) al f′
    in r′ , d′ , trans e₂ (cong suc e₁) , eq , h′

  innerFinish-off {op = op} {a} {inst} (finish-all-drain fp dr) st refl pf wm s h
    with foldPath-off fp st refl (proj₂ (proj₂ pf)) s h
  ... | (o₁ , sc₁ , s₁) , fp′ , e₁ , refl , h₁
    with mergeAllDrain-off dr s₁ refl (pa-of {op = op} {j = inst} pf) (foldPath-floor fp (proj₂ (proj₂ pf)) s , wm) h₁
  ...   | (o₂ , a₂ , q₂ , sc₂ , s₂) , dr′ , e₂ , refl , h₂ =
    _ , finish-all-drain fp′ dr′ , cong₂ (λ x z → suc (x + z)) e₁ e₂
      , cong (λ z → _ , [] , _ , sc₂ , z) (ov-set s₂ a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h₂)
      , has-set s₂ a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h₂
  innerFinish-off {a = a} {inst} (finish-switch-clear cq) st refl pf wm s h =
    _ , finish-switch-clear cq , refl
      , cong (λ z → [] , _ , _ , _ , z) (ov-set st a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h)
      , has-set st a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h
  innerFinish-off {a = a} {inst} finish-exhaust-clear st refl pf wm s h =
    _ , finish-exhaust-clear , refl
      , cong (λ z → [] , _ , _ , _ , z) (ov-set st a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h)
      , has-set st a _ (notIn₂ {a} {inst} {k} (proj₁ pf refl)) h
  innerFinish-off (finish-nil u) st refl pf wm s h = _ , finish-nil u , refl , refl , h

  mergeAllDrain-off drain-spent       st refl pa sw h = _ , drain-spent , refl , refl , h
  mergeAllDrain-off drain-nil         st refl pa sw h = _ , drain-nil , refl , refl , h
  mergeAllDrain-off (drain-no-room nr) st refl pa sw h = _ , drain-no-room nr , refl , refl , h
  mergeAllDrain-off {a = a} (drain-room room c dq dr) st refl pa (s , w) h
    with subscribeInner-off c (installNode a _ st) (ov-set st a _ (proj₂ (proj₂ pa) refl) h) pa
           (si (NI-set a _ _ (ni s) (λ e′ → pa-inl pa e′ , ≤-trans (n≤1+n _) (w e′))) (ea s) (lt s) (rm s))
           (has-set st a _ (proj₂ (proj₂ pa) refl) h)
  ... | (i₁ , o₁ , sc₁ , s₁) , c′ , e₁ , refl , h₁
    with mergeAllDrain-off dr s₁ refl pa
           (reread dq (subscribeInner-floor c pa
             (si (NI-set a _ _ (ni s) (λ e′ → pa-inl pa e′ , ≤-trans (n≤1+n _) (w e′))) (ea s) (lt s) (rm s)))) h₁
  ...   | (o₂ , a₂ , q₂ , sc₂ , s₂) , dr′ , e₂ , refl , h₂ =
    _ , drain-room room c′ (trans (cong (drainSt _) (sym (look-ov s₁ a (proj₂ (proj₂ pa) refl)))) dq) dr′
      , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂

  foldPath-off fold-root st refl ph s h = _ , fold-root , refl , refl , h
  foldPath-off (fold-sink {i = i} dd) st refl ph s h =
    let (r′ , d′ , e₁ , eq , h′) = dispatchShare-off dd st refl (PI.pcl ph i refl) s h in r′ , fold-sink d′ , cong suc e₁ , eq , h′
  foldPath-off (fold-step sf rr) st refl ph s h
    with stepFrame-off sf st refl (pf-of ph) s h
  ... | (o₁ , v₁ , f₁ , sc₁ , s₁) , sf′ , e₁ , refl , h₁
    with foldPath-off rr s₁ refl (proj₂ (proj₂ (pf-of ph))) (stepFrame-floor sf (pf-of ph) s) h₁
  ...   | (o₂ , sc₂ , s₂) , rr′ , e₂ , refl , h₂ =
    _ , fold-step sf′ rr′ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂

  dispatchShare-off (disp {i = i} {fin = fin} w) st refl c s h =
    let (r′ , w′ , e₁ , eq , h′) = shareWalk-off w (shareDying i fin st) (dying-ov i fin st) c (dying-SI i fin s) (dying-has i fin st h)
    in _ , disp w′ , cong suc e₁ , trans (cong (shareFinish i fin) eq) (finish-ov i fin r′) , finish-has i fin r′ h′

  shareWalk-off walk-nil st refl c s h = _ , walk-nil , refl , refl , h
  shareWalk-off {i = i} (walk-end g) st refl c s h =
    let (r′ , g′ , e₁ , eq , h′) = shareGo-off g (shareSpend i st) refl (admit i c (ea s)) (si (ni s) (ea s) (lt s) (rm s)) h
    in r′ , walk-end g′ , cong suc e₁ , eq , h′
  shareWalk-off {i = i} (walk-more g w) st refl c s h
    with shareGo-off g st refl (admit i c (ea s)) s h
  ... | (o₁ , sc₁ , s₁) , g′ , e₁ , refl , h₁
    with shareWalk-off w s₁ refl c (shareGo-floor g (admit i c (ea s)) s) h₁
  ...   | (o₂ , sc₂ , s₂) , w′ , e₂ , refl , h₂ =
    _ , walk-more g′ w′ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂

  shareGo-off go-nil st refl hp s h = _ , go-nil , refl , refl , h
  shareGo-off (go-cut sk g) st refl hp s h =
    let (r′ , g′ , e₁ , eq , h′) = shareGo-off g st refl (λ m → hp (there m)) s h in r′ , go-cut sk g′ , cong suc e₁ , eq , h′
  shareGo-off (go-live {fin = fin} {rid = rid} sk f g) st refl hp s h
    with foldPath-off f (markDlv fin rid st) refl (hp (here refl)) (si (ni s) (ea s) (lt s) (rm s)) h
  ... | (o₁ , sc₁ , s₁) , f′ , e₁ , refl , h₁
    with shareGo-off g s₁ refl (λ m → hp (there m)) (foldPath-floor f (hp (here refl)) (si (ni s) (ea s) (lt s) (rm s))) h₁
  ...   | (o₂ , sc₂ , s₂) , g′ , e₂ , refl , h₂ =
    _ , go-live sk f′ g′ , cong₂ (λ x z → suc (x + z)) e₁ e₂ , refl , h₂

------------------------------------------------------------------
-- A FOLD DOWN A PATH OFF A NODE IS FRAMED BY IT: run from a table
-- holding that node, rewritten, it is the fold from the table as it
-- was, of the same size, with the rewrite laid over where it ends.
-- The node must be in the table: rewriting an absent one appends it,
-- and a node the fold installs then lands on the other side of it.
-- A share the fold connects has no reader but the one the connect
-- registers, which is the rule's `linked`.
--
-- REFUTED: `Refuted.Fold-Off-Absent`, read with
--   `git show d035ee48:agda/evidence/refuted/Refuted/Fold-Off-Absent.agda`
--   -- the node absent, a merge handed a `defer` installs past it.
------------------------------------------------------------------
fold-off : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {lo s} {κ : Path Δ lo s t} {k x y now vals fin sched st r}
         → lookupNode k (EvalSt.nodes st) ≡ just x
         → Clear k κ sched st
         → (d : foldPath⇓ {e = e} now κ vals fin sched (record st { nodes = setNode k y (EvalSt.nodes st) }) r)
         → Σ _ λ r′ → Σ (foldPath⇓ now κ vals fin sched st r′) λ d′
             → sz-foldPath d′ ≡ sz-foldPath d
             × r ≡ (proj₁ r′ , proj₁ (proj₂ r′) , record (proj₂ (proj₂ r′)) { nodes = setNode k y (EvalSt.nodes (proj₂ (proj₂ r′))) })
fold-off {e = e} {κ = κ} {k = k} {x = x} {y = y} {sched = sched} {st = st} lX (nd , so) d =
  let (r′ , d′ , e₁ , eq , _) = foldPath-off d st refl pi₀ s₀ (has x lX) in r′ , d′ , e₁ , eq
  where
  open Off {e = e} k y (endOf κ) (Sched.slots sched) (EvalSt.connectedShares st)
  open Watch {e = e} false k (endOf κ) (waiting (just y)) (just y) (Sched.slots sched) (EvalSt.connectedShares st)
  pi₀ = pᵢ (off-ok κ (off-path nd)) (λ h → ⊥-elim (off-path nd h)) (λ i eq → inj₁ (clear-self (endOf κ) i eq))
  s₀ = si (nᵢ (subst (λ h → waiting h ≤ waiting (just y)) (sym (lookup-set k y (EvalSt.nodes st))) ≤-refl)
              (λ _ → lookup-set k y (EvalSt.nodes st)))
          (ea-start refl refl (at-end nd) (linked-ov (linked (ruled so)))) (node-below nd) (keeps-refl _ _)
