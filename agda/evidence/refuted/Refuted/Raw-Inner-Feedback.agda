-- AN INNER SUBSCRIBED RAW NEED NOT TERMINATE AT A STATE `rawInner`'S
-- HYPOTHESES ADMIT, AND THE WITNESS NEEDS NO SHARE.
--
-- WHAT THIS KILLS.  `rawInner` promises a run for one inner subscribed
-- under its exit frame, from any state carrying the room, the rule for
-- the path below and the rule for the flattener's own node.  The budget
-- argument in its header says a merge's queue can outgrow a drain only
-- through a share's fan-out, and the rule's one terminus per node closes
-- that route.  But the rule is a fact about REGISTRY ROWS, and nothing
-- the hypotheses say constrains the PATH itself: in particular nothing
-- stops the path below the inner's exit frame from passing through the
-- flattener's own outer frame again.
--
-- THE STATE.  One merge, node 0, limited to one lane and busy.  The path
-- below the inner's exit frame maps every value to an observable and
-- hands it to node 0's own outer frame, then ends at the root.  The
-- registry is empty, so the rule and both node facts are vacuous, and
-- the table has no share, so the room is zero.
--
-- THE INNER EMITS ITS VALUE AND ITS END IN TWO GROUPS, and that is the
-- whole trick.  It is `mergeAll(of(of 0))`: the nested merge's finish
-- folds the value down with no end, and only the outer walk's wrap
-- sends the end.  The value crosses the map and reaches node 0's outer,
-- which finds no lane and queues the mapped observable -- the inner
-- itself.  The end then finishes node 0's lane, and the finish READS
-- the queue it just grew, frees the lane and drains it: the drained
-- inner is the same inner, under the same path, at a state with the
-- same three facts.  A value folded WITH the end could not do this,
-- because a finish reads the queue before it folds and writes back
-- what it read.
--
-- SO THE DERIVATION WOULD CONTAIN ITSELF, and the refutation is plain
-- structural recursion on it: `loop` inverts one round and lands on a
-- strictly smaller derivation at the same shape.
--
-- WHAT THE REPAIR HAS TO CARRY.  No run reaches this state: a path is
-- built by nesting subscriptions, so a flattener's outer frame is never
-- under its own inner.  The hypotheses have to say so -- the flattener's
-- node is not on the path below its exit frame -- and nothing in
-- `Sound` or `NodeOn` does.
module Refuted.Raw-Inner-Feedback where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; _≤_; _<_; _∸_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Tick)
open import Rx.Mint using (setAt; mint-init; nodeᵏ)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; Exp; Val; FnClo; ofᵉ; emptyᵉ; mergeAllᵉ; nat̂; strmᵗ; []ᵉ; _∷ᵉ_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; _↠[_]_; map-f; thru-outer; from-inner;
  AllOp; mergeAllᵒ; NodeId; NodeState; mergeAll-st; lookupNode; setNode; thruWrap; aliveThroughᶠ; consumeUsable; pathHasNode; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; thruConsume⇓; innerFinish⇓; foldPath⇓;
  subs-of; subs-merge-all; sub-all; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  walk-nil; walk-cons; drain-spent; drain-no-room; drain-room; finish-all-drain; finish-nil;
  react-false; react-alive; react-dead; step-map; step-from-inner; step-thru-outer; fold-root; fold-step)
open import Rx.Evaluator.Freshness using (nodeCt; lookup-set; set-above)
open import Rx.Evaluator.Reducible using (Room; Sound; sound; rule; NodeOn; node-on; bumpNode)

------------------------------------------------------------------
-- THE STATEMENT, COPIED FROM `rawInner` IN `Rx.Evaluator.Reducible`.
------------------------------------------------------------------

RawInner : Set
RawInner = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
             (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
           → (op : AllOp) (nid : NodeId) (κ : Path Γ ℓ u t) (now : Tick) (o : Val Γ (obs u))
             (sched : Sched Γ) (st : EvalSt e) → Room m sched st
           → Sound κ sched st → NodeOn nid κ sched st
           → Σ (Stream Γ t × Sched Γ × EvalSt e)
               (subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st)

------------------------------------------------------------------
-- THE PROGRAM PIECES.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

-- the root program is never run; it only indexes the state
e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

-- the inner: its value and its end leave in separate groups
M-body : Exp Γ₀ [] [] (natᵗ ∷ []) natᵗ
M-body = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- every value maps to the inner itself
g : FnClo Γ₀ natᵗ (obs natᵗ)
g = [] , strmᵗ M-body , []ᵉ

o : Val Γ₀ (obs natᵗ)
o = natᵗ ∷ [] , M-body , (0 ∷ᵉ []ᵉ)

-- and the path below the exit frame feeds node 0's own outer
κL : Path Γ₀ 0 natᵗ natᵗ
κL = map-f g ↠[ ≤-refl ] (thru-outer mergeAllᵒ 0 ↠[ ≤-refl ] root)

busy : List (Val Γ₀ (obs natᵗ)) → Maybe (NodeState Γ₀)
busy q = just (mergeAll-st {t = natᵗ} (just 1) 1 q false)

------------------------------------------------------------------
-- THE FACTS A ROUND CARRIES.
------------------------------------------------------------------

St : Set
St = EvalSt e₀

At0 : List (Val Γ₀ (obs natᵗ)) → St → Set
At0 q st = lookupNode 0 (EvalSt.nodes st) ≡ busy q

Reg : St → Set
Reg st = EvalSt.registry st ≡ []

true≢false : true ≡ false → ⊥
true≢false ()

-- an empty registry keeps no inner alive
dead : ∀ {inst} {st : St} → Reg st → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true → ⊥
dead {inst} {st} r x = true≢false (trans (sym x) (cong (any (aliveThroughᶠ inst st)) r))

-- the nested merge's outer end: its lane is free and its queue empty
wrapN : ∀ (nid : NodeId) (sched : Sched Γ₀) (st : St)
      → lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = natᵗ} nothing 0 [] false)
      → thruWrap {e = e₀} mergeAllᵒ nid true (sched , st)
        ≡ (true , sched , record st { nodes = setNode nid (mergeAll-st {t = natᵗ} nothing 0 [] true) (EvalSt.nodes st) })
wrapN nid sched st eq with lookupNode nid (EvalSt.nodes st)
wrapN nid sched st refl | .(just (mergeAll-st nothing 0 [] false)) = refl

------------------------------------------------------------------
-- THE ROUND'S SIDE BRANCHES, which terminate and move three facts.
------------------------------------------------------------------

-- node 0's outer meets the inner with no lane free, and queues it
consume0 : ∀ {now} {sched : Sched Γ₀} {st : St} {r}
         → At0 [] st → Reg st
         → thruConsume⇓ mergeAllᵒ 0 (root {lo = 0}) now o sched st r
         → At0 (o ∷ []) (proj₂ (proj₂ r)) × Reg (proj₂ (proj₂ r))
consume0 {st = st} a0 rg (consume-all-enqueue eq _) with trans (sym a0) eq
... | refl = lookup-set 0 _ (EvalSt.nodes st) , rg
consume0 a0 rg (consume-all-sub eq room _) with trans (sym a0) eq
... | refl = ⊥-elim (true≢false (sym room))
consume0 a0 rg (consume-all-nil u) = ⊥-elim (true≢false (trans (sym (cong (consumeUsable mergeAllᵒ natᵗ) a0)) u))

P0 : NodeId → Path Γ₀ 0 natᵗ natᵗ
P0 c = from-inner mergeAllᵒ 0 c ↠[ ≤-refl ] κL

-- the nested merge finishing its one inner: the value is folded down to
-- node 0, and the group left behind is empty and carries no end
finN : ∀ {N inst now} {sched : Sched Γ₀} {st : St} {ns} {c r}
     → (N ≡ᵇ 0) ≡ false → ns ≡ just (mergeAll-st {t = natᵗ} nothing 1 [] false)
     → At0 [] st → Reg st
     → innerFinish⇓ mergeAllᵒ N inst (P0 c) now (0 ∷ []) sched st ns r
     → proj₁ (proj₂ r) ≡ [] × proj₁ (proj₂ (proj₂ r)) ≡ false
       × lookupNode N (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ just (mergeAll-st {t = natᵗ} nothing 0 [] false)
       × At0 (o ∷ []) (proj₂ (proj₂ (proj₂ (proj₂ r)))) × Reg (proj₂ (proj₂ (proj₂ (proj₂ r))))
finN {N = N} ne refl a0 rg
  (finish-all-drain {st₂ = st₂}
    (fold-step (step-from-inner react-false) (fold-step step-map (fold-step (step-thru-outer (walk-cons c0 walk-nil)) fold-root)))
    drain-spent) =
  let (a0′ , rg′) = consume0 a0 rg c0
  in refl , refl , lookup-set N _ (EvalSt.nodes st₂) , trans (set-above N 0 _ (EvalSt.nodes st₂) ne) a0′ , rg′
finN ne refl a0 rg (finish-nil ())

-- an empty group with no end crosses node 0's exit frame and the map
-- and leaves the state as it was
quiet : ∀ {c now} {sched : Sched Γ₀} {st : St} {vs fin r}
      → vs ≡ [] → fin ≡ false
      → foldPath⇓ now (P0 c) vs fin sched st r → proj₂ (proj₂ r) ≡ st
quiet refl refl (fold-step (step-from-inner react-false) (fold-step step-map (fold-step (step-thru-outer walk-nil) fold-root))) = refl

-- the nested merge's outer meeting its one inner: the lane is free, the
-- inner is subscribed, and what comes back is node 0 grown by one
consumeN : ∀ {N c now} {sched : Sched Γ₀} {st : St} {I r}
         → (N ≡ᵇ 0) ≡ false
         → lookupNode N (EvalSt.nodes st) ≡ just (mergeAll-st {t = natᵗ} nothing 0 [] false)
         → At0 [] st → Reg st
         → I ≡ (natᵗ ∷ [] , ofᵉ (nat̂ 0 ∷ []) , (0 ∷ᵉ []ᵉ))
         → thruConsume⇓ mergeAllᵒ N (P0 c) now I sched st r
         → lookupNode N (EvalSt.nodes (proj₂ (proj₂ r))) ≡ just (mergeAll-st {t = natᵗ} nothing 0 [] false)
           × At0 (o ∷ []) (proj₂ (proj₂ r)) × Reg (proj₂ (proj₂ r))
consumeN {st = st} ne aN a0 rg refl
  (consume-all-sub eq _ (inner refl (subs-of (fold-step (step-from-inner (react-alive x)) _))))
  with trans (sym aN) eq
... | refl = ⊥-elim (dead {st = st} rg x)
consumeN {N = N} {st = st} ne aN a0 rg refl
  (consume-all-sub eq _ (inner refl (subs-of (fold-step (step-from-inner (react-dead x f)) rest))))
  with trans (sym aN) eq
... | refl =
  let (v≡ , f≡ , aN′ , a0′ , rg′) = finN ne (lookup-set N _ (EvalSt.nodes st))
                                         (trans (set-above N 0 _ (EvalSt.nodes st) ne) a0) rg f
      q≡ = quiet v≡ f≡ rest
  in  subst (λ s → lookupNode N (EvalSt.nodes s) ≡ just (mergeAll-st {t = natᵗ} nothing 0 [] false)) (sym q≡) aN′
    , subst (At0 (o ∷ [])) (sym q≡) a0′
    , subst Reg (sym q≡) rg′
consumeN ne aN a0 rg refl (consume-all-enqueue eq room) with trans (sym aN) eq
... | refl = ⊥-elim (true≢false room)
consumeN ne aN a0 rg refl (consume-all-nil u) =
  ⊥-elim (true≢false (trans (sym (cong (consumeUsable mergeAllᵒ natᵗ) aN)) u))

------------------------------------------------------------------
-- THE ROUND ITSELF: the derivation holds a strictly smaller one at the
-- same shape.
------------------------------------------------------------------

record Inv (sched : Sched Γ₀) (st : St) : Set where
  constructor inv
  field
    at0 : At0 [] st
    reg : Reg st
    ct  : (nodeCt sched ≡ᵇ 0) ≡ false

mutual
  loop : ∀ {c now} {sched : Sched Γ₀} {st : St} {r}
       → Inv sched st → subscribeE⇓ o (P0 c) now sched st r → ⊥
  loop {sched = sched} {st = st} (inv a0 rg ne)
    (subs-merge-all (sub-all refl (subs-of (fold-step (step-thru-outer (walk-cons {sched₁ = sA} {st₁ = stA} cN walk-nil)) d3)))) =
    let (aN , a0′ , rg′) = consumeN ne (lookup-set (nodeCt sched) _ (EvalSt.nodes st))
                                    (trans (set-above (nodeCt sched) 0 _ (EvalSt.nodes st) ne) a0) rg refl cN
    in afterN (wrapN (nodeCt sched) sA stA aN)
              (trans (set-above (nodeCt sched) 0 _ (EvalSt.nodes stA) ne) a0′) rg′ d3

  -- the nested merge's end reaches node 0's exit frame, whose finish
  -- drains the queue it just grew
  afterN : ∀ {c now} {sched : Sched Γ₀} {st : St} {w : Bool × Sched Γ₀ × St} {r}
         → w ≡ (true , sched , st) → At0 (o ∷ []) st → Reg st
         → foldPath⇓ now (P0 c) [] (proj₁ w) (proj₁ (proj₂ w)) (proj₂ (proj₂ w)) r → ⊥
  afterN {st = st} refl a0 rg (fold-step (step-from-inner (react-alive x)) _) = dead {st = st} rg x
  afterN refl a0 rg (fold-step (step-from-inner (react-dead x f)) _) = fin0 a0 rg f

  fin0 : ∀ {c now} {sched : Sched Γ₀} {st : St} {ns r}
       → ns ≡ busy (o ∷ []) → Reg st
       → innerFinish⇓ mergeAllᵒ 0 c κL now [] sched st ns r → ⊥
  fin0 refl rg (finish-nil ())
  fin0 refl rg (finish-all-drain (fold-step step-map (fold-step (step-thru-outer walk-nil) fold-root)) (drain-no-room ()))
  fin0 {st = st} refl rg
    (finish-all-drain (fold-step step-map (fold-step (step-thru-outer walk-nil) fold-root)) (drain-room _ (inner refl d′) _ _)) =
    loop (inv (lookup-set 0 _ (EvalSt.nodes st)) rg refl) d′

------------------------------------------------------------------
-- THE REFUTATION.
------------------------------------------------------------------

sched₀ : Sched Γ₀
sched₀ = record { mint = setAt nodeᵏ 1 (mint-init 0) ; live = [] ; slots = λ () }

st₀ : St
st₀ = record (st-init e₀) { nodes = (0 , mergeAll-st {t = natᵗ} (just 1) 1 [] false) ∷ [] }

-- the path's only node is node 0, which is below the counter
fresh₀ : ∀ k → T (pathHasNode k κL) → k < 1
fresh₀ zero    _  = s≤s z≤n
fresh₀ (suc k) ()

raw-inner-false : RawInner → ⊥
raw-inner-false ri =
  let (_ , d) = ri {Γ = Γ₀} {e = e₀} (<-wellFounded 0) z≤n (<-wellFounded 0) mergeAllᵒ 0 κL 0 o sched₀ st₀ z≤n
                   (sound (rule (λ _ ()) (λ ())) (λ _ _ ()) fresh₀) (node-on (λ ()) (s≤s z≤n))
  in loop (inv refl refl refl) d
