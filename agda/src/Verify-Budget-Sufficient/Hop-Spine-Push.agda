------------------------------------------------------------------
-- SCAN'S PUSH FACE, on the hop ledger.
--
-- `subscribeE` at a `scanᵉ` mints a node, subscribes the source under a
-- `scan-f` frame, and pushes the source's burst through that frame
-- (Rx.Evaluator, the scanᵉ clause).  `pushBurst` walks the burst emit
-- by emit; `stepFrame` at a `scan-f` reads the node's accumulator, runs
-- `scanVals` over the emit's values, and writes the last accumulator
-- back.  So the hop receipt for a scan subscription is this walk, and
-- its per-emit content is exactly `scanVals-hopSpn`.
--
-- THE STATE IS THE REASON THIS IS ITS OWN FACE, and why the family's
-- shared header says a frame-generic push face is refuted: the
-- accumulator lives in the node table, not in the burst, so the
-- invariant has to be carried ACROSS emits.  `scanAccSpn?` is that
-- carrier — the node's stored accumulator satisfies `valHopSpn?` — and
-- the walk both consumes and re-establishes it.  `lookupNode-setNode`
-- and `≟ᵗ-refl` (.Node-Table) are what make the written-then-read node
-- reduce.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Push where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; _≤_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Fin  using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Prim  using (InstEmit; InstEvent; init; value; close;
                            handoff; complete; Gas; Id; Tick)
open import Rx.Exp   using (Ty; Ctx; Val; Fn; Closed; _≟ᵗ_; _×ᵗ_)
open import Rx.Hop-Depth using (hopDᵗ; pmᵗ)
open import Rx.Evaluator using (Stream; EvalSt; Sched; Path; NodeId; NodeState;
                                scan-st; take-st; merge-st; concat-st;
                                switch-st; exhaust-st; scan-f;
                                lookupNode; setNode; splitEvents; retagEvents;
                                pushBurst; stepFrame; scanVals)
open import Verify-Budget-Sufficient.Node-Table using (≟ᵗ-refl; lookupNode-setNode)
open import Verify-Budget-Sufficient.Measures using
  (∧-true; ∧-intro; all-++-intro)
open import Verify-Budget-Sufficient.Hop-Spine-Face using
  (valHopSpn?; evHopSpnH?; burstHopSpnH?)
open import Verify-Budget-Sufficient.Hop-Spine-Step using (scanVals-hopSpn)

------------------------------------------------------------------
-- THE CARRIER.  A node the walk does not own reads as `true`: only a
-- `scan-st` at the matching payload type is a scan accumulator, and
-- `stepFrame` emits nothing in every other case, so there is nothing
-- to bound.
------------------------------------------------------------------

nodeAccSpn? : ∀ {n} {Γ : Ctx n} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
              (u : Ty) → Maybe (NodeState Γ) → Bool
nodeAccSpn? V η P B u nothing                  = true
nodeAccSpn? V η P B u (just (take-st _))       = true
nodeAccSpn? V η P B u (just (merge-st _ _))    = true
nodeAccSpn? V η P B u (just (concat-st _ _ _)) = true
nodeAccSpn? V η P B u (just (switch-st _ _))   = true
nodeAccSpn? V η P B u (just (exhaust-st _ _))  = true
nodeAccSpn? V η P B u (just (scan-st {w} acc)) with w ≟ᵗ u
... | yes refl = valHopSpn? V η P B u acc
... | no _     = true

scanAccSpn? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → ℕ → (Fin n → ℕ) →
              ℕ → ℕ → (u : Ty) → NodeId → EvalSt e → Bool
scanAccSpn? V η P B u nid st =
  nodeAccSpn? V η P B u (lookupNode nid (EvalSt.nodes st))

------------------------------------------------------------------
-- SPLITTING AN EMIT.  Values carry the predicate; bookkeeping carries
-- it vacuously, and `splitEvents` sorts the two apart.
------------------------------------------------------------------

splitEvents-vals : ∀ {n} {Γ : Ctx n} {u} {A : Set} (V : ℕ) (η : Fin n → ℕ)
  (P B : ℕ) (es : List (InstEvent (Val Γ u))) →
  all (evHopSpnH? V η P B) es ≡ true →
  all (valHopSpn? V η P B u) (proj₁ (splitEvents {A = A} es)) ≡ true
splitEvents-vals V η P B []               h = refl
splitEvents-vals V η P B (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals V η P B es (proj₂ (∧-true _ _ h)))
splitEvents-vals V η P B (init s   ∷ es) h = splitEvents-vals V η P B es (proj₂ (∧-true _ _ h))
splitEvents-vals V η P B (close s r ∷ es) h = splitEvents-vals V η P B es (proj₂ (∧-true _ _ h))
splitEvents-vals V η P B (handoff s ∷ es) h = splitEvents-vals V η P B es (proj₂ (∧-true _ _ h))
splitEvents-vals V η P B (complete ∷ es) h = splitEvents-vals V η P B es (proj₂ (∧-true _ _ h))

-- the bookkeeping half carries no value at all, so it satisfies the
-- predicate by computation whatever the payload type it is retagged to
splitEvents-book : ∀ {n} {Γ : Ctx n} {u w} (V : ℕ) (η : Fin n → ℕ)
  (P B : ℕ) (es : List (InstEvent (Val Γ u))) →
  all (evHopSpnH? {Γ = Γ} {u = w} V η P B)
      (proj₁ (proj₂ (splitEvents {A = Val Γ w} es))) ≡ true
splitEvents-book V η P B []                = refl
splitEvents-book V η P B (value v   ∷ es) = splitEvents-book V η P B es
splitEvents-book V η P B (init s    ∷ es) = splitEvents-book V η P B es
splitEvents-book V η P B (close s r ∷ es) = splitEvents-book V η P B es
splitEvents-book V η P B (handoff s ∷ es) = splitEvents-book V η P B es
splitEvents-book V η P B (complete  ∷ es) = splitEvents-book V η P B es

map-value-hopSpn : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (vs : List (Val Γ u)) → all (valHopSpn? V η P B u) vs ≡ true →
  all (evHopSpnH? V η P B) (map value vs) ≡ true
map-value-hopSpn V η P B []       h = refl
map-value-hopSpn V η P B (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (map-value-hopSpn V η P B vs (proj₂ (∧-true _ _ h)))

fin-hopSpn : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) (fin : Bool) →
  all (evHopSpnH? {Γ = Γ} {u = u} V η P B) (if fin then complete ∷ [] else []) ≡ true
fin-hopSpn V η P B true  = refl
fin-hopSpn V η P B false = refl

-- the stuck `with` inside nodeAccSpn? unblocks exactly here: ≟ᵗ-refl is
-- what turns the installed-then-read node back into its accumulator
nodeAccSpn?-scan : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u : Ty) (acc : Val Γ u) →
  nodeAccSpn? V η P B u (just (scan-st acc)) ≡ valHopSpn? V η P B u acc
nodeAccSpn?-scan V η P B u acc rewrite ≟ᵗ-refl u = refl

-- and the other arm: a scan node at a DIFFERENT payload type is not this
-- walk's node, `stepFrame` emits nothing for it, and the carrier is vacuous
nodeAccSpn?-scan-off : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u w : Ty) (acc : Val Γ w) → ¬ (w ≡ u) →
  nodeAccSpn? V η P B u (just (scan-st acc)) ≡ true
nodeAccSpn?-scan-off V η P B u w acc ne with w ≟ᵗ u
... | yes p = ⊥-elim (ne p)
... | no  _ = refl

------------------------------------------------------------------
-- ONE EMIT.  The dispatch has eight arms and seven of them emit
-- nothing: a node that is absent, or is not a scan, or is a scan at a
-- different payload type, makes `stepFrame` return the empty list and
-- leave the state alone, so all three conjuncts hold by computation.
-- The eighth is the fold.
------------------------------------------------------------------

-- the node is taken as a PARAMETER with its lookup equation, rather than
-- scrutinised by `with`: `dispatch` puts the state back after it reduces,
-- so a with-abstraction loses the very hypothesis the next emit needs.
-- The equation survives that and hands it back by `subst`.
stepFrame-scan-hopSpn-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (nd : Maybe (NodeState Γ)) →
  lookupNode nid (EvalSt.nodes st) ≡ nd →
  nodeAccSpn? V η P B u nd ≡ true →
  pmᵗ V 0 fn ≤ P → hopDᵗ V η fn ≤ B →
  all (valHopSpn? V η P B s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in (all (valHopSpn? V η P B u) (proj₁ r) ≡ true)
   × (all (evHopSpnH? {Γ = Γ} {u = u} V η P B) (retagEvents (proj₁ (proj₂ r))) ≡ true)
   × (scanAccSpn? V η P B u nid (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  nothing eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (take-st _)) eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (merge-st _ _)) eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (concat-st _ _ _)) eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (switch-st _ _)) eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (exhaust-st _ _)) eq hnd hP hB hv rewrite eq =
    refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq) hnd
stepFrame-scan-hopSpn-at {u = u} V η P B g id now fn nid κ vals fin sched st
  (just (scan-st {w} acc)) eq hnd hP hB hv rewrite eq with w ≟ᵗ u
... | no  ne = refl , refl , subst (λ z → nodeAccSpn? V η P B u z ≡ true) (sym eq)
                              (nodeAccSpn?-scan-off V η P B u _ acc ne)
-- hnd arrives ALREADY reduced here: the with-abstraction on `w ≟ᵗ u`
-- unblocks nodeAccSpn?'s own dispatch, so the carrier IS the accumulator's
-- receipt and no bridge lemma is needed on the way in — only on the way out
... | yes refl = proj₂ fold , refl , acc'OK
  where
  fold = scanVals-hopSpn V η P B fn acc vals hP hB hnd hv
  acc'OK : nodeAccSpn? V η P B _
             (lookupNode nid (setNode nid
                (scan-st (proj₂ (scanVals fn acc vals))) (EvalSt.nodes st))) ≡ true
  acc'OK rewrite lookupNode-setNode nid
                   (scan-st (proj₂ (scanVals fn acc vals)))
                   (EvalSt.nodes st) =
    trans (nodeAccSpn?-scan V η P B _ (proj₂ (scanVals fn acc vals))) (proj₁ fold)

stepFrame-scan-hopSpn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  pmᵗ V 0 fn ≤ P → hopDᵗ V η fn ≤ B →
  scanAccSpn? V η P B u nid st ≡ true →
  all (valHopSpn? V η P B s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in (all (valHopSpn? V η P B u) (proj₁ r) ≡ true)
   × (all (evHopSpnH? {Γ = Γ} {u = u} V η P B) (retagEvents (proj₁ (proj₂ r))) ≡ true)
   × (scanAccSpn? V η P B u nid (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
stepFrame-scan-hopSpn V η P B g id now fn nid κ vals fin sched st hP hB hacc hv =
  stepFrame-scan-hopSpn-at V η P B g id now fn nid κ vals fin sched st
    (lookupNode nid (EvalSt.nodes st)) refl hacc hP hB hv

------------------------------------------------------------------
-- THE WALK.  One emit at a time, threading the node's accumulator: the
-- output emit's events are the input's bookkeeping, the frame's own
-- events (none, for a scan), the fold's outputs, and a possible
-- `complete` — three of the four vacuous and the third the fold.
------------------------------------------------------------------

pushBurst-scan-hopSpn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  pmᵗ V 0 fn ≤ P → hopDᵗ V η fn ≤ B →
  scanAccSpn? V η P B u nid st ≡ true →
  burstHopSpnH? V η P B str ≡ true →
  let r = pushBurst g id now (scan-f fn nid) κ str sched st
  in (burstHopSpnH? V η P B (proj₁ r) ≡ true)
   × (scanAccSpn? V η P B u nid (proj₂ (proj₂ r)) ≡ true)
pushBurst-scan-hopSpn V η P B g id now fn nid κ [] sched st hP hB hacc h =
  refl , hacc
pushBurst-scan-hopSpn {Γ = Γ} {s = s} {u = u} V η P B g id now fn nid κ
  (em ∷ ems) sched st hP hB hacc h =
  ∧-intro emOK (proj₁ IH) , proj₂ IH
  where
  sp   = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf   = stepFrame-scan-hopSpn V η P B g id now fn nid κ
           (proj₁ sp) (proj₂ (proj₂ sp)) sched st hP hB hacc
           (splitEvents-vals V η P B (InstEmit.events em) (proj₁ (∧-true _ _ h)))
  step = stepFrame g id now (scan-f fn nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  emOK = all-++-intro (evHopSpnH? V η P B) (proj₁ (proj₂ sp)) _
           (splitEvents-book V η P B (InstEmit.events em))
           (all-++-intro (evHopSpnH? V η P B) (retagEvents (proj₁ (proj₂ step))) _
             (proj₁ (proj₂ sf))
             (all-++-intro (evHopSpnH? V η P B) (map value (proj₁ step)) _
               (map-value-hopSpn V η P B (proj₁ step) (proj₁ sf))
               (fin-hopSpn V η P B (proj₁ (proj₂ (proj₂ step))))))
  IH = pushBurst-scan-hopSpn V η P B g id now fn nid κ ems
         (proj₁ (proj₂ (proj₂ (proj₂ step))))
         (proj₂ (proj₂ (proj₂ (proj₂ step))))
         hP hB (proj₂ (proj₂ sf)) (proj₂ (∧-true _ _ h))
