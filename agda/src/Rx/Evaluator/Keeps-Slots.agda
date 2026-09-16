------------------------------------------------------------------
-- THE SLOT TABLE IS INERT ACROSS A SUBSCRIPTION.
------------------------------------------------------------------

-- WHAT THIS ESTABLISHES, AND WHY IT IS ONE BLOCK.  The report's
-- premises are denominated at one `slotDepth sl` the caller fixes, and
-- the walk carries the agreement `Sched.slots sched ≡ sl` down every
-- recursion for free -- but a clause that hands a LATER schedule onward
-- has to say that the table survived the hand-off.  It does: no
-- constructor of the subscribe family writes `slots`, so the equation is
-- `refl` at every leaf and a recursion everywhere else.  The block is
-- the family's own SCC, because the relation is mutually defined and a
-- proof over it cannot be split any finer than the relation is.
--
-- AND IT IS A STRUCTURAL INDUCTION OVER THE RELATION, NOT OVER THE
-- BUILDER.  A derivation is an inductive datatype, so recursion on one
-- is structural whatever well-founded apparatus the builder that
-- PRODUCES it needs -- the builder's measure is a property of the
-- builder and never of the relation it inhabits.
module Rx.Evaluator.Keeps-Slots where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; obs; Fn; _×ᵗ_; _≟ᵗ_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId;
  NodeState; Frame; take-st; scan-st; takeVals; takeDispatch;
  scanDispatch; thruWrap;
  switchKill; oneShotBurst; lookupNode; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  stepFrame⇓; innerReact⇓; innerFinish⇓; mergeAllDrain⇓; thruWalk⇓;
  thruConsume⇓; subscribeInner⇓; sharedConnect⇓; subscribeSharedSlot⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; inner;
  consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-from-inner;
  step-thru-outer; push-nil; push-cons; sub-all;
  connect-live; connect-died; slot-spent; slot-join; slot-connect)

------------------------------------------------------------------
-- THE THREE FUNCTIONS A CLAUSE HANDS A SCHEDULE TO.
------------------------------------------------------------------

-- Each is a leaf of the induction below: the clause's output schedule
-- is this function's, so the relation says nothing about it and the
-- fact has to be read off the body.

-- the mint touches `nextSource` and nothing else
oneShot-slots : ∀ {n} {Γ : Ctx n} {u}
  (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) →
  Sched.slots (proj₂ (oneShotBurst vals id sched)) ≡ Sched.slots sched
oneShot-slots vals id sched = refl

-- the cut sweeps `live`; the pass-through arm hands the schedule back
take-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  Sched.slots (proj₁ (proj₂ (proj₂ (proj₂
    (takeDispatch {e = e} nid vals fin sched st ns)))))
    ≡ Sched.slots sched
take-slots nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = refl
... | false = refl
take-slots nid vals fin sched st nothing                      = refl
take-slots nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
take-slots nid vals fin sched st (just (switch-st _ _))       = refl
take-slots nid vals fin sched st (just (exhaust-st _ _))      = refl
take-slots nid vals fin sched st (just (scan-st _))           = refl

-- the fold rewrites its accumulator and passes the schedule through
scan-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ)) →
  Sched.slots (proj₁ (proj₂ (proj₂ (proj₂
    (scanDispatch {e = e} fn nid vals fin sched st ns)))))
    ≡ Sched.slots sched
scan-slots {u = u} fn nid vals fin sched st (just (scan-st {w} a))
  with w ≟ᵗ u
... | no  _    = refl
... | yes refl = refl
scan-slots fn nid vals fin sched st nothing                      = refl
scan-slots fn nid vals fin sched st (just (take-st _))           = refl
scan-slots fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
scan-slots fn nid vals fin sched st (just (switch-st _ _))       = refl
scan-slots fn nid vals fin sched st (just (exhaust-st _ _))      = refl

-- the wrap rewrites a node and passes the schedule straight through
wrap-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List _ × Sched Γ × EvalSt e) →
  Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r)))))
    ≡ Sched.slots (proj₁ (proj₂ (proj₂ r)))
wrap-slots op nid false r = refl
wrap-slots mergeAllᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
... | just (take-st _)           = refl
... | just (scan-st _)           = refl
... | nothing                    = refl
wrap-slots switchᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
... | just (take-st _)           = refl
... | just (scan-st _)           = refl
... | nothing                    = refl
wrap-slots exhaustᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
... | just (take-st _)           = refl
... | just (scan-st _)           = refl
... | nothing                    = refl

-- the kill severs registrations and sweeps `live`.  It is stated over
-- the whole triple rather than over a named schedule because both
-- consumers reach it through a `with … in`, which hands back the
-- equation at the tuple the pattern bound.
switchKill-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) {res} →
  switchKill cur sched st ≡ res →
  Sched.slots (proj₁ (proj₂ res)) ≡ Sched.slots sched
switchKill-slots nothing  sched st refl = refl
switchKill-slots (just v) sched st refl = refl

------------------------------------------------------------------
-- THE WALK.
------------------------------------------------------------------

mutual

  subs-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  subs-keeps (subs-floor _)          = refl
  subs-keeps (subs-shared _ s)       = slot-keeps s
  subs-keeps (subs-hot-done _ _ _)   = refl
  subs-keeps (subs-hot-live _ _ _)   = refl
  subs-keeps {sched = sched} (subs-cold-sync {sync = sync} {id = id} _ _ refl) =
    oneShot-slots sync id sched
  subs-keeps (subs-cold-async _ _ _ _) = refl
  subs-keeps {sched = sched} (subs-of {ts = ts} {id = id} refl) = refl
  subs-keeps {sched = sched} (subs-empty {id = id} refl) = refl
  subs-keeps (subs-map d p)          = trans (push-keeps p) (subs-keeps d)
  subs-keeps (subs-take-zero _ refl) = refl
  subs-keeps (subs-take-suc _ refl d p) = trans (push-keeps p) (subs-keeps d)
  subs-keeps (subs-scan refl d p)    = trans (push-keeps p) (subs-keeps d)
  subs-keeps (subs-merge-all a)      = all-keeps a
  subs-keeps (subs-switch-all a)     = all-keeps a
  subs-keeps (subs-exhaust-all a)    = all-keeps a
  subs-keeps (subs-μ d)              = subs-keeps d
  subs-keeps (subs-defer _ _ _)      = refl

  all-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {ns : NodeState Γ} {b : Closed Γ (obs u)}
    {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeAll⇓ {e = e} op ns b κ id now sched st (burst , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  all-keeps (sub-all refl d p) = trans (push-keeps p) (subs-keeps d)

  inner-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {allNid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {inst : NodeId} {vs : List (Val Γ u)} {bs : List _} {done : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeInner⇓ {e = e} op allNid κ id now o sched st
      (inst , vs , bs , done , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  inner-keeps (inner refl d _) = subs-keeps d

  push-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {f : Frame Γ s u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {ems : Stream Γ s} {sched : Sched Γ} {st : EvalSt e}
    {rest : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} →
    pushBurst⇓ {e = e} id now f κ ems sched st (rest , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  push-keeps push-nil            = refl
  push-keeps (push-cons _ sf ps) = trans (push-keeps ps) (step-keeps sf)

  step-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
    {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
    {vals : List (Val Γ s)} {fin : Bool} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    stepFrame⇓ {e = e} id now fr κ vals fin sched st
      (vals′ , evs , fin′ , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  step-keeps step-map        = refl
  step-keeps {vals = vals} {fin = fin} {sched = sched} {st = st}
             (step-scan {fn = fn} {nid = nid}) =
    scan-slots fn nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  step-keeps {id = id} {now = now} {vals = vals} {fin = fin}
             {sched = sched} {st = st} (step-take {nid = nid}) =
    take-slots nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  step-keeps (step-from-inner r) = react-keeps r
  step-keeps {id = id} {now = now} {fin = fin} (step-thru-outer {op = op}
             {nid = nid} w) = trans (wrap-slots op nid fin _) (walk-keeps w)

  react-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {op : AllOp} {allNid inst : NodeId} {κ : Path Γ lo s t}
    {id : Id} {now : Tick} {vals : List (Val Γ s)}
    {sched : Sched Γ} {st : EvalSt e} {fin : Bool}
    {vals′ : List (Val Γ s)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    innerReact⇓ {e = e} op allNid inst κ id now vals sched st fin
      (vals′ , evs , fin′ , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  react-keeps react-false        = refl
  react-keeps (react-alive _)    = refl
  react-keeps (react-dead _ f)   = finish-keeps f

  finish-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {op : AllOp} {allNid inst : NodeId} {κ : Path Γ lo s t}
    {id : Id} {now : Tick} {vals : List (Val Γ s)}
    {sched : Sched Γ} {st : EvalSt e} {ns : Maybe (NodeState Γ)}
    {vals′ : List (Val Γ s)} {evs : List _} {fin′ : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    innerFinish⇓ {e = e} op allNid inst κ id now vals sched st ns
      (vals′ , evs , fin′ , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  finish-keeps (finish-all-drain d)     = drain-keeps d
  finish-keeps (finish-switch-clear _)  = refl
  finish-keeps finish-exhaust-clear     = refl
  finish-keeps finish-nil               = refl

  drain-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {allNid : NodeId} {κ : Path Γ lo s t} {id : Id} {now : Tick}
    {lim : Maybe ℕ} {act : ℕ} {od : Bool} {q : List (Closed Γ s)}
    {sched : Sched Γ} {st : EvalSt e}
    {vs : List (Val Γ s)} {bs : List _} {act′ : ℕ} {q′ : List (Closed Γ s)}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    mergeAllDrain⇓ {e = e} allNid κ id now lim act od q sched st
      (vs , bs , act′ , q′ , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  drain-keeps drain-nil          = refl
  drain-keeps (drain-no-room _)  = refl
  drain-keeps (drain-room _ i d) = trans (drain-keeps d) (inner-keeps i)

  walk-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {os : List (Val Γ (obs u))} {sched : Sched Γ} {st : EvalSt e}
    {vs : List (Val Γ u)} {bs : List _}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    thruWalk⇓ {e = e} op nid κ id now os sched st (vs , bs , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  walk-keeps walk-nil        = refl
  walk-keeps (walk-cons c w) = trans (walk-keeps w) (consume-keeps c)

  consume-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {id : Id} {now : Tick}
    {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
    {vals′ : List (Val Γ u)} {evs : List _}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (vals′ , evs , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  consume-keeps (consume-all-sub _ _ i)     = inner-keeps i
  consume-keeps (consume-all-enqueue _ _)   = refl
  consume-keeps consume-all-nil             = refl
  consume-keeps (consume-switch-sub {sched₀ = sched₀} {st₀ = st₀} {cur = cur}
                _ k i) =
    trans (inner-keeps i) (switchKill-slots cur sched₀ st₀ k)
  consume-keeps consume-switch-nil          = refl
  consume-keeps (consume-exhaust-sub _ i)   = inner-keeps i
  consume-keeps consume-exhaust-nil         = refl

  connect-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {i : Fin n} {d : Closed Γ (lookup Γ i)}
    {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
    {id : Id} {now : Tick} {sched : Sched Γ} {st : EvalSt e}
    {burst : Stream Γ (lookup Γ i)} {sched′ : Sched Γ} {st′ : EvalSt e} →
    sharedConnect⇓ {e = e} i d κ below id now sched st
      (burst , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  connect-keeps (connect-live d _) = subs-keeps d
  connect-keeps (connect-died d _) = subs-keeps d

  slot-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {i : Fin n} {d : Closed Γ (lookup Γ i)}
    {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
    {id : Id} {now : Tick} {sched : Sched Γ} {st : EvalSt e}
    {burst : Stream Γ (lookup Γ i)} {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeSharedSlot⇓ {e = e} i d κ below id now sched st
      (burst , sched′ , st′) →
    Sched.slots sched′ ≡ Sched.slots sched
  slot-keeps (slot-spent _)      = refl
  slot-keeps (slot-join _ _)     = refl
  slot-keeps (slot-connect _ _ c) = connect-keeps c
