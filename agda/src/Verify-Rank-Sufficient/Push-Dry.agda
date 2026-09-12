------------------------------------------------------------------
-- THE BURST PIPELINE IS DRY-FREE WHEREVER IT DOES NOT HOP, and that
-- is most of it.
--
-- `pushBurst` takes a child's subscription burst and re-emits it
-- through the one frame just built above: the emit's own bookkeeping
-- survives verbatim, the frame's events are retagged in, the frame's
-- outputs are appended as values, and a completion is appended when
-- the split saw one.  Only two of those four parts can carry a close
-- at all, and NEITHER of them can carry the dry one — so the whole
-- reassembly is dry exactly when the child's burst was.
--
-- WHAT MAKES THIS A LIST INDUCTION AND NOT A DESCENT ARGUMENT is the
-- frame.  A frame reaching a deeper `subscribeE` is where a run can go
-- dry, and exactly one shape does: `thru-outer`, whose walk ends in
-- `subscribeInner` and peels the rank.  Every other frame returns a
-- bounded event list off state it already holds, so its contribution
-- is decided by reading the events it can build — which is what
-- `FrameDry` names, and what the three lemmas below discharge for the
-- three of them.
--
-- SO THE HYPOTHESIS IS THE FRAME AND NOT THE WITNESS.  `pushBurst-dry`
-- takes the accessibility witness because `stepFrame` does, and spends
-- none of it: the recursion is on the burst's spine.  That is the
-- point of stating it here rather than inside the walk — a caller with
-- a quiet frame gets dry-freedom with no arithmetic at all, and the
-- rank reading is left to the one caller that genuinely hops.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Push-Dry where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≡ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Id; Source; InstEvent; init; value; close;
  handoff; complete; InstEmit; CloseReason; cut; cutPending; exhausted; dried)
open import Rx.Exp using (Ctx; Closed; Val; Fn; _×ᵗ_; _≟ᵗ_)
open import Rx.Strat-Order using (_≺_)
open import Rx.Evaluator using (Stream; Frame; Path; Sched; EvalSt; NodeId;
  NodeState; RegId; Chain; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; map-f; scan-f; take-f; lookupNode; takeVals; cutThrough;
  takeDispatch; pathHasNode; memberSource; stepFrame; splitEvents; retagEvents; pushBurst;
  hasDry; dryEvent)

----------------------------------------------------------------------
-- Boolean plumbing.  `hasDry` and `any dryEvent` are both disjunctive
-- folds, so every statement below is a conjunction hiding inside a
-- `∨ ≡ false`, and these are how one is opened and closed.
----------------------------------------------------------------------

∨-split : ∀ (a b : Bool) → a ∨ b ≡ false → a ≡ false × b ≡ false
∨-split false b p = refl , p
∨-split true  b ()

∨-join : ∀ {a b : Bool} → a ≡ false → b ≡ false → a ∨ b ≡ false
∨-join refl hb = hb

any-dry-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  any dryEvent xs ≡ false → any dryEvent ys ≡ false →
  any dryEvent (xs ++ ys) ≡ false
any-dry-++ []       ys hx hy = hy
any-dry-++ (x ∷ xs) ys hx hy with ∨-split (dryEvent x) (any dryEvent xs) hx
... | hd , ht = ∨-join hd (any-dry-++ xs ys ht hy)

-- a close reads the same at every payload type: the marker is the
-- REASON, and retagging carries it through unchanged
close-dry-cross : ∀ {A B : Set} (s : Source) (r : CloseReason) →
  dryEvent (close {A} s r) ≡ false → dryEvent (close {B} s r) ≡ false
close-dry-cross s cut        h = refl
close-dry-cross s cutPending h = refl
close-dry-cross s exhausted  h = refl
close-dry-cross s dried      ()

----------------------------------------------------------------------
-- The three parts of a re-emitted event list that are not the frame's.
-- The split keeps every bookkeeping event with its reason intact, so
-- it neither creates nor destroys a dry close; the payload run and the
-- appended completion carry no close at all.
----------------------------------------------------------------------

splitEvents-dry : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (evs : List (InstEvent (Val Γ u))) → any dryEvent evs ≡ false →
  any dryEvent (proj₁ (proj₂ (splitEvents {A = A} evs))) ≡ false
splitEvents-dry []               h = refl
splitEvents-dry (value v ∷ es)   h = splitEvents-dry es (proj₂ (∨-split _ _ h))
splitEvents-dry (complete ∷ es)  h = splitEvents-dry es (proj₂ (∨-split _ _ h))
splitEvents-dry (init s ∷ es)    h = splitEvents-dry es (proj₂ (∨-split _ _ h))
splitEvents-dry (handoff s ∷ es) h = splitEvents-dry es (proj₂ (∨-split _ _ h))
splitEvents-dry (close s r ∷ es) h with ∨-split (dryEvent (close s r)) _ h
... | hd , ht = ∨-join (close-dry-cross s r hd) (splitEvents-dry es ht)

retag-dry : ∀ {A B : Set} (evs : List (InstEvent A)) →
  any dryEvent evs ≡ false → any dryEvent (retagEvents {A} {B} evs) ≡ false
retag-dry []               h = refl
retag-dry (value v ∷ es)   h = retag-dry es (proj₂ (∨-split _ _ h))
retag-dry (init s ∷ es)    h = retag-dry es (proj₂ (∨-split _ _ h))
retag-dry (handoff s ∷ es) h = retag-dry es (proj₂ (∨-split _ _ h))
retag-dry (complete ∷ es)  h = retag-dry es (proj₂ (∨-split _ _ h))
retag-dry (close s r ∷ es) h with ∨-split (dryEvent (close s r)) _ h
... | hd , ht = ∨-join (close-dry-cross s r hd) (retag-dry es ht)

-- the payload run plus whatever completion the split saw: no close at
-- all, so nothing to read
tailPart-dry : ∀ {A : Set} (vs : List A) (fin : Bool) →
  any dryEvent (map value vs ++ (if fin then complete ∷ [] else [])) ≡ false
tailPart-dry []       true  = refl
tailPart-dry []       false = refl
tailPart-dry (v ∷ vs) fin   = tailPart-dry vs fin

-- one re-emitted event list, assembled from its four parts
emitEvents-dry : ∀ {A : Set} (bs es : List (InstEvent A)) (vs : List A)
  (fin : Bool) → any dryEvent bs ≡ false → any dryEvent es ≡ false →
  any dryEvent (bs ++ es ++ map value vs ++ (if fin then complete ∷ [] else []))
    ≡ false
emitEvents-dry bs es vs fin hb he =
  any-dry-++ bs _ hb (any-dry-++ es _ he (tailPart-dry vs fin))

----------------------------------------------------------------------
-- A QUIET FRAME: one whose own step can build no dry close.  This is
-- the hypothesis `pushBurst-dry` runs on, and the whole reason the
-- walk's four non-flattening operators need no arithmetic.
----------------------------------------------------------------------

FrameDry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} →
  Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t → Set
FrameDry {Γ = Γ} {e = e} {s = s} ac id now f κ =
  ∀ (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ) (st : EvalSt e) →
    any dryEvent (proj₁ (proj₂ (stepFrame ac id now f κ vals fin sd st))) ≡ false

-- a cut severs registrations and announces each with `cut` or
-- `cutPending`; neither is the evaluator's own marker, and no other
-- reason is reachable from here
cutThrough-dry : ∀ {n} {Γ : Ctx n} {t} (nid : NodeId) (dl : List RegId)
  (wm : RegId) (dy : List Source) (r : List (RegId × Source × Chain Γ t)) →
  any dryEvent (proj₁ (proj₂ (cutThrough nid dl wm dy r))) ≡ false
cutThrough-dry nid dl wm dy [] = refl
cutThrough-dry nid dl wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c)
     | cutThrough nid dl wm dy r | cutThrough-dry nid dl wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) dl ∧ memberSource src dy
...     | true  = ih
...     | false with any (_≡ᵇ rid) dl ∨ (wm ≤ᵇ rid)
...       | true  = ih
...       | false = ih

takeDispatch-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sd : Sched Γ)
  (st : EvalSt e) (m : Maybe (NodeState Γ)) →
  any dryEvent (proj₁ (proj₂ (takeDispatch {t = t} nid vals fin sd st m)))
    ≡ false
takeDispatch-dry nid vals fin sd st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = cutThrough-dry nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                (EvalSt.dying st) (EvalSt.registry st)
... | false = refl
takeDispatch-dry nid vals fin sd st nothing                      = refl
takeDispatch-dry nid vals fin sd st (just (scan-st v))           = refl
takeDispatch-dry nid vals fin sd st (just (mergeAll-st l a q o)) = refl
takeDispatch-dry nid vals fin sd st (just (switch-st m o))       = refl
takeDispatch-dry nid vals fin sd st (just (exhaust-st a o))      = refl

----------------------------------------------------------------------
-- THE THREE QUIET FRAMES.  A map is a pure transform, a scan reads and
-- rewrites one accumulator, and a take's only events are the closes it
-- severs — so none of the three reaches a `subscribeE` at all, and the
-- walk's four non-flattening operators are exactly the four that build
-- one of them.
----------------------------------------------------------------------

map-frame-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (κ : Path Γ u t) → FrameDry {e = e} ac id now (map-f fn) κ
map-frame-dry ac id now fn κ vals fin sd st = refl

scan-frame-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (κ : Path Γ u t) → FrameDry {e = e} ac id now (scan-f fn nid) κ
scan-frame-dry {u = u} ac id now fn nid κ vals fin sd st
  with lookupNode nid (EvalSt.nodes st)
... | nothing                      = refl
... | just (take-st k)             = refl
... | just (mergeAll-st l a q o)   = refl
... | just (switch-st m o)         = refl
... | just (exhaust-st a o)        = refl
... | just (scan-st {w} v) with w ≟ᵗ u
...   | yes refl = refl
...   | no  _    = refl

take-frame-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (nid : NodeId)
  (κ : Path Γ s t) → FrameDry {e = e} ac id now (take-f {s = s} nid) κ
take-frame-dry ac id now nid κ vals fin sd st =
  takeDispatch-dry nid vals fin sd st (lookupNode nid (EvalSt.nodes st))

----------------------------------------------------------------------
-- THE WALK.  Induction on the burst's spine: every emit contributes
-- its own bookkeeping, the frame's events and a payload run, and the
-- first of those is the only one the child could have made dry.
----------------------------------------------------------------------

pushBurst-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (burst : Stream Γ s) (sd : Sched Γ) (st : EvalSt e) →
  FrameDry {e = e} ac id now f κ → hasDry burst ≡ false →
  hasDry (proj₁ (pushBurst ac id now f κ burst sd st)) ≡ false
pushBurst-dry ac id now f κ []         sd st fd hb = refl
pushBurst-dry {Γ = Γ} {t = t} {e = e} {s = s} {u = u} ac id now f κ (em ∷ ems) sd st fd hb
  with ∨-split (any dryEvent (InstEmit.events em)) (hasDry ems) hb
... | he , hr =
  ∨-join
    (emitEvents-dry (proj₁ (proj₂ sp)) (retagEvents (proj₁ (proj₂ sf)))
      (proj₁ sf) (proj₁ (proj₂ (proj₂ sf)))
      (splitEvents-dry (InstEmit.events em) he)
      (retag-dry (proj₁ (proj₂ sf)) (fd (proj₁ sp) (proj₂ (proj₂ sp)) sd st)))
    (pushBurst-dry ac id now f κ ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf)))) fd hr)
  where
  sp : List (Val Γ s) × List (InstEvent (Val Γ u)) × Bool
  sp = splitEvents (InstEmit.events em)

  sf : List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  sf = stepFrame ac id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sd st
