------------------------------------------------------------------
-- DRYNESS IS A PROPERTY OF EVENTS, and this module says so at the
-- shapes the subscription machine actually builds.
--
-- `hasDry` is a disjunctive fold over emits and then over their
-- events, so every fact here is one induction and none of them knows
-- anything about the descent.  They are separated from the descent
-- proof for that reason: a clause that assembles a burst out of
-- `init`, `value` and `close … exhausted` is dry-free for a reason
-- that has nothing to do with which triple it was standing at, and
-- mixing the two would put arithmetic beside a list induction.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Dry-Emits where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Prim using (Id; Source; InstEvent; init; value; close; complete;
  exhausted; InstEmit; _at_from_as_; EmitKind; subscribe)
open import Rx.Exp using (Ctx; Val)
open import Rx.Evaluator using (Stream; Sched; hasDry; dryEvent; sharedPlumb; oneShotBurst)

-- dryness of a concatenation is dryness of either half
hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry xs ≡ false → hasDry ys ≡ false → hasDry (xs ++ ys) ≡ false
hasDry-++ []         ys hx hy = hy
hasDry-++ (em ∷ ems) ys hx hy with any dryEvent (InstEmit.events em)
... | true  = hx
... | false = hasDry-++ ems ys hx hy

-- a branch neither of whose arms is dry.  It is stated over the
-- machine's RETURN TRIPLE rather than over a bare burst because that is
-- the shape the clauses branch at — `proj₁` does not commute with `if`,
-- so a lemma about the burst alone would not apply to one
hasDry-if : ∀ {n} {Γ : Ctx n} {u} {B C : Set} (b : Bool)
  (x y : Stream Γ u × B × C) →
  hasDry (proj₁ x) ≡ false → hasDry (proj₁ y) ≡ false →
  hasDry (proj₁ (if b then x else y)) ≡ false
hasDry-if true  x y hx hy = hx
hasDry-if false x y hx hy = hy

-- a one-emit burst is dry exactly when its event list is
hasDry-single : ∀ {A : Set} (evs : List (InstEvent A)) (id : Id) (src : Source)
  (k : EmitKind) → any dryEvent evs ≡ false →
  hasDry ((evs at id from src as k) ∷ []) ≡ false
hasDry-single evs id src k h rewrite h = refl

-- a payload run carries no close at all, so it cannot carry the dry one
values-dry : ∀ {A : Set} (vs : List A) (rest : List (InstEvent A)) →
  any dryEvent rest ≡ false → any dryEvent (map value vs ++ rest) ≡ false
values-dry []       rest h = h
values-dry (v ∷ vs) rest h = values-dry vs rest h

values-only-dry : ∀ {A : Set} (vs : List A) → any dryEvent (map value vs) ≡ false
values-only-dry []       = refl
values-only-dry (v ∷ vs) = values-only-dry vs

-- a cold with an async tail announces its sync prefix and keeps the
-- source open for the schedule, so its burst ends on a value rather
-- than on any close at all
cold-tail-dry : ∀ {A : Set} (vs : List A) (id : Id) (src : Source) →
  hasDry (((init src ∷ map value vs) at id from src as subscribe) ∷ []) ≡ false
cold-tail-dry vs id src =
  hasDry-single (init src ∷ map value vs) id src subscribe (values-only-dry vs)

-- the source that lives and dies inside its own subscription burst
oneShot-dry : ∀ {A : Set} (vals : List A) (id : Id) (src : Source) →
  hasDry (((init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
            at id from src as subscribe) ∷ []) ≡ false
oneShot-dry vals id src =
  hasDry-single (init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
    id src subscribe (values-dry vals (close src exhausted ∷ complete ∷ []) refl)

oneShotBurst-dry : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (id : Id)
  (sched : Sched Γ) → hasDry (proj₁ (oneShotBurst vals id sched)) ≡ false
oneShotBurst-dry vals id sched = oneShot-dry vals id _

-- re-kinding an emit leaves its events alone, so plumbing a share's
-- connect burst upward cannot introduce dryness the burst did not have
hasDry-sharedPlumb : ∀ {n} {Γ : Ctx n} {u} (b : Stream Γ u) →
  hasDry (sharedPlumb b) ≡ hasDry b
hasDry-sharedPlumb []         = refl
hasDry-sharedPlumb (em ∷ ems) =
  cong (any dryEvent (InstEmit.events em) ∨_) (hasDry-sharedPlumb ems)

-- what a connect returns: one announcing emit the machine writes
-- itself, then the def's own burst re-kinded as plumbing
connect-emit-dry : ∀ {n} {Γ : Ctx n} {u} (evs : List (InstEvent (Val Γ u)))
  (id : Id) (src : Source) (b : Stream Γ u) →
  any dryEvent evs ≡ false → hasDry b ≡ false →
  hasDry ((evs at id from src as subscribe) ∷ sharedPlumb b) ≡ false
connect-emit-dry evs id src b he hb rewrite he | hasDry-sharedPlumb b = hb
