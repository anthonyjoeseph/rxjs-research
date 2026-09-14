-- THE HOP LEAF IS FALSE WITHOUT A PREMISE ABOUT WHAT IT IS HANDED, AND
-- THE RELATION IS WHAT SAYS SO RATHER THAN ANY ARITHMETIC.
--
-- `thruConsume` is the one clause that takes a value which IS an inner
-- observable and subscribes it, so it is where the machine asks whether
-- that inner is written shallower than the rank it is standing at.  On
-- the negative answer it does not recurse: it mints the instance and
-- hands back a burst carrying the dry marker.
--
-- THE CONSTRUCTOR SET HAS NO ARM FOR THAT ANSWER, WHICH IS THE WHOLE
-- WITNESS.  `subscribeInner⇓` is a single constructor and it DEMANDS a
-- derivation for the inner subscribe, so the only result it relates is
-- the one a real descent produced.  A totality claim quantified freely
-- over the entry therefore asserts a derivation at a triple where the
-- machine refused to descend — and the refusal is visible in the
-- statement's own output, not merely in a figure computed beside it.
--
-- SO THE STARVED ENTRY IS THE POINT AND NOT THE PROGRAM.  Nothing here
-- is nested, wrapped or gated: the inner is `EMPTY`, which the measure
-- reads at nought, and the caller enters at a rank of nought.  A guard
-- comparing the two strictly refuses, so no program can be shallow
-- enough to escape this — which is what makes the repair a premise
-- relating the two ends rather than a cleverer measure.
module Refuted.Hop-Unconditioned where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; close; dried)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; emptyᵉ)
open import Rx.Slots using (Slots)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (AllOp; NodeId; Path; root; Sched; EvalSt;
  mergeAllᵒ; mergeAll-st; installNode; sched-init; st-init; thruConsume;
  drySource)
open import Rx.Evaluator.Domain using (thruConsume⇓; consume-all-sub;
  consume-all-enqueue; consume-all-nil; inner; subs-empty)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED.  `src` declares
-- a postulate of exactly this type, and a refutation that APPLIED it
-- would be evidence about whatever that name says today.  Written out,
-- a repair that conditions the entry makes the row below fail to
-- typecheck rather than quietly agreeing with it.
----------------------------------------------------------------------

ConsumeTotal : Set
ConsumeTotal =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId)
    (κ : Path Γ lo u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (thruConsume {e = e} ac op nid κ id now o sched st)

----------------------------------------------------------------------
-- THE ENTRY, AND EVERY PART OF IT IS THE MACHINE'S OWN.  The store is
-- built by the evaluator's installer rather than by a record update, so
-- the node the walk finds is one a run could have installed; the
-- schedule is the root seeding.  What is chosen adversarially is the
-- one thing the statement lets a caller choose — the triple.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ ins₀

-- an unbounded merge with nothing active, so the walk takes the arm
-- that subscribes rather than the one that parks
st₀ : EvalSt e₀
st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (st-init e₀)

o₀ : Val Γ₀ (obs natᵗ)
o₀ = emptyᵉ

-- NAMED so the floor is pinned rather than inferred: a bare `root`
-- leaves its index open, and the machine's own clauses are then blocked
-- on a meta instead of reducing to the burst this witness is about.
κ₀ : Path Γ₀ 0 natᵗ natᵗ
κ₀ = root

ac₀ : Acc _≺_ (0 , 0 , 0)
ac₀ = ≺-wellFounded (0 , 0 , 0)

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl` RATHER THAN COMPUTED INSIDE THE ⊥.
-- Two figures, and the finding is that they cannot meet: the inner is
-- read at nought and the rank it is compared against is nought, so a
-- STRICT guard refuses at the shallowest inner there is.
----------------------------------------------------------------------

inner-depth : obsDepthᵉ o₀ ≡ 0
inner-depth = refl

-- LOAD-BEARING, and it is the whole witness: the machine's own second
-- component carries the marker.  A repair that made the guard pass here
-- leaves this row failing rather than silently true.
dry-out : proj₁ (proj₂ (thruConsume {e = e₀} ac₀ mergeAllᵒ 0 κ₀ 0 0 o₀ sched₀ st₀))
            ≡ close {Val Γ₀ natᵗ} drySource dried ∷ []
dry-out = refl

----------------------------------------------------------------------
-- THE REFUTATION, TAKEN OVER AN OPEN RESULT AND CLOSED BY THE PINNED
-- EQUATION.  Reading the machine's result straight into the index
-- leaves unification stuck against the store update the subscribing arm
-- writes, which decides nothing either way; quantifying the result and
-- spending `dry-out` puts the crossing where the constructors are, so
-- each arm is refuted by the events IT builds.
--
-- Three arms can stand at this operator and none of them builds the
-- marker: the two that answer without descending emit nothing at all,
-- and the one that descends carries an inner derivation whose burst is
-- `EMPTY`'s own one-shot.
----------------------------------------------------------------------

no-dry : ∀ {res} → thruConsume⇓ {e = e₀} mergeAllᵒ 0 κ₀ 0 0 o₀ sched₀ st₀ res
       → proj₁ (proj₂ res) ≡ close drySource dried ∷ [] → ⊥
no-dry (consume-all-sub _ _ (inner refl (subs-empty refl) refl)) ()
no-dry (consume-all-enqueue _ _) ()
no-dry consume-all-nil ()

consume-total-false : ConsumeTotal → ⊥
consume-total-false h =
  no-dry (h {e = e₀} ac₀ mergeAllᵒ 0 κ₀ 0 0 o₀ sched₀ st₀) dry-out
