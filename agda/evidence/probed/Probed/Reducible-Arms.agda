-- THE SEVEN LEAVES OF THE REDUCIBILITY BODY, INSTANTIATED.
--
-- WHAT IS AT RISK, AND IT IS THE SAME RISK IN ALL SEVEN.  The
-- candidate's observable arm demands a subscription derivation in
-- EVERY schedule and EVERY state, together with a satisfaction claim
-- over everything the derivation emits.  Nothing had ever produced one
-- of those pairs.  A statement nobody has inhabited at a single point
-- is not a hard statement, it is an unknown one, and the way it would
-- be false is that the two halves cannot be had together -- a
-- derivation reachable only at a state the satisfaction claim cannot
-- be taken at, or a burst whose values no induction hypothesis
-- reaches.
--
-- WHAT THE ROWS BUY, STATED IN CONJUNCTS RATHER THAN IN PROGRAMS.
-- Every row below inhabits BOTH halves at its point, which is the
-- conjunct that was unknown.  The satisfaction half is reached at a
-- PAYLOAD by exactly one row -- a frame whose function returns an
-- observable, where what the pushed value must satisfy is another
-- expression's own reducibility.  Every other row's burst is protocol
-- traffic or data, where the candidate is the trivial predicate and
-- satisfaction holds by computation; those rows are evidence about the
-- DERIVATION half and about the state threading, and they are labelled
-- so nobody reads them as coverage of the other.
--
-- AND THE SLOT ARM CANNOT BE REACHED ON THE SATISFACTION HALF AT ALL,
-- WHICH IS A PROPERTY OF THE STATEMENT RATHER THAN A GAP HERE.  A
-- scripted slot carries its own side condition that the element type
-- is DATA, so the candidate at a slot's values is the trivial
-- predicate by construction and no program can make that conjunct
-- assert anything.  A slot whose values could fail it would have to be
-- a SHARE, whose def is an expression -- which is the sub-arm below
-- that nothing here reaches.
--
-- NOT REACHED, and each is a region rather than a program.  A share's
-- connect, which is the slot leaf's sixth sub-arm and the only one
-- whose def is an arbitrary term.  A mu whose body actually refers to
-- itself: the rows here peel a body with no self-reference, so they
-- exercise the peel and say nothing about the fixpoint.  A flattener
-- with a LIVE inner -- these reach the empty outer, where the queue
-- never fills, the switch never kills and the exhaust never refuses.
-- The bounded-concurrency axis is untouched at every limit.  Two of
-- the slot's five scripted sub-arms -- the spent hot and the cold with
-- an asynchronous tail -- and the take and scan arms of the body,
-- whose own recursion the body already checks.
--
-- TARGET: red-tm @e1ae28
-- TARGET: red-input-shared @21f529
-- TARGET: red-push @733369
-- TARGET: red-μ @2f6b5c
-- TARGET: red-merge-all @76b1cd
-- TARGET: red-switch-all @e42657
-- TARGET: red-exhaust-all @98824b
module Probed.Reducible-Arms where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (init; value; subscribe; _at_from_as_)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; Exp; ofᵉ; emptyᵉ; unfoldμ; nat̂; strmᵗ; varᵗ; Tm; input)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Stream; Path; root; map-f; sched-init;
  st-init)
open import Rx.Evaluator.Reducible using (Red; StreamSat; reducible; red-tm;
  red-input-shared; red-push; red-μ; red-merge-all; red-switch-all; red-exhaust-all)

open import Rx.Evaluator.Domain using (subs-μ; subs-shared; slot-spent; slot-join;
  subs-empty; push-cons; push-nil; step-map; step-thru-outer; walk-nil;
  sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE HARNESS: a closed program in an empty slot table, at the state
-- a run actually starts in.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []

ins₀ : Slots Γ₀
ins₀ ()

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ (nat̂ 7 ∷ [])

sch₀ : Sched Γ₀
sch₀ = sched-init e₀ ins₀

st₀ : EvalSt e₀
st₀ = st-init e₀

-- the root of the chain, at the floor a run starts at
κ₀ : Path Γ₀ 0 natᵗ natᵗ
κ₀ = root

----------------------------------------------------------------------
-- 1.  THE TERM ARM.  LOAD-BEARING at an observable payload, where the
-- claim IS an expression's reducibility; the numeral row is DEGENERATE
-- and is here only to say the data half asserts nothing.
----------------------------------------------------------------------

inner₀ : Tm Γ₀ [] [] [] (obs natᵗ)
inner₀ = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

row-tm-obs : Confirms (red-tm {Γ = Γ₀} inner₀ {e = e₀} κ₀ 0 0 sch₀ st₀)
row-tm-obs = reducible (ofᵉ (nat̂ 7 ∷ [])) {e = e₀} κ₀ 0 0 sch₀ st₀

row-tm-nat : Confirms (red-tm {Γ = Γ₀} (nat̂ 7))
row-tm-nat = tt

----------------------------------------------------------------------
-- 2.  THE μ PEEL.  The body here does not refer to itself, so the row
-- exercises the PEEL -- the unfolding subscribed in the caller's own
-- state -- and says nothing about the fixpoint.  Load-bearing for the
-- conjunct that the peeled term's derivation IS the μ's: if the
-- unfolding landed in a different state, this would not typecheck.
----------------------------------------------------------------------

body₀ : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
body₀ = ofᵉ (nat̂ 7 ∷ [])

row-μ-peel : Confirms (red-μ {Γ = Γ₀} body₀ {e = e₀} κ₀ 0 0 sch₀ st₀)
row-μ-peel =
  let (r , d , sat) = reducible (unfoldμ body₀) {e = e₀} κ₀ 0 0 sch₀ st₀
  in r , subs-μ d , sat

----------------------------------------------------------------------
-- 3.  THE SLOT'S SHARE, at the two sub-arms that carry no payload.  A
-- share whose source has completed answers spent; one whose definition
-- is already connected joins the existing fan-out.  Neither runs the
-- definition, so neither reaches the connect -- which is the whole of
-- what is left in this statement, and is why the rows are evidence
-- about the SHAPE rather than about the hard sub-arm.
--
-- BOTH STATES ARE CONSTRUCTED RATHER THAN REACHED, and that is the
-- coverage boundary: the flags these arms dispatch on are written into
-- the state directly, so the rows say the arms compose at a state of
-- that description and not that a run produces one.  They are stated
-- anyway because the predicate HOLDS at them -- a constructed state
-- where it FAILED would be a refutation candidate instead.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ []

e₁ : Closed Γ₁ natᵗ
e₁ = input zero

d₁ : Closed Γ₁ natᵗ
d₁ = ofᵉ (nat̂ 5 ∷ [])

insShared : Slots Γ₁
insShared zero = shared d₁ {ok = tt}

schShared : Sched Γ₁
schShared = sched-init e₁ insShared

-- the share's own source has completed, so the subscription is handed
-- the spent protocol burst and the state is threaded on untouched
stSpent : EvalSt e₁
stSpent = record (st-init e₁) { completedSources = 0 ∷ [] }

row-share-spent : Confirms
  (red-input-shared {Γ = Γ₁} zero d₁ {tt} (root {lo = 1}) (s≤s z≤n) 0 0
     schShared refl stSpent)
row-share-spent =
  _ , subs-shared {d = d₁} {below = s≤s z≤n} {ok = tt} refl (slot-spent refl) , (tt ∷ tt ∷ tt ∷ []) ∷ []

-- the definition is live and already connected, so this subscription
-- only registers: the burst is one `init` and the state gains a row
stJoin : EvalSt e₁
stJoin = record (st-init e₁) { connectedShares = 0 ∷ [] }

row-share-join : Confirms
  (red-input-shared {Γ = Γ₁} zero d₁ {tt} (root {lo = 1}) (s≤s z≤n) 0 0
     schShared refl stJoin)
row-share-join =
  _ , subs-shared {d = d₁} {below = s≤s z≤n} {ok = tt} refl (slot-join refl refl) , (tt ∷ []) ∷ []

----------------------------------------------------------------------
-- 4.  THE FRAME PUSH, and the one place in this file where the
-- satisfaction half is a real claim.  The frame's function returns an
-- OBSERVABLE, so what the pushed burst must satisfy is another
-- expression's own reducibility rather than a protocol event -- the
-- conjunct every other row here leaves at ⊤.
----------------------------------------------------------------------

fnObs : Tm Γ₀ [] [] (natᵗ ∷ []) (obs natᵗ)
fnObs = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

burstVal : Stream Γ₀ natᵗ
burstVal = ((init 0 ∷ value 7 ∷ []) at 0 from 0 as subscribe) ∷ []

satVal : StreamSat (Red {Γ = Γ₀} natᵗ) burstVal
satVal = (tt ∷ tt ∷ []) ∷ []

-- the push's root sits at the frame's OUTPUT type, so this row needs a
-- program whose own type is the observable the frame produces
e₂ : Closed Γ₀ (obs natᵗ)
e₂ = ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])

sch₂ : Sched Γ₀
sch₂ = sched-init e₂ ins₀

st₂ : EvalSt e₂
st₂ = st-init e₂

κ₂ : Path Γ₀ 0 (obs natᵗ) (obs natᵗ)
κ₂ = root

row-push-obs : Confirms
  (red-push {e = e₂} 0 0 (map-f fnObs) κ₂ satVal sch₂ st₂)
row-push-obs =
  _ , push-cons refl step-map push-nil
    , (tt ∷ reducible (ofᵉ (nat̂ 7 ∷ [])) ∷ []) ∷ []

----------------------------------------------------------------------
-- 5.  THE THREE FLATTENERS, at an outer that emits no inner at all.
-- This is the arm each one takes when its walk has nothing to consume,
-- so the queue never fills, the switch never kills and the exhaust
-- never refuses: evidence that the node install, the outer's own
-- subscription and the push back through the frame compose, and
-- evidence about nothing downstream of the hop.
----------------------------------------------------------------------

outer₀ : Closed Γ₀ (obs natᵗ)
outer₀ = emptyᵉ

redOuter : Red {Γ = Γ₀} (obs (obs natᵗ)) outer₀
redOuter = reducible outer₀

row-merge-empty : Confirms
  (red-merge-all {Γ = Γ₀} nothing outer₀ redOuter {e = e₀} κ₀ 0 0 sch₀ st₀)
row-merge-empty =
  _ , subs-merge-all (sub-all refl (subs-empty refl)
        (push-cons refl (step-thru-outer walk-nil) push-nil))
    , (tt ∷ tt ∷ tt ∷ []) ∷ []

row-switch-empty : Confirms
  (red-switch-all {Γ = Γ₀} outer₀ redOuter {e = e₀} κ₀ 0 0 sch₀ st₀)
row-switch-empty =
  _ , subs-switch-all (sub-all refl (subs-empty refl)
        (push-cons refl (step-thru-outer walk-nil) push-nil))
    , (tt ∷ tt ∷ tt ∷ []) ∷ []

row-exhaust-empty : Confirms
  (red-exhaust-all {Γ = Γ₀} outer₀ redOuter {e = e₀} κ₀ 0 0 sch₀ st₀)
row-exhaust-empty =
  _ , subs-exhaust-all (sub-all refl (subs-empty refl)
        (push-cons refl (step-thru-outer walk-nil) push-nil))
    , (tt ∷ tt ∷ tt ∷ []) ∷ []
