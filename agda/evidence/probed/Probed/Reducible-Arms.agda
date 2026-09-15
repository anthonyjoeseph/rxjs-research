-- THE THREE LEAVES OF THE REDUCIBILITY BODY, INSTANTIATED.
--
-- WHAT IS AT RISK, AND IT IS THE SAME RISK IN ALL THREE.  The
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
-- whose def is an arbitrary term.  A flattener's node holding
-- something already -- a queue with an entry in it, a switch whose
-- current inner is actually running, an exhaust already active -- so
-- the kill below walks an empty registry and the refusal reached is
-- the concurrency one rather than the exhaust's.  Two of the slot's
-- five scripted sub-arms -- the spent hot and the cold with an
-- asynchronous tail -- and the take and scan arms of the body, whose
-- own recursion the body already checks.
--
-- TARGET: red-tm @e1ae28
-- TARGET: red-input-shared @21f529
-- TARGET: red-push @733369
module Probed.Reducible-Arms where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (nothing; just)
import Data.Nat
open import Data.Nat using (zero; s≤s; z≤n)
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (InstEmit; InstEvent; init; value; close; handoff; complete; subscribe; _at_from_as_)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; nat̂; strmᵗ; varᵗ; Tm; input)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Stream; Path; root; map-f; sched-init;
  st-init; thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp; NodeState; from-inner; _↠_;
  mergeAll-st; switch-st; exhaust-st; installNode; oneShotBurst)
open import Rx.Evaluator.Reducible using (Red; EvSat; StreamSat; reducible; red-tm;
  red-input-shared; red-push; satOneShot)

open import Rx.Evaluator.Domain using (subs-shared; slot-spent; slot-join; push-cons; push-nil; step-map;
  step-thru-outer; walk-nil; walk-cons; inner; consume-all-sub; consume-all-enqueue;
  consume-switch-sub; consume-exhaust-sub)

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
-- 5.  THE SAME PUSH THROUGH A FLATTENING FRAME, which is where the
-- hop now lives.  The three `*All` operators are not statements of
-- their own: each runs its source through a `thru-outer` frame and
-- pushes what came back, so everything an operator DOES -- the queue,
-- the kill, the refusal, the concurrency limit -- is a clause of this
-- push rather than of anything above it.  The row reaches the frame's
-- own step and the walk that finds nothing to consume.
--
-- LOAD-BEARING for the frame clause and DEGENERATE for the operator:
-- the outer's burst is protocol traffic with no value on it, so the
-- walk has no observable to hand the operator and no reading of the
-- store is made.  A live inner is not reached here.
----------------------------------------------------------------------

nid₃ : _
nid₃ = Sched.nextNode sch₀

sched₃ : Sched Γ₀
sched₃ = record sch₀ { nextNode = Data.Nat.suc nid₃ }

st₃ : EvalSt e₀
st₃ = installNode nid₃ (mergeAll-st {t = natᵗ} nothing 0 [] false) st₀

burstOuter : Stream Γ₀ (obs natᵗ)
burstOuter = proj₁ (oneShotBurst [] 0 sched₃)

satOuter : StreamSat (Red {Γ = Γ₀} (obs natᵗ)) burstOuter
satOuter = satOneShot 0 sched₃ []

row-push-thru : Confirms
  (red-push {e = e₀} 0 0 (thru-outer mergeAllᵒ nid₃) κ₀ satOuter sched₃ st₃)
row-push-thru =
  _ , push-cons refl (step-thru-outer walk-nil) push-nil
    , (tt ∷ tt ∷ tt ∷ []) ∷ []

----------------------------------------------------------------------
-- 6.  THE SAME PUSH AT A LIVE INNER, which is the operator-specific
-- half.  The outer's burst now carries an actual observable, so the
-- walk hands it to the operator and the operator reads its own node:
-- mergeAll subscribes it or queues it depending on the concurrency
-- limit, switch kills whatever was current and subscribes, exhaust
-- subscribes because nothing is active.  The inner's own subscription
-- is the candidate at the value, which is what the push's hypothesis
-- hands over -- so these rows are also where the candidate is spent
-- rather than merely carried.
--
-- LOAD-BEARING at each operator's reading of the store, and at the
-- bounded limit for mergeAll, where `hasRoom` answers false and the
-- value is enqueued instead.  DEGENERATE on the satisfaction half:
-- the frame's output type is the inner's element type, which is data
-- here, so what comes back out is checked by computation.
----------------------------------------------------------------------

-- The frame's output is the inner's element type, which is data here,
-- so every event of what comes back out satisfies the candidate by
-- computation.  Spelling that out once keeps the rows below to their
-- derivations.
evsTriv : ∀ {A : Set} {P : A → Set} → (∀ x → P x)
        → (es : List (InstEvent A)) → All (EvSat P) es
evsTriv p []                = []
evsTriv p (init _    ∷ es)  = tt ∷ evsTriv p es
evsTriv p (value v   ∷ es)  = p v ∷ evsTriv p es
evsTriv p (close _ _ ∷ es)  = tt ∷ evsTriv p es
evsTriv p (handoff _ ∷ es)  = tt ∷ evsTriv p es
evsTriv p (complete  ∷ es)  = tt ∷ evsTriv p es

satTriv : ∀ {A : Set} {P : A → Set} → (∀ x → P x)
        → (s : List (InstEmit A)) → StreamSat P s
satTriv p []       = []
satTriv p (em ∷ s) = evsTriv p (InstEmit.events em) ∷ satTriv p s

oInner : Closed Γ₀ natᵗ
oInner = ofᵉ (nat̂ 7 ∷ [])

burstLive : Stream Γ₀ (obs natᵗ)
burstLive = ((init 0 ∷ value oInner ∷ []) at 0 from 0 as subscribe) ∷ []

satLive : StreamSat (Red {Γ = Γ₀} (obs natᵗ)) burstLive
satLive = (tt ∷ reducible oInner ∷ []) ∷ []

instL : _
instL = Sched.nextNode sched₃

subLive : ∀ (op : AllOp) (ns : NodeState Γ₀) → _
subLive op ns =
  proj₁ (proj₂ (reducible oInner (from-inner op nid₃ instL ↠ κ₀) 0 0
                  (record sched₃ { nextNode = Data.Nat.suc instL })
                  (installNode nid₃ ns st₀)))

row-live-merge : Confirms
  (red-push {e = e₀} 0 0 (thru-outer mergeAllᵒ nid₃) κ₀ satLive sched₃ st₃)
row-live-merge =
  _ , push-cons refl
        (step-thru-outer
          (walk-cons (consume-all-sub refl refl
                       (inner refl (subLive mergeAllᵒ (mergeAll-st nothing 0 [] false)) refl))
                     walk-nil))
        push-nil
    , satTriv (λ _ → tt) _

stBound : EvalSt e₀
stBound = installNode nid₃ (mergeAll-st {t = natᵗ} (just 0) 0 [] false) st₀

row-live-queue : Confirms
  (red-push {e = e₀} 0 0 (thru-outer mergeAllᵒ nid₃) κ₀ satLive sched₃ stBound)
row-live-queue =
  _ , push-cons refl (step-thru-outer (walk-cons (consume-all-enqueue refl refl) walk-nil)) push-nil
    , satTriv (λ _ → tt) _

stSwitch : EvalSt e₀
stSwitch = installNode nid₃ (switch-st nothing false) st₀

row-live-switch : Confirms
  (red-push {e = e₀} 0 0 (thru-outer switchᵒ nid₃) κ₀ satLive sched₃ stSwitch)
row-live-switch =
  _ , push-cons refl
        (step-thru-outer
          (walk-cons (consume-switch-sub refl refl
                       (inner refl (subLive switchᵒ (switch-st nothing false)) refl))
                     walk-nil))
        push-nil
    , satTriv (λ _ → tt) _

stExhaust : EvalSt e₀
stExhaust = installNode nid₃ (exhaust-st false false) st₀

row-live-exhaust : Confirms
  (red-push {e = e₀} 0 0 (thru-outer exhaustᵒ nid₃) κ₀ satLive sched₃ stExhaust)
row-live-exhaust =
  _ , push-cons refl
        (step-thru-outer
          (walk-cons (consume-exhaust-sub refl
                       (inner refl (subLive exhaustᵒ (exhaust-st false false)) refl))
                     walk-nil))
        push-nil
    , satTriv (λ _ → tt) _
