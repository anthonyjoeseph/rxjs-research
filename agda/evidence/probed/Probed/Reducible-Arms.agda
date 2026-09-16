-- THE REMAINING LEAVES OF THE REDUCIBILITY BODY, INSTANTIATED.
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
-- TARGET: red-input-shared @21f529
-- TARGET: red-scan @c288cd
-- TARGET: red-from-inner @de6e75
-- TARGET: red-thru @f94cad
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

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; nat̂; varᵗ; input; _×ᵗ_; fstᵗ; Fn)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init; mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp;
  NodeState; from-inner; _↠_; map-f; mergeAll-st; switch-st; exhaust-st; installNode; scan-st)
open import Rx.Evaluator.Reducible using (Red; reducible; red-input-shared; red-thru; red-scan; red-from-inner)

open import Rx.Evaluator.Domain using (subs-shared; slot-spent; slot-join; step-thru-outer; walk-nil; walk-cons; inner; step-scan;
  step-from-inner; react-false; consume-all-sub; consume-all-enqueue; consume-switch-sub;
  consume-exhaust-sub)

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
-- 4.  THE TWO STORE-READING FRAMES THAT ARE NOT FLATTENERS.  Both are
-- stated at an OBSERVABLE payload, which is the only shape in which
-- either can fail: at a data payload the satisfaction half is `⊤` and
-- the row asserts nothing about the candidate.
--
-- THE STATES ARE CONSTRUCTED, AND THAT IS THE FINDING RATHER THAN A
-- WEAKNESS OF THE ROWS.  A scan reads its accumulator back out of the
-- node and emits it, so the row can only be written by installing an
-- accumulator that IS reducible -- and nothing in the statement, in
-- `Red`, or in `EvalSt` says an installed one ever is.  The take arm
-- is the contrast that makes the point precise: its values pass
-- through untouched and the store only decides HOW MANY, so its row
-- needs no such installation and the arm is store-reading without
-- being store-DEPENDENT.  That split is what the leg above this tier
-- is deciding.
----------------------------------------------------------------------

fstFn : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
fstFn = fstᵗ (varᵗ (here refl))

-- the frame's output is an observable, so the chain below it needs one
-- more hop to reach the run's data root
κ₂ : Path Γ₀ 0 (obs natᵗ) natᵗ
κ₂ = map-f (nat̂ 0) ↠ κ₀

nid₂ : _
nid₂ = Sched.nextNode sch₀

acc₂ : Closed Γ₀ natᵗ
acc₂ = ofᵉ (nat̂ 7 ∷ [])

stScan : EvalSt e₀
stScan = installNode nid₂ (scan-st {t = obs natᵗ} acc₂) st₀

-- LOAD-BEARING: the emitted value IS the stored accumulator, so the
-- row fails unless the candidate holds of what the node was holding.
row-scan-acc : Confirms
  (red-scan {e = e₀} 0 0 fstFn nid₂ κ₂ {3 ∷ []} (tt ∷ []) false sch₀ stScan)
row-scan-acc =
  _ , step-scan , reducible acc₂ ∷ []

-- THE INNER'S OWN FRAME, at the arm that carries rather than spends.
-- An unfinished inner emit passes its values through untouched, so the
-- row is LOAD-BEARING on the carry -- an observable payload leaves the
-- frame and its candidate has to arrive at the conclusion -- and reads
-- no store at all.  The drain and the kill, which are where this
-- statement reads the `*All` node, are NOT reached by it.
row-inner-carry : Confirms
  (red-from-inner {e = e₀} 0 0 mergeAllᵒ nid₂ nid₂ κ₂
     {ofᵉ (nat̂ 7 ∷ []) ∷ []} (reducible (ofᵉ (nat̂ 7 ∷ [])) ∷ []) false sch₀ st₀)
row-inner-carry =
  _ , step-from-inner react-false , reducible (ofᵉ (nat̂ 7 ∷ [])) ∷ []

----------------------------------------------------------------------
-- 5.  THE SAME STEP THROUGH A FLATTENING FRAME, which is where the
-- hop lives.  The three `*All` operators are not statements of their
-- own: each runs its source through a `thru-outer` frame and pushes
-- what came back, so everything an operator DOES -- the queue, the
-- kill, the refusal, the concurrency limit -- is a clause of this
-- step rather than of anything above it.
--
-- LOAD-BEARING at each operator's reading of the store, and at the
-- bounded limit for mergeAll, where `hasRoom` answers false and the
-- value is enqueued instead.  The batch carries a real observable, so
-- the inner is actually subscribed and what comes back is the
-- candidate's own derivation for it -- these rows SPEND the candidate
-- rather than carrying it.  DEGENERATE on the satisfaction half: the
-- frame's output type is the inner's element type, which is data
-- here, so what comes back out is checked by computation.
----------------------------------------------------------------------

-- the flattening rows' output type is data, so everything that comes
-- back out satisfies the candidate by computation
allTriv : ∀ {A : Set} {P : A → Set} → (∀ x → P x) → (vs : List A) → All P vs
allTriv p []       = []
allTriv p (v ∷ vs) = p v ∷ allTriv p vs

nid₃ : _
nid₃ = Sched.nextNode sch₀

sched₃ : Sched Γ₀
sched₃ = record sch₀ { nextNode = Data.Nat.suc nid₃ }

oInner : Closed Γ₀ natᵗ
oInner = ofᵉ (nat̂ 7 ∷ [])

satLive : All (Red {Γ = Γ₀} (obs natᵗ)) (oInner ∷ [])
satLive = reducible oInner ∷ []

instL : _
instL = Sched.nextNode sched₃

subLive : ∀ (op : AllOp) (ns : NodeState Γ₀) → _
subLive op ns =
  proj₁ (proj₂ (reducible oInner (from-inner op nid₃ instL ↠ κ₀) 0 0
                  (record sched₃ { nextNode = Data.Nat.suc instL })
                  (installNode nid₃ ns st₀)))

st₃ : EvalSt e₀
st₃ = installNode nid₃ (mergeAll-st {t = natᵗ} nothing 0 [] false) st₀

row-live-merge : Confirms
  (red-thru {e = e₀} 0 0 mergeAllᵒ nid₃ κ₀ satLive false sched₃ st₃)
row-live-merge =
  _ , step-thru-outer
        (walk-cons (consume-all-sub refl refl
                     (inner refl (subLive mergeAllᵒ (mergeAll-st nothing 0 [] false)) refl))
                   walk-nil)
    , allTriv (λ _ → tt) _

stBound : EvalSt e₀
stBound = installNode nid₃ (mergeAll-st {t = natᵗ} (just 0) 0 [] false) st₀

row-live-queue : Confirms
  (red-thru {e = e₀} 0 0 mergeAllᵒ nid₃ κ₀ satLive false sched₃ stBound)
row-live-queue =
  _ , step-thru-outer (walk-cons (consume-all-enqueue refl refl) walk-nil)
    , allTriv (λ _ → tt) _

stSwitch : EvalSt e₀
stSwitch = installNode nid₃ (switch-st nothing false) st₀

row-live-switch : Confirms
  (red-thru {e = e₀} 0 0 switchᵒ nid₃ κ₀ satLive false sched₃ stSwitch)
row-live-switch =
  _ , step-thru-outer
        (walk-cons (consume-switch-sub refl refl
                     (inner refl (subLive switchᵒ (switch-st nothing false)) refl))
                   walk-nil)
    , allTriv (λ _ → tt) _

stExhaust : EvalSt e₀
stExhaust = installNode nid₃ (exhaust-st false false) st₀

row-live-exhaust : Confirms
  (red-thru {e = e₀} 0 0 exhaustᵒ nid₃ κ₀ satLive false sched₃ stExhaust)
row-live-exhaust =
  _ , step-thru-outer
        (walk-cons (consume-exhaust-sub refl
                     (inner refl (subLive exhaustᵒ (exhaust-st false false)) refl))
                   walk-nil)
    , allTriv (λ _ → tt) _
