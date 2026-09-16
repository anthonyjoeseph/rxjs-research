-- THE REMAINING LEAVES OF THE REDUCIBILITY BODY, INSTANTIATED.
--
-- WHAT IS AT RISK, AND IT IS THE SAME RISK IN BOTH.  The
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
-- NOT REACHED, and each is a region rather than a program.  A
-- flattener's node whose inner is genuinely RUNNING -- a switch
-- holding a live current, an exhaust already active -- so the refusal
-- reached below is the concurrency one rather than the exhaust's.  A
-- literal inner retires inside its own subscribe frame, so every
-- running-inner region wants a scripted source the empty slot table
-- here cannot supply.
--
-- TARGET: red-thru @f94cad
module Probed.Reducible-Arms where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (nothing; just)
import Data.Nat
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init; mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp;
  NodeState; from-inner; _↠_; mergeAll-st; switch-st; exhaust-st; installNode)
open import Rx.Evaluator.Reducible using (Red; reducible; red-thru)

open import Rx.Evaluator.Domain using (step-thru-outer; walk-nil; walk-cons; inner; consume-all-sub; consume-all-enqueue;
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
-- 4.  THE SAME STEP THROUGH A FLATTENING FRAME, which is where the
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
    , allTriv (λ _ → tt) _ , tt

stBound : EvalSt e₀
stBound = installNode nid₃ (mergeAll-st {t = natᵗ} (just 0) 0 [] false) st₀

row-live-queue : Confirms
  (red-thru {e = e₀} 0 0 mergeAllᵒ nid₃ κ₀ satLive false sched₃ stBound)
row-live-queue =
  _ , step-thru-outer (walk-cons (consume-all-enqueue refl refl) walk-nil)
    , allTriv (λ _ → tt) _ , tt

----------------------------------------------------------------------
-- 5.  A BURST OF MORE THAN ONE VALUE, WHERE THE SECOND STEP'S GUARD
-- READS WHAT THE FIRST STEP WROTE.  Every row above walks a ONE-value
-- burst, so the walk reaches its terminal step immediately and the
-- state it threads is never read back by anything.  Here two
-- observables arrive together at a node whose limit is already full,
-- so the first is queued and the second is decided against a queue
-- that is no longer empty -- which is the node-holding-something
-- region no row above stands in.
--
-- LOAD-BEARING on the threading.  The clause itself is reached one row
-- up, at a state written down by hand; what no row reached is the walk
-- CARRYING the first step's node state into the second's lookup, and
-- the second `refl` is exactly that -- it holds only if the queue the
-- guard reads is the one the first step appended to.  A walk handing
-- the ORIGINAL state to its recursive step would leave that `refl`
-- unprovable.
--
-- WHY THE MIXED BURST IS NOT THE ROW HERE, and it is a fact about the
-- machine rather than about this file.  The obvious threading row is a
-- limit of one with the first value subscribed and the second refused
-- by the state it left; that derivation CANNOT BE BUILT.  A literal
-- inner completes inside its own subscribe frame, so the active count
-- is back at zero by the time the second value is considered and
-- `hasRoom` answers true again.  At any positive limit a burst of
-- synchronously-completing inners therefore subscribes every entry,
-- and the refusal path is reachable mid-burst only with an inner that
-- outlives its own subscribe frame -- which needs a scripted source
-- rather than a literal, the same harness the switch and exhaust
-- running-inner states want.
--
-- NOT REACHED STILL: a subscribe and a refusal in ONE walk, per the
-- paragraph above; and a switch or exhaust whose inner is genuinely
-- running.
----------------------------------------------------------------------

satBurst : All (Red {Γ = Γ₀} (obs natᵗ)) (oInner ∷ oInner ∷ [])
satBurst = reducible oInner ∷ reducible oInner ∷ []

stFull : EvalSt e₀
stFull = installNode nid₃ (mergeAll-st {t = natᵗ} (just 0) 0 [] false) st₀

row-live-burst : Confirms
  (red-thru {e = e₀} 0 0 mergeAllᵒ nid₃ κ₀ satBurst false sched₃ stFull)
row-live-burst =
  _ , step-thru-outer
        (walk-cons (consume-all-enqueue refl refl)
          (walk-cons (consume-all-enqueue refl refl) walk-nil))
    , allTriv (λ _ → tt) _ , tt

stSwitch : EvalSt e₀
stSwitch = installNode nid₃ (switch-st nothing false) st₀

row-live-switch : Confirms
  (red-thru {e = e₀} 0 0 switchᵒ nid₃ κ₀ satLive false sched₃ stSwitch)
row-live-switch =
  _ , step-thru-outer
        (walk-cons (consume-switch-sub refl refl
                     (inner refl (subLive switchᵒ (switch-st nothing false)) refl))
                   walk-nil)
    , allTriv (λ _ → tt) _ , tt

stExhaust : EvalSt e₀
stExhaust = installNode nid₃ (exhaust-st false false) st₀

row-live-exhaust : Confirms
  (red-thru {e = e₀} 0 0 exhaustᵒ nid₃ κ₀ satLive false sched₃ stExhaust)
row-live-exhaust =
  _ , step-thru-outer
        (walk-cons (consume-exhaust-sub refl
                     (inner refl (subLive exhaustᵒ (exhaust-st false false)) refl))
                   walk-nil)
    , allTriv (λ _ → tt) _ , tt
