-- Naive-Rx: the rxjs operators the TypeScript implementation actually
-- uses, modeled as Mealy machines — so that
-- Implementation/Batch-Simultaneous.agda can be a one-for-one replica
-- of typescript/src/primitives.ts and batch-simultaneous.ts.
--
-- An "observable" here is a machine driven by the world's inputs
-- (In n): it cannot see the future because the future never exists as
-- a value. Each postulate below is one rxjs operator; discharging it
-- means writing the step function that models that operator's
-- synchronous delivery semantics.
--
-- What has NO counterpart here, and why (the pure model dissolves it):
--   r.tap / r.finalize — exist in the TS solely to maintain the
--     multicast registry by side effect; pure machines have no effects
--     to observe.
--   r.defer / r.startWith — exist in the TS to wrap the Subject's
--     mutable `ended` flag and registration emit; the naive subject
--     (srcI) is a direct machine and needs neither.
--   r.connect / r.share — multicast. Machine values are DETERMINISTIC:
--     two copies of a machine driven by the same inputs produce
--     identical outputs, so fan-out is free and the serial joins'
--     connect dissolves into using the outer machine twice (the value
--     branch strips registration events, so nothing double-counts).
--     share's per-ref semantics (connecting ref vs late ref) lives in
--     shareRefI, on the Canonical (non-resetting) domain the theorem
--     is stated over.
--
-- Spawning semantics shared by the flattening quartet: "subscribing"
-- an inner machine mid-run means feeding the fresh machine a synthesized
-- subscription input — `frame` with empty per-source flushes — during
-- the current step, so its synchronous flush coalesces into the step
-- that spawned it. The in-flight input itself is NOT delivered to the
-- new machine (an rxjs Subject snapshots its subscribers at dispatch
-- start — the upstream-race rule).
module Implementation.Naive-Rx where

open import Prelude
open import Shared-Types

------------------------------------------------------------------------
-- the protocol: what flows between operators (typescript/src/types.ts).
-- No timestamps anywhere — that is the point.

Prov : Set
Prov = ℕ

data Ev (A : Set) : Set where
  init  : Prov → Ev A   -- a subscription chain of root provenance came alive
  value : A → Ev A      -- a value
  close : Prov → Ev A   -- a registration ended (take cut, switch switched away)
  fin   : Ev A          -- completion, carried IN-BAND with its cascade

-- what ONE downstream next-callback invocation carries
-- (TypeScript: InstEmit { provenance, events })
Emit : Set → Set
Emit A = Prov × List (Ev A)

-- the types.ts helpers, verbatim
values : {A : Set} → List (Ev A) → List A
values []             = []
values (value v ∷ es) = v ∷ values es
values (_ ∷ es)       = values es

hasFinEvs : {A : Set} → List (Ev A) → Bool
hasFinEvs []         = false
hasFinEvs (fin ∷ _)  = true
hasFinEvs (_ ∷ es)   = hasFinEvs es

hasFin : {A : Set} → Emit A → Bool
hasFin e = hasFinEvs (snd e)

stripFin : {A : Set} → List (Ev A) → List (Ev A)
stripFin []         = []
stripFin (fin ∷ es) = stripFin es
stripFin (ev ∷ es)  = ev ∷ stripFin es

-- init/close only (TS: triggerItem's `others`)
initsCloses : {A : Set} → List (Ev A) → List (Ev A)
initsCloses []             = []
initsCloses (init p ∷ es)  = init p ∷ initsCloses es
initsCloses (close p ∷ es) = close p ∷ initsCloses es
initsCloses (_ ∷ es)       = initsCloses es

-- everything but the values (a late share ref registers, replays nothing)
dropValues : {A : Set} → List (Ev A) → List (Ev A)
dropValues []             = []
dropValues (value _ ∷ es) = dropValues es
dropValues (ev ∷ es)      = ev ∷ dropValues es

------------------------------------------------------------------------
-- a naive rxjs Observable of elements X, in a world with n sources:
-- a Mealy machine from world inputs to elements

RxObs : ℕ → Set → Set₁
RxObs n X = Machine (In n) X

-- .subscribe(console.log): drive the machine over the serialized world
-- and collect the callback log
subscribeRx : {n : ℕ} {X : Set} → RxObs n X → Emissions n → Subscription X
subscribeRx m em = run m (flatten em)

------------------------------------------------------------------------
-- the operator set (one postulate per rxjs export the TypeScript uses)

postulate
  -- r.of / r.EMPTY: emit everything on the first input received (the
  -- subscription moment), then nothing
  ofRx         : {n : ℕ} {X : Set} → List X → RxObs n X
  emptyRx      : {n : ℕ} {X : Set} → RxObs n X
  -- r.endWith: append one element when the run ends (the `end` input)
  endWithRx    : {n : ℕ} {X : Set} → X → RxObs n X → RxObs n X
  -- r.map
  mapRx        : {n : ℕ} {X Y : Set} → (X → Y) → RxObs n X → RxObs n Y
  -- r.scan: THE fundamental one — a scan IS a Mealy machine
  scanRx       : {n : ℕ} {X S : Set} → (S → X → S) → S → RxObs n X → RxObs n S
  -- r.merge (binary; n-ary is folded from it). Subscribes left before
  -- right: within one step, left's outputs precede right's.
  mergeRx      : {n : ℕ} {X : Set} → RxObs n X → RxObs n X → RxObs n X
  -- r.takeWhile (inclusive flag as in rxjs)
  takeWhileRx  : {n : ℕ} {X : Set} → (X → Bool) → Bool → RxObs n X → RxObs n X
  -- the flattening quartet: spawn an inner machine per element, under
  -- the operator's native subscription policy (mergeMap: all live;
  -- concatMap: queue; switchMap: cut; exhaustMap: drop while busy)
  mergeMapRx   : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  concatMapRx  : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  switchMapRx  : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  exhaustMapRx : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
