-- Naive-Rx: the rxjs operators the TypeScript implementation actually
-- uses, modeled as Mealy machines — so that
-- Implementation/Batch-Simultaneous.agda can be a one-for-one replica
-- of typescript/src/primitives.ts and batch-simultaneous.ts.
--
-- An "observable" here is a machine driven by the world's inputs
-- (In n): it cannot see the future because the future never exists as
-- a value. Each postulate below is one rxjs operator; discharging it
-- means writing the step function that models that operator's
-- synchronous delivery semantics. The set is EXACTLY the operators the
-- TypeScript imports from rxjs — nothing more.
--
-- (r.tap and r.finalize appear in the TypeScript solely to maintain the
-- multicast registry by side effect; in this pure model that bookkeeping
-- lives INSIDE connectRx/shareRx, so they get no separate counterpart.)
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
  -- r.of / r.EMPTY: emit everything at subscription (the frame input),
  -- then complete
  ofRx         : {n : ℕ} {X : Set} → List X → RxObs n X
  emptyRx      : {n : ℕ} {X : Set} → RxObs n X
  -- r.defer: build the machine at subscription time
  deferRx      : {n : ℕ} {X : Set} → (⊤ → RxObs n X) → RxObs n X
  -- r.startWith: prepend one element to the frame
  startWithRx  : {n : ℕ} {X : Set} → X → RxObs n X → RxObs n X
  -- r.endWith: append one element at completion (the batching machine's
  -- drain sentinel)
  endWithRx    : {n : ℕ} {X : Set} → X → RxObs n X → RxObs n X
  -- r.map
  mapRx        : {n : ℕ} {X Y : Set} → (X → Y) → RxObs n X → RxObs n Y
  -- r.scan: THE fundamental one — a scan IS a Mealy machine
  scanRx       : {n : ℕ} {X S : Set} → (S → X → S) → S → RxObs n X → RxObs n S
  -- r.merge (binary; n-ary is folded from it)
  mergeRx      : {n : ℕ} {X : Set} → RxObs n X → RxObs n X → RxObs n X
  -- r.takeWhile (inclusive flag as in rxjs)
  takeWhileRx  : {n : ℕ} {X : Set} → (X → Bool) → Bool → RxObs n X → RxObs n X
  -- the flattening quartet: spawn an inner machine per element, under
  -- the operator's subscription policy
  mergeMapRx   : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  concatMapRx  : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  switchMapRx  : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  exhaustMapRx : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
  -- r.connect: multicast — the selector's branches consume ONE
  -- subscription of the source. The careful one: in a pure model,
  -- fan-out of deliveries is free, but the source's registration
  -- (init) contribution must happen ONCE, not once per branch —
  -- the counting-transparency bookkeeping lives here.
  connectRx    : {n : ℕ} {X Y : Set} → (RxObs n X → RxObs n Y) → RxObs n X → RxObs n Y
  -- r.share: connect on first subscriber, reset on completion /
  -- refcount-zero, reconnect replays (share LIVES, rxjs-confirmed)
  shareRx      : {n : ℕ} {X : Set} → RxObs n X → RxObs n X
