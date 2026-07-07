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
  wt    : ℕ → Ev A      -- weight: this emit accounts for `k` delivery chains
                        -- this instant (a serial join stamps its coalesce
                        -- count; absent ⇒ 1). The counting machine drains its
                        -- owed-count by the weight, so a serial join's single
                        -- coalesced emit still closes an instant of K chains.

-- what ONE downstream next-callback invocation carries
-- (TypeScript: InstEmit { provenance, events })
Emit : Set → Set
Emit A = Prov × List (Ev A)

-- how many delivery chains this emit accounts for: the SUM of its stamped
-- weight markers, or 1 if it has none (an ordinary single-chain emit). A
-- serial join marks each flush it coalesces with one `wt`, so an instant of
-- K chains folded into one emit reads back as weight K — and because the
-- markers survive stripFin, nested serial joins' weights propagate outward.
sumWt : {A : Set} → List (Ev A) → ℕ
sumWt []          = 0
sumWt (wt k ∷ es) = k + sumWt es
sumWt (_ ∷ es)    = sumWt es

weightOf : {A : Set} → List (Ev A) → ℕ
weightOf evs = let s = sumWt evs in if eqℕ s 0 then 1 else s

-- drop weight markers (a fold re-stamps its own total, so inner markers are
-- absorbed rather than double-counted)
stripWt : {A : Set} → List (Ev A) → List (Ev A)
stripWt []          = []
stripWt (wt _ ∷ es) = stripWt es
stripWt (ev ∷ es)   = ev ∷ stripWt es

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
-- the operator set (one per rxjs export the TypeScript uses).
-- All DEFINED except the three serial flattening policies.

-- r.of / r.EMPTY: emit everything on the first input received (the
-- subscription moment), then nothing
ofRx : {n : ℕ} {X : Set} → List X → RxObs n X
ofRx xs = record
  { State = Bool ; start = false
  ; step  = λ s _ → true , (if s then [] else xs) }

emptyRx : {n : ℕ} {X : Set} → RxObs n X
emptyRx = ofRx []

-- r.map
mapRx : {n : ℕ} {X Y : Set} → (X → Y) → RxObs n X → RxObs n Y
mapRx f m = record
  { State = State m ; start = start m
  ; step  = λ s i → let r = step m s i in fst r , map f (snd r) }

-- r.endWith: append one element when the run ends (the `end` input) —
-- an operator CAN inspect the world input, it just usually doesn't care
endWithRx : {n : ℕ} {X : Set} → X → RxObs n X → RxObs n X
endWithRx {n} {X} x m = record
  { State = State m ; start = start m
  ; step  = λ s i → let r = step m s i in fst r , atEnd i (snd r) }
  where
    atEnd : In n → List X → List X
    atEnd end os = os ++ (x ∷ [])
    atEnd _   os = os

-- r.scan: THE fundamental one — a scan IS a Mealy machine. One input
-- may carry several elements; each threads the accumulator and emits.
-- The burst-fold is TOP-LEVEL so proofs can reason about it: threading
-- the accumulator through one input's elements, emitting each running
-- state.
scanBurst : {X S : Set} → (S → X → S) → S → List X → S × List S
scanBurst f s []       = s , []
scanBurst f s (x ∷ xs) = let r = scanBurst f (f s x) xs in fst r , f s x ∷ snd r

scanRx : {n : ℕ} {X S : Set} → (S → X → S) → S → RxObs n X → RxObs n S
scanRx {n} {X} {S} f z m = record
  { State = State m × S ; start = start m , z
  ; step  = λ s i →
      let r = step m (fst s) i
          o = scanBurst f (snd s) (snd r)
      in (fst r , fst o) , snd o }

-- r.merge (binary; n-ary is folded from it). Subscribes left before
-- right: within one step, left's outputs precede right's (registration
-- rank as delivery order).
mergeRx : {n : ℕ} {X : Set} → RxObs n X → RxObs n X → RxObs n X
mergeRx m₁ m₂ = record
  { State = State m₁ × State m₂ ; start = start m₁ , start m₂
  ; step  = λ s i →
      let r₁ = step m₁ (fst s) i
          r₂ = step m₂ (snd s) i
      in (fst r₁ , fst r₂) , snd r₁ ++ snd r₂ }

-- r.takeWhile (inclusive flag as in rxjs); once dead, the upstream is
-- unsubscribed — its state freezes and nothing more is emitted
takeWhileRx : {n : ℕ} {X : Set} → (X → Bool) → Bool → RxObs n X → RxObs n X
takeWhileRx {n} {X} p incl m = record
  { State = State m × Bool ; start = start m , true
  ; step  = λ s i →
      if snd s
      then (let r = step m (fst s) i
                t = takeW (snd r)
            in (fst r , snd t) , fst t)
      else (s , []) }
  where
    takeW : List X → List X × Bool
    takeW []       = [] , true
    takeW (x ∷ xs) =
      if p x
      then (let r = takeW xs in x ∷ fst r , snd r)
      else ((if incl then x ∷ [] else []) , false)

-- "subscribing" a machine mid-run: a spawn during the real frame IS a
-- frame subscription (it sees the sync flushes); a spawn during any
-- later input gets a synthesized frame with empty flushes — and NOT the
-- in-flight input itself (an rxjs Subject snapshots its subscribers at
-- dispatch start: the upstream-race rule)
spawnInput : {n : ℕ} → In n → In n
spawnInput         (frame ss)  = frame ss
spawnInput         (spawnAt k) = spawnAt k
spawnInput         (next _ _)  = spawnAt 0
spawnInput         (endSlot j) = spawnAt (suc (toℕ j))
spawnInput {n = n} end         = spawnAt n

-- r.mergeMap: every element spawns an inner machine, all stay live.
-- The state holds each running inner as a dependent pair — WHICH
-- element spawned it, paired with the state of that element's machine.
-- Per step, delivery is in registration-rank order: the outer chain
-- first (each spawned inner's synchronous flush riding at its trigger's
-- position), then the existing inners in spawn order.
--
-- The two per-step helpers are TOP-LEVEL (not a where block) so the
-- proofs can state lemmas about them: stepping the live inners, and
-- spawning fresh ones. A running inner is a dependent pair — which
-- element spawned it, paired with the state of that element's machine.
MMRun : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → Set
MMRun {n} {X} f = Σ X (λ x → State (f x))

mmStepAll : {n : ℕ} {X Y : Set} (f : X → RxObs n Y)
          → In n → List (MMRun f) → List (MMRun f) × List Y
mmStepAll f i []              = [] , []
mmStepAll f i ((x ▹ sx) ∷ rs) =
  let r    = step (f x) sx i
      rest = mmStepAll f i rs
  in ((x ▹ fst r) ∷ fst rest) , snd r ++ snd rest

mmSpawnAll : {n : ℕ} {X Y : Set} (f : X → RxObs n Y)
           → In n → List X → List (MMRun f) × List Y
mmSpawnAll f i []       = [] , []
mmSpawnAll f i (x ∷ xs) =
  let r    = step (f x) (start (f x)) i
      rest = mmSpawnAll f i xs
  in ((x ▹ fst r) ∷ fst rest) , snd r ++ snd rest

mergeMapRx : {n : ℕ} {X Y : Set} → (X → RxObs n Y) → RxObs n X → RxObs n Y
mergeMapRx {n} {X} {Y} f m = record
  { State = State m × List (MMRun f)
  ; start = start m , []
  ; step  = λ s i →
      let u  = step m (fst s) i
          sp = mmSpawnAll f (spawnInput i) (snd u)
          ex = mmStepAll f i (snd s)
      in (fst u , fst ex ++ fst sp) , snd sp ++ snd ex }

-- the serial flattening policies (concatMap queues, switchMap cuts,
-- exhaustMap drops while busy) — same Running-state architecture as
-- mergeMapRx plus the policy bookkeeping.
--
-- rxjs carries completion on a SEPARATE channel; the machine model
-- carries it in-band. The serial policies are exactly the operators
-- that must OBSERVE inner completion (a queued inner subscribes when
-- the live one completes; an arrival is dropped only while one is
-- open), so each takes the in-band completion test as its first
-- argument: `isLast y` = "y is the last element this inner will emit"
-- (rxjs's complete signal, reified).

-- r.concatMap: one inner live at a time; arrivals queue. When the live
-- inner completes, the queue drains INSIDE the same step — a queued
-- inner subscribes at the completion instant and its synchronous flush
-- rides there; a synchronously completing inner hands off to the next.
concatMapRx : {n : ℕ} {X Y : Set} → (Y → Bool)
            → (X → RxObs n Y) → RxObs n X → RxObs n Y
concatMapRx {n} {X} {Y} isLast f m = record
  { State = State m × Maybe Running × List X
  ; start = start m , nothing , []
  ; step  = λ s i →
      let u = step m (fst s) i                 -- the outer, first (its rank
      in go (fst u) (fst (snd s))              --  precedes every inner's)
            (snd (snd s) ++ snd u) i }
  where
    Running : Set
    Running = Σ X (λ x → State (f x))

    drain : In n → List X → (Maybe Running × List X) × List Y
    drain i []       = (nothing , []) , []
    drain i (x ∷ xs) =
      let r = step (f x) (start (f x)) i
      in if any isLast (snd r)
         then (let d = drain i xs in fst d , snd r ++ snd d)
         else ((just (x ▹ fst r) , xs) , snd r)

    go : State m → Maybe Running → List X → In n
       → (State m × Maybe Running × List X) × List Y
    go sm nothing        que i =
      let d = drain (spawnInput i) que
      in (sm , fst (fst d) , snd (fst d)) , snd d
    go sm (just (x ▹ sx)) que i =
      let r = step (f x) sx i
      in if any isLast (snd r)
         then (let d = drain (spawnInput i) que
               in (sm , fst (fst d) , snd (fst d)) , snd r ++ snd d)
         else ((sm , just (x ▹ fst r) , que) , snd r)

-- r.switchMap: a new arrival CUTS the live inner BEFORE it reacts to
-- the in-flight input (the outer's delivery rank precedes every
-- inner's, and rxjs unsubscription takes effect mid-dispatch). Within
-- one burst of arrivals each sibling's synchronous flush still fires
-- before the next sibling cuts it; only the last stays live.
switchMapRx : {n : ℕ} {X Y : Set} → (Y → Bool)
            → (X → RxObs n Y) → RxObs n X → RxObs n Y
switchMapRx {n} {X} {Y} isLast f m = record
  { State = State m × Maybe Running
  ; start = start m , nothing
  ; step  = λ s i →
      let u = step m (fst s) i
      in go (fst u) (snd s) (snd u) i }
  where
    Running : Set
    Running = Σ X (λ x → State (f x))

    spawnSeq : In n → List X → Maybe Running × List Y
    spawnSeq i []       = nothing , []
    spawnSeq i (x ∷ []) =
      let r = step (f x) (start (f x)) i
      in (if any isLast (snd r) then nothing else just (x ▹ fst r)) , snd r
    spawnSeq i (x ∷ xs@(_ ∷ _)) =
      let r    = step (f x) (start (f x)) i
          rest = spawnSeq i xs
      in fst rest , snd r ++ snd rest

    go : State m → Maybe Running → List X → In n
       → (State m × Maybe Running) × List Y
    go sm nothing         [] i = (sm , nothing) , []
    go sm (just (x ▹ sx)) [] i =
      let r = step (f x) sx i
      in (sm , (if any isLast (snd r) then nothing else just (x ▹ fst r)))
         , snd r
    go sm live xs@(_ ∷ _) i =                  -- the cut: live never reacts
      let sp = spawnSeq (spawnInput i) xs
      in (sm , fst sp) , snd sp

-- r.exhaustMap: an arrival is DROPPED (not queued) while the previously
-- accepted inner is still open; a synchronously completing inner frees
-- the slot for its own burst siblings.
exhaustMapRx : {n : ℕ} {X Y : Set} → (Y → Bool)
             → (X → RxObs n Y) → RxObs n X → RxObs n Y
exhaustMapRx {n} {X} {Y} isLast f m = record
  { State = State m × Maybe Running
  ; start = start m , nothing
  ; step  = λ s i →
      let u = step m (fst s) i
      in go (fst u) (snd s) (snd u) i }
  where
    Running : Set
    Running = Σ X (λ x → State (f x))

    exSeq : In n → List X → Maybe Running × List Y
    exSeq i []       = nothing , []
    exSeq i (x ∷ xs) =
      let r = step (f x) (start (f x)) i
      in if any isLast (snd r)
         then (let rest = exSeq i xs in fst rest , snd r ++ snd rest)
         else (just (x ▹ fst r) , snd r)       -- still open: xs dropped

    go : State m → Maybe Running → List X → In n
       → (State m × Maybe Running) × List Y
    go sm (just (x ▹ sx)) xs i =               -- open: every arrival dropped
      let r = step (f x) sx i
      in (sm , (if any isLast (snd r) then nothing else just (x ▹ fst r)))
         , snd r
    go sm nothing         xs i =
      let sp = exSeq (spawnInput i) xs
      in (sm , fst sp) , snd sp
