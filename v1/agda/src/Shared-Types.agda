-- The vocabulary BOTH sides speak: what the outside world does to a
-- program (Emissions), what a subscriber observes (Subscription), the
-- program grammar itself (Exp / ExpS), and the Mealy-machine language the
-- implementation is written in.
--
-- Spec and Implementation each define a batchSimultaneous over these
-- types; Formal-Verification states that they agree.
module Shared-Types where

open import Prelude

------------------------------------------------------------------------
-- values

Val : Set
Val = ℕ

------------------------------------------------------------------------
-- Emissions: everything the outside world does to a program with n
-- source subjects.
--
--   syncs  — per source, the values it flushes during the subscribe()
--            call (the frame; ALL of them are one instant by definition)
--   asyncs — the global schedule of .next() calls, in order; one entry
--            = one .next() = one instant. The schedule is global, not
--            per-source: interleaving across sources is observable.
--
-- This is the referee's complete knowledge of a run. Time lives here
-- and nowhere else: tick 0 is the frame, tick k+1 is asyncs entry k.

record Emissions (n : ℕ) : Set where
  constructor emissions
  field
    syncs  : Vec (List Val) n
    asyncs : List (Fin n × Val)
open Emissions public

------------------------------------------------------------------------
-- Subscription: what one subscriber's callback log reads, in order.
-- batchSimultaneous produces a Subscription (List Val) — the element
-- type List Val is what carries the batch boundaries.

Subscription : Set → Set
Subscription A = List A

------------------------------------------------------------------------
-- the shared grammar: one Exp tree, indexed by the number of sources,
-- imported by BOTH Spec/ and Implementation/. Exactly the system's
-- canonical primitives; merge / concat / mergeMap are derived below.

data Exp (n : ℕ) : Set
data ExpS (n : ℕ) : Set

data Exp n where
  srcE        : Fin n → Exp n                      -- a source subject slot
  emptyE      : Exp n
  ofE         : List Val → Exp n
  -- shareE first? i: a subscription of hot share slot i; the flag marks
  -- the CONNECTING ref (the pre-order-first static ref of its binder)
  shareE      : Bool → ℕ → Exp n
  letShareE   : Exp n → Exp n → Exp n
  mapE        : (Val → Val) → Exp n → Exp n
  takeE       : ℕ → Exp n → Exp n
  scanE       : (Val → Val → Val) → Val → Exp n → Exp n
  mergeAllE   : ExpS n → Exp n
  concatAllE  : ExpS n → Exp n
  switchAllE  : ExpS n → Exp n
  exhaustAllE : ExpS n → Exp n

data ExpS n where
  ofS  : List (Exp n) → ExpS n
  mapS : (Val → Exp n) → Exp n → ExpS n

-- the familiar combinators, as the derived forms they really are
mergeE : {n : ℕ} → Exp n → Exp n → Exp n
mergeE a b = mergeAllE (ofS (a ∷ b ∷ []))

concatE : {n : ℕ} → Exp n → Exp n → Exp n
concatE a b = concatAllE (ofS (a ∷ b ∷ []))

mergeMapE : {n : ℕ} → (Val → Exp n) → Exp n → Exp n
mergeMapE f e = mergeAllE (mapS f e)

------------------------------------------------------------------------
-- Mealy machines: the implementation's ONLY computational medium.
--
-- A machine holds a state and, given ONE input, produces a new state
-- and the outputs it emits synchronously in response. The future does
-- not exist as a value a machine could inspect — causality is
-- structural, not a side condition. rxjs's `scan` IS this shape, which
-- is why the TypeScript implementation is written in pure-scan style.

record Machine (I O : Set) : Set₁ where
  field
    State : Set
    start : State
    step  : State → I → State × List O
open Machine public

-- feed a machine a burst of inputs within one step (used by composition:
-- everything an upstream step emits cascades downstream synchronously,
-- inside the same instant)
feed : {I O : Set} (m : Machine I O) → State m → List I → State m × List O
feed m s []       = s , []
feed m s (i ∷ is) =
  let r  = step m s i
      r′ = feed m (fst r) is
  in fst r′ , (snd r ++ snd r′)

-- run: the harness. It lives HERE, not in Implementation/ — the
-- implementation exports machines and never holds the input list.
run : {I O : Set} → Machine I O → List I → List O
run m is = snd (feed m (start m) is)

-- NOTE there is deliberately no element-wise machine-composition
-- operator here: piping elements one at a time would ERASE which
-- outputs one input caused — the very knowledge the frame boundary and
-- an inner's synchronous flush depend on. Operators compose by
-- machine-transformer application instead (each Naive-Rx operator maps
-- whole machines to machines), exactly as rxjs operators are
-- Observable → Observable functions.

------------------------------------------------------------------------
-- the top-level input alphabet: what the world does, one entry at a
-- time. `frame` is the subscribe() call itself, carrying every source's
-- synchronous flush; `next` is one .next(); `endSlot i` completes ONE
-- source — its own instant, exactly like the TS driver's per-subject
-- .end() calls (a concat leg spawned when its predecessor completes
-- registers normally and fins on ITS OWN later input); `end` is the
-- final teardown sentinel (the TS r.endWith, promoted to a type).
--
-- `spawnAt k` is NOT produced by flatten — it is the SYNTHESIZED
-- subscription input a mid-run spawn feeds a fresh inner (Naive-Rx's
-- spawnInput). It carries how many sources have already completed by the
-- spawn instant (k = threshold: slot i is done iff toℕ i < k). A source
-- subscribed after its own completion must complete immediately — the TS
-- InstantSubject's `ended ? of([fin])` — and a plain empty frame cannot
-- express that, since a fresh copy never sees the past endSlot. Because
-- completions are serialized in slot order at the very end, the current
-- input pins k exactly (0 during frame/next, suc j at endSlot j, n at end).

data In (n : ℕ) : Set where
  frame   : Vec (List Val) n → In n
  spawnAt : ℕ → In n
  next    : Fin n → Val → In n
  endSlot : Fin n → In n
  end     : In n

-- flatten: an Emissions record, serialized exactly as the machine will
-- experience it — subscribe, the .next() schedule, then the sources
-- completed in slot order, then teardown. The machine sees THIS list
-- one element at a time and nothing else.
flatten : {n : ℕ} → Emissions n → List (In n)
flatten em =
  frame (syncs em)
    ∷ (map (λ p → next (fst p) (snd p)) (asyncs em)
       ++ map endSlot allFins
       ++ (end ∷ []))
