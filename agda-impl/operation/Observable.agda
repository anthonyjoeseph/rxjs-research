{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  The shared engine, run in IO: real refs, user-written
-- colds that may perform IO.  Nothing here is proven; it is checked
-- against the TypeScript by the oracle.
--
-- Asynchrony is JavaScript's, not threads': a cold sets timers with
-- `after`, and the loop runs the earliest, ties in the order they were
-- set.  Time is the loop's own counter, so a run takes no wall-clock
-- time and two runs of one program agree.
--
-- `subscribe` is the one place the rules bend.  The pure runtime closes
-- the engine's recursion by unfolding it n times; a real program needs
-- every unfolding, and IO cannot re-run to take the limit, so here it is
-- closed with Haskell's `fix`.  That is sound only because nothing in the
-- engine forces a `defer`, a stored callback or the loop's next turn
-- before it is reached — which laziness then delivers.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import Level using (Lift; lift; lower; 0ℓ) renaming (suc to lsuc)

open import Tree using (Obs; Later)
open import operation.AbstractObservable using (Prims; module Run)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Timeline)

------------------------------------------------------------------------
-- Haskell's refs

postulate
  IORef      : Set → Set
  newIORef   : ∀ {A} → A → IO (IORef A)
  readIORef  : ∀ {A} → IORef A → IO A
  writeIORef : ∀ {A} → IORef A → A → IO ⊤

  fix! : ∀ {ℓ} {A : Set ℓ} → (A → A) → A

{-# FOREIGN GHC import qualified Data.IORef #-}
{-# FOREIGN GHC import qualified Data.Function #-}
{-# COMPILE GHC IORef = type Data.IORef.IORef #-}
{-# COMPILE GHC newIORef = \ _ -> Data.IORef.newIORef #-}
{-# COMPILE GHC readIORef = \ _ -> Data.IORef.readIORef #-}
{-# COMPILE GHC writeIORef = \ _ -> Data.IORef.writeIORef #-}
{-# COMPILE GHC fix! = \ _ _ -> Data.Function.fix #-}

private
  infixl 1 _>>_
  _>>_ : ∀ {A : Set} → IO ⊤ → IO A → IO A
  m >> n = m >>= λ _ → n

  unless : IORef Bool → IO ⊤ → IO ⊤
  unless r m = readIORef r >>= λ b → if b then pure tt else m

------------------------------------------------------------------------
-- Colds

-- A cold, as the user writes it.  `subscription` runs when the cold is
-- subscribed; every `produce` it makes before returning is the
-- synchronous burst.  A `produce` from a timer it set is an async
-- emission.  `teardown` runs once, on completion or unsubscribe; after
-- it, `produce` and `complete` are ignored.
record Started (Internal : Set) : Set where
  field
    subscription : IO Internal
    teardown     : Internal → IO ⊤

-- What a cold is handed: how to emit, and how to set a timer.
-- `closed` is rxjs's `subscriber.closed`, for a producer to poll.
record Emit (A : Set) : Set where
  field
    produce  : A → IO ⊤
    complete : IO ⊤
    closed   : IO Bool
    after    : ℕ → IO ⊤ → IO ⊤

-- `create` takes an `Emit`, not its fields curried: with `Internal`
-- erased MAlonzo compiles this record to a `newtype`, and GHC rejects a
-- newtype whose field mentions `IO` bare — its kind-polymorphic
-- arguments become existentials.
record IOCold (A : Set) : Set₁ where
  field
    Internal : Set
    create   : Emit A → Started Internal

-- A registered observer, as the IO it runs.
record SinkSlot (A : Set) : Set where
  field
    onNext     : A → IO ⊤
    onComplete : IO ⊤
    isClosed   : IO Bool

-- A started cold: whether it is spent, and its teardown once known —
-- not before its `subscription` has returned.
record Slot : Set where
  field
    spent    : IORef Bool
    tearDown : IORef (Maybe (IO ⊤))

-- IO has one world, so every name is valid everywhere.  A record with no
-- fields, so any two worlds are equal by eta and weakening is the identity.
record One : Set₁ where

IOᴾ : Prims
IOᴾ = record
  { World = One ; _⊑_ = λ _ _ → ⊤ ; ⊑-refl = tt ; _⨾_ = λ _ _ → tt
  ; RefOf = λ _ _ → IORef ; Sink = λ _ → SinkSlot ; Handle = λ _ → Slot
  ; wkRef = λ _ _ r → r ; wkSink = λ _ s → s ; wkHandle = λ _ h → h
  ; Cold = IOCold ; Eff = IO }

open Run IOᴾ

Observable : Set → Set₁
Observable = Obs IOCold []

------------------------------------------------------------------------
-- The runtime

-- The engine's monad: IO, lifted to the universe its tables live in.
M : One → Set → Set₁
M _ A = IO (Lift (lsuc 0ℓ) A)

private
  ret : ∀ {w A} → IO A → M w A
  ret m = m >>= λ a → pure (lift a)

  low : ∀ {w A} → M w A → IO A
  low m = m >>= λ a → pure (lower a)

-- The loop's state: the clock, and the timers in the order they fire.
record Loop : Set where
  field
    clock  : IORef ℕ
    timers : IORef (List (ℕ × IO ⊤))

private
  -- After every timer due no later: two timers due together fire in the
  -- order they were set.
  insert : ℕ → IO ⊤ → List (ℕ × IO ⊤) → List (ℕ × IO ⊤)
  insert d a []              = (d , a) ∷ []
  insert d a ((e , b) ∷ ts) = if e ≤ᵇ d then (e , b) ∷ insert d a ts else (d , a) ∷ (e , b) ∷ ts

  setTimer : Loop → ℕ → IO ⊤ → IO ⊤
  setTimer lp d a = readIORef (Loop.clock lp) >>= λ now → readIORef (Loop.timers lp) >>= λ ts →
                    writeIORef (Loop.timers lp) (insert (now + d) a ts)

  runTeardown : Slot → IO ⊤
  runTeardown sl = readIORef (Slot.tearDown sl) >>= λ where
    nothing  → pure tt
    (just t) → writeIORef (Slot.tearDown sl) nothing >> t

  -- Spends the slot, once.
  spend : Slot → IO ⊤ → IO ⊤
  spend sl m = unless (Slot.spent sl) (writeIORef (Slot.spent sl) true >> m >> runTeardown sl)

  -- Runs the user's `subscription`, delivering each `produce` as it is
  -- made.  A cold spent during its own subscription is torn down the
  -- moment its teardown exists.
  playCold : Loop → ∀ {A} → IOCold A → SinkSlot A → IO Slot
  playCold lp {A} c sk =
    newIORef false >>= λ sp → newIORef nothing >>= λ td →
    let sl = record { spent = sp ; tearDown = td }
        st = IOCold.create c (record
          { produce  = λ a → unless sp (SinkSlot.onNext sk a)
          ; complete = spend sl (SinkSlot.onComplete sk)
          ; closed   = readIORef sp >>= λ s → if s then pure true else SinkSlot.isClosed sk
          ; after    = setTimer lp })
    in Started.subscription st >>= λ i →
       writeIORef td (just (Started.teardown st i)) >>
       readIORef sp >>= λ s → (if s then runTeardown sl else pure tt) >> pure sl

  nextTimer : Loop → IO Bool
  nextTimer lp = readIORef (Loop.timers lp) >>= λ where
    []             → pure false
    ((t , a) ∷ ts) → writeIORef (Loop.timers lp) ts >> writeIORef (Loop.clock lp) t >> a >> pure true

IOᴿ : Loop → Runtime
IOᴿ lp = record
  { M          = M
  ; return     = λ a → pure (lift a)
  ; _>>=_      = λ m f → m >>= λ a → f (lower a)
  ; newRefᴿ    = λ _ a k → newIORef a >>= k tt
  ; readRefᴿ   = λ r k → readIORef r >>= k tt
  ; writeRefᴿ  = λ r a → ret (writeIORef r a)
  ; registerᴿ  = λ run n c x k → k tt (record { onNext = λ a → low (run (n a)) ; onComplete = low (run c) ; isClosed = low (run x) })
  ; sendᴿ      = λ _ sk a → ret (SinkSlot.onNext sk a)
  ; finishᴿ    = λ _ sk → ret (SinkSlot.onComplete sk)
  ; startColdᴿ = λ _ c sk k → playCold lp c sk >>= k tt
  ; stopᴿ      = λ sl → ret (spend sl (pure tt))
  ; effᴿ       = ret
  ; divergeᴿ   = fix! λ d → d
  ; nextᴿ      = λ _ → ret (nextTimer lp)
  }

------------------------------------------------------------------------
-- A timeline, played

-- Frame 0 inline, then each later frame on a timer set where the burst
-- before it ends.  A closed subscriber or a teardown stops the playing.
fromTimeline : ∀ {A} → Timeline A → IOCold A
fromTimeline {A} c = record
  { Internal = IORef Bool
  ; create   = λ e → record
      { subscription = newIORef false >>= λ off → first e off (lower c) >> pure off
      ; teardown     = λ off → writeIORef off true }
  }
  where
    -- `self` plays the frames after this burst.
    burst : Emit A → IORef Bool → (Time → ML A → IO ⊤) → Time → Burst A → IO ⊤
    burst e off self t = fix! λ go b → Emit.closed e >>= λ c → if c then pure tt else step go b
      where
        step : (Burst A → IO ⊤) → Burst A → IO ⊤
        step go (emit a k) = Emit.produce e a >> unless off (go (Burst∞.force k))
        step go (stall k)  = go (Burst∞.force k)
        step go (close k)  = self t (ML∞.force k)

    play : Emit A → IORef Bool → Time → ML A → IO ⊤
    play e off = fix! λ self now → λ where
      done     → Emit.complete e
      quiet    → pure tt
      (at t b) → Emit.after e (t ∸ now) (unless off (burst e off self t b))

    first : Emit A → IORef Bool → ML A → IO ⊤
    first e off (at 0 b) = burst e off (play e off) 0 b
    first e off m        = play e off 0 m

------------------------------------------------------------------------
-- The entry point

-- The recursion, closed for real.
deferred∞ : Deferred
deferred∞ = fix! {A = Deferred} λ d l ρ → compileWith (λ l′ ρ′ → d l′ ρ′) (Later.force l) ρ

module _ (lp : Loop) where
  open Engine (IOᴿ lp)

  private
    run∞ : RunAct
    run∞ = fix! λ self {w} {B} → interpret (λ {w′} {B′} → self {w′} {B′}) {w} {B}

    loop∞ : M _ ⊤
    loop∞ = fix! (loopStep run∞)

  running : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
  running {A} o f c = low (drive run∞ loop∞ (compileWith deferred∞ o []) observer)
    where
      observer : Observer A _
      observer = record
        { next     = λ a → eff (readIORef (Loop.clock lp) >>= λ t → f t a) λ _ → done tt
        ; complete = eff c λ _ → done tt
        ; closed   = done false
        }

-- THE ENTRY POINT: runs until no timer is left.  Each value is handed
-- the loop's time at its arrival; the last argument runs on completion.
subscribe : ∀ {A} → Observable A → (Time → A → IO ⊤) → IO ⊤ → IO ⊤
subscribe o f c = newIORef 0 >>= λ cl → newIORef [] >>= λ ts → running (record { clock = cl ; timers = ts }) o f c
