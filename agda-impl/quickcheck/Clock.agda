{-# OPTIONS --guardedness #-}

-- THE HARNESS'S CLOCK.  The IO runtime keeps no time, so the oracle keeps
-- it: a virtual clock and a queue of timers, handed to every input cold
-- it builds.  A run takes no wall-clock time, and two runs of one program
-- agree.
--
-- The queue is touched by one thread at a time: by the subscribing thread
-- during the subscribe burst, then by `fire`'s alone — which starts only
-- once the burst is over, and runs every timer to the end.  Timers due
-- together fire in the order they were set.
module quickcheck.Clock where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)

open import denotation.MonotonicList.Events using (From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; fixed; fresh; timelineAt; Pos; ix)
open import operation.Observable using (IORef; newIORef; readIORef; writeIORef; IOCold; Emit; fixIO′)

private
  infixl 1 _>>_
  _>>_ : ∀ {A : Set} → IO ⊤ → IO A → IO A
  m >> n = m >>= λ _ → n

  unless : IORef Bool → IO ⊤ → IO ⊤
  unless r m = readIORef r >>= λ b → if b then pure tt else m

record Clock : Set where
  field
    now    : IORef Time
    timers : IORef (List (Time × IO ⊤))

newClock : IO Clock
newClock = newIORef 0 >>= λ n → newIORef [] >>= λ ts → pure (record { now = n ; timers = ts })

private
  -- After every timer due no later.
  insert : Time → IO ⊤ → List (Time × IO ⊤) → List (Time × IO ⊤)
  insert d a []              = (d , a) ∷ []
  insert d a ((e , b) ∷ ts) = if e ≤ᵇ d then (e , b) ∷ insert d a ts else (d , a) ∷ (e , b) ∷ ts

after : Clock → ℕ → IO ⊤ → IO ⊤
after ck d a = readIORef (Clock.now ck) >>= λ t → readIORef (Clock.timers ck) >>= λ ts →
               writeIORef (Clock.timers ck) (insert (t + d) a ts)

-- Every timer, earliest first, the clock set to each as it fires, until
-- none is left.
fire : Clock → IO ⊤
fire ck = fixIO′ (λ again _ → readIORef (Clock.timers ck) >>= λ where
  []             → pure tt
  ((t , a) ∷ ts) → writeIORef (Clock.timers ck) ts >> writeIORef (Clock.now ck) t >> a >> again tt) tt

------------------------------------------------------------------------
-- A timeline, played

-- Frame 0 inline, then each later frame on a timer set where the burst
-- before it ends.  A closed subscriber or a teardown stops the playing.
-- IO knows no positions, so a `fresh` leaf's name is drawn from `names`,
-- a supply shared by the run: a position no other draw returns, which is
-- all a name is read for.
fromTimeline : ∀ {A} → Clock → IORef ℕ → Timeline A → IOCold A
fromTimeline {A} ck names c = record
  { Internal = IORef Bool
  ; create   = λ e → record
      { subscription = newIORef false >>= λ off → named c >>= λ q → first e off (timelineAt c q) >> pure off
      ; teardown     = λ off → writeIORef off true }
  }
  where
    -- `self` plays the frames after this burst.
    burst : Emit A → IORef Bool → (∀ t → From A (suc t) → IO ⊤) → ∀ t → Frame A t → IO ⊤
    burst e off self t = fixIO′ λ next′ b → Emit.closed e >>= λ c → if c then pure tt else step next′ b
      where
        step : (Frame A t → IO ⊤) → Frame A t → IO ⊤
        step next′ (emit a k) = Emit.produce e a >> unless off (next′ k)
        step next′ (stall k)  = next′ (Frame∞.force k)
        step next′ (close k)  = self t (From∞.force k)

    play : Emit A → IORef Bool → Time → ∀ {u} → From A u → IO ⊤
    play e off now m = fixIO′ step (now , _ , m)
      where
        step : (Time × Σ Time (From A) → IO ⊤) → Time × Σ Time (From A) → IO ⊤
        step self (now , _ , done)     = Emit.complete e
        step self (now , _ , quiet)    = pure tt
        step self (now , _ , at t _ b) = after ck (t ∸ now) (unless off (burst e off (λ t′ m′ → self (t′ , suc t′ , m′)) t b))

    named : Timeline A → IO Pos
    named (fixed _) = pure []
    named fresh     = readIORef names >>= λ n → writeIORef names (suc n) >> pure (ix n ∷ [])

    first : Emit A → IORef Bool → From A 0 → IO ⊤
    first e off (at 0 _ b) = burst e off (λ t′ m′ → play e off t′ m′) 0 b
    first e off m        = play e off 0 m
