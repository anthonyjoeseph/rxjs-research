{-# OPTIONS --guardedness #-}

-- THE PURE RUNTIME OVER `operation.AbstractObservable`.  A cold leaf keeps
-- the frame it plays — the cascade it sits in, its next index — or the
-- completion it owes; that is its mark's key.  A frame's later frames
-- are the same leaf, rekeyed under the timer cascade `Unfold` places them
-- in.  So the driver keeps nothing: no clock, no timers, no turns, no
-- depths.  The run's time is the tick of the position it is at.
module operation.PureObservable where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline; timelineAt; ML; Burst; Burst∞; ML∞; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Pos; ix; last; tick) renaming (sub to subᴾ)
open import operation.Key using (Key) renaming (at to atᴷ)

------------------------------------------------------------------------
-- Observing a run

-- `R` is the type the root observes.
module Pure (R : Set) where
  -- How the record of a run ends.
  data End : Set where
    finished : End
    dry      : End
    cutOff   : Time → End

  stalls : ∀ {A} → Burst∞ A
  stalls .Burst∞.force = stall stalls

  ending : ∀ {A} → End → ML A
  ending finished   = done
  ending dry        = quiet
  ending (cutOff t) = at t (stall stalls)

  sameFrame : ∀ {A} → Bool → Burst A → Burst A → Burst A
  sameFrame true  b _ = b
  sameFrame false _ c = c

  mutual
    -- The record, from a frame at tick t whose values so far are out.
    frames : ∀ {A} → List (Time × A) → End → ML A
    frames []             e = ending e
    frames ((t , a) ∷ xs) e = at t (emit a (within t xs e))

    within : ∀ {A} → Time → List (Time × A) → End → Burst∞ A
    within t xs e .Burst∞.force = inFrame t xs e

    inFrame : ∀ {A} → Time → List (Time × A) → End → Burst A
    inFrame t []               (cutOff c) = sameFrame (c ≡ᵇ t) (stall stalls) (close (later (ending (cutOff c))))
    inFrame t []               e          = close (later (ending e))
    inFrame t ((t′ , a) ∷ xs) e          = sameFrame (t′ ≡ᵇ t) (emit a (within t xs e)) (close (later (frames ((t′ , a) ∷ xs) e)))

    later : ∀ {A} → ML A → ML∞ A
    later m .ML∞.force = m

-- What a started cold keeps: the frame it plays, from the tick it was
-- subscribed at, in cascade `u`, its next index; the completion it owes
-- at a position; or nothing more.
data Tape (A : Set) : Set₁ where
  play   : Time → Pos → ℕ → (t : Time) → Frame A t → Tape A
  ending : Pos → Tape A
  over   : Tape A

due : ∀ {A} → Tape A → Maybe Key
due (play τ u i t fr) = just (atᴷ (u ++ [ ix i ]))
due (ending e)        = just (atᴷ e)
due over              = nothing

-- What it shows when due: a frame's value or its end; a stall or a
-- frame's close shows nothing.
peek : ∀ {A} → Tape A → Maybe (Maybe A)
peek (play τ u i t (emit a k)) = just (just a)
peek (play τ u i t _)          = nothing
peek (ending e)                = just nothing
peek over                      = nothing

-- After a frame ending at `e`: a completion owed, nothing, or the next
-- frame, under a cascade at its tick.
rest : ∀ {A t} → Time → Pos → From A t → Tape A
rest τ e done        = ending e
rest τ e quiet       = over
rest τ e (at t _ fr) = play τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 t fr

-- A timeline subscribed at `p`: frame 0 played in place, or its frames
-- after it.
opening : ∀ {A} → Pos → From A 0 → Tape A
opening p (at zero _ b) = play (tick p) p 0 0 b
opening p m             = rest (tick p) (p ++ [ last ]) m

-- A program the pure runtime runs: colds are timelines.
PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

import operation.AbstractObservable
module Machine = operation.AbstractObservable Timeline Tape due peek
open Machine using (Conf; Stepped; moved; starting; turn; quiet; load; Poke; gone; leaf; nx; cp)
  renaming (step to stepᴹ)

module Driver (R : Set) where
  open Pure R using (End; finished; cutOff; frames) renaming (dry to dryᴱ)

  data Step : Set₁ where
    silent   : Time → Conf R → Step
    value    : Time → Pos → R → Conf R → Step
    complete : Pos → Step
    drained  : Step

  -- A leaf's turn: a completion owed is delivered; a leaf gone, torn
  -- down or closed stops; else its frame's next value delivered, a stall
  -- skipped, a close rekeying it to its next frame.
  played : Poke R → Step
  played gone = drained
  played (leaf b (ending e) cl dv st) = silent (tick e) (dv cp over false e)
  played (leaf false l cl dv st) = silent 0 (st over)
  played (leaf true l true dv st) = silent 0 (st over)
  played (leaf true (play τ u i t (emit a k)) false dv st) =
    silent (tick u) (dv (nx a) (play τ u (suc i) t (Frame∞.force k)) true (u ++ [ ix i ]))
  played (leaf true (play τ u i t (stall k)) false dv st) = silent (tick u) (st (play τ u (suc i) t (Frame∞.force k)))
  played (leaf true (play τ u i t (close k)) false dv st) = silent (tick u) (st (rest τ (u ++ [ last ]) (From∞.force k)))
  played (leaf true over false dv st) = silent 0 (st over)

  took : Stepped R → Step
  took (moved c ((p , nx a) ∷ _) _) = value (tick p) p a c
  took (moved c ((p , cp) ∷ _) _)   = complete p
  took (moved c [] _)               = silent (tick (Conf.pos c)) c
  took (starting x p k)             = silent (tick p) (k (opening p (timelineAt x p)))
  took (turn pk)                    = played pk
  took quiet                        = drained

  step : Conf R → Step
  step c = took (stepᴹ c)

  ------------------------------------------------------------------------
  -- The run

  mutual
    -- Each step's clock on its silent steps, so a reader cut there knows
    -- the time.
    data Trace : Set where
      tau  : Time → Trace∞ → Trace
      out  : Time → Pos → R → Trace∞ → Trace
      end  : Pos → Trace
      idle : Trace

    record Trace∞ : Set where
      coinductive
      field force : Trace

  open Trace∞

  mutual
    trace : Conf R → Trace
    trace m = shown (step m)

    shown : Step → Trace
    shown (silent t m)    = tau t λ where .force → trace m
    shown (value t p a m) = out t p a λ where .force → trace m
    shown (complete p)    = end p
    shown drained         = idle

  ------------------------------------------------------------------------
  -- The run, read as `operation.PureObservable` reads its own

  record Read : Set where
    constructor read
    field
      marks   : List Pos
      log     : List (Time × R)
      endedAs : End

  noted : Pos → Time × R → Read → Read
  noted p x r = read (p ∷ Read.marks r) (x ∷ Read.log r) (Read.endedAs r)

  later : Time → Time → Time
  later c t = if c <ᵇ t then t else c

  -- `c` the last time seen; a step past the horizon cuts the run there.
  reading : Time → ℕ → Time → Conf R → Read
  reading h zero    c k = read [] [] (cutOff c)
  reading h (suc n) c k with step k
  ... | silent t k′    = if h <ᵇ t then read [] [] (cutOff c) else reading h n (later c t) k′
  ... | value t p a k′ = if h <ᵇ t then read [] [] (cutOff c) else noted p (t , a) (reading h n t k′)
  ... | complete p     = read [ p ] [] finished
  ... | drained        = read [] [] dryᴱ

  prefix : ℕ → Time → PureObs [] R → ML R
  prefix n h o = frames (Read.log r) (Read.endedAs r)
    where r = reading h n 0 (load o)

-- THE PURE SEMANTICS: a program's first n steps up to tick h.
run : ∀ {R} → ℕ → Time → PureObs [] R → ML R
run {R} = Driver.prefix R
