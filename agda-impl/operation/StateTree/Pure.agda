{-# OPTIONS --guardedness #-}

-- THE PURE DRIVER OF THE STATE-TREE MACHINE.  `operation.StateTree`'s
-- machine, fed on a virtual clock: every transition is the shared one,
-- and what this module adds is only what the pure runtime does at a
-- cold — its timeline, read at the position it was subscribed at, played
-- into its leaf a frame at a time, its later frames on timers.
--
-- A leaf keeps its own TAPE: the frame it is playing or waiting for, at
-- its tick on the cold's own timeline.  So what the driver keeps is
-- untyped — paths, positions, ticks — and every value it delivers comes
-- out of the leaf it goes into.
--
-- A frame is played at the depth of the job stack it was started or
-- fired at: the jobs a delivery owes are run before the next value, as
-- the value's cascade would run them inside rxjs's `next`.
module operation.StateTree.Pure where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline; timelineAt; ML; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Pos; ix; last) renaming (sub to subᴾ)
open import operation.PureObservable using (module Pure)

-- What a started cold keeps: the frame due at tick `t` of its own
-- timeline, or nothing more.
data Tape (A : Set) : Set₁ where
  tape : ∀ t → Frame A t → Tape A
  over : Tape A

import operation.StateTree
module Machine = operation.StateTree Timeline Tape
open Machine using (Conf; Stepped; moved; starting; load; Poke; gone; leaf; poke; spot; calm; depth; nx; cp)
  renaming (step to stepᴹ)

module Driver (R : Set) where
  open Pure R using (End; finished; cutOff; frames) renaming (dry to dryᴱ)

  ------------------------------------------------------------------------
  -- The driver's state

  -- A frame being played: the leaf, by its path; where the frame sits;
  -- its next value's index; whether its observer has been asked if it is
  -- closed; the depth it plays at.  Or a completion owed the leaf, at its
  -- position, at a depth.
  data Turn : Set where
    play   : List ℕ → Pos → ℕ → Bool → ℕ → Turn
    finish : List ℕ → Pos → ℕ → Turn

  depthOf : Turn → ℕ
  depthOf (play _ _ _ _ d) = d
  depthOf (finish _ _ d)   = d

  -- A frame due on the clock, for the leaf at `path`; `from` is the
  -- position the timer was set at, which places the frame.
  record Timer : Set where
    constructor timer
    field
      due  : ℕ
      path : List ℕ
      from : Pos

  -- A frame set at e, due at t, is a cascade rooted at ix t ∷ subᴾ e ∷ [].
  cascade : Timer → Pos
  cascade tm = ix (Timer.due tm) ∷ subᴾ (Timer.from tm) ∷ []

  -- After every timer due no later: two timers due together fire in the
  -- order they were set.
  insert : Timer → List Timer → List Timer
  insert tm []        = tm ∷ []
  insert tm (t′ ∷ ts) = if Timer.due t′ ≤ᵇ Timer.due tm then t′ ∷ insert tm ts else tm ∷ t′ ∷ ts

  record Mach : Set₁ where
    constructor mach
    field
      conf   : Conf R
      clock  : ℕ
      timers : List Timer
      turns  : List Turn       -- innermost first

  ------------------------------------------------------------------------
  -- One step

  -- What a step shows: nothing, a value recorded at the clock and the
  -- position it was made at, the root's completion, or nothing left.
  data Step : Set₁ where
    silent   : Mach → Step
    value    : Time → Pos → R → Mach → Step
    complete : Pos → Step
    drained  : Step

  -- The frames after one ending at `now`, at position e: a completion
  -- owed, nothing, or a timer for the next.  `k` puts the leaf's tape.
  rest : Mach → ∀ {A u} → Time → Pos → From A u → (Tape A → Conf R) → Mach
  rest m now e done        k = let c = k over in record m { conf = c ; turns = finish (spot c) e (depth c) ∷ Mach.turns m }
  rest m now e quiet       k = record m { conf = k over }
  rest m now e (at t _ fr) k = let c = k (tape t fr) in
    record m { conf = c ; timers = insert (timer (Mach.clock m + (t ∸ now)) (spot c) e) (Mach.timers m) }

  -- A timeline just started at p: frame 0 played now, or its frames
  -- scheduled.
  opening : Mach → ∀ {A} → Pos → From A 0 → (Tape A → Conf R) → Mach
  opening m p (at zero _ b) k = let c = k (tape 0 b) in record m { conf = c ; turns = play (spot c) p 0 false (depth c) ∷ Mach.turns m }
  opening m p f             k = rest m 0 (p ++ [ last ]) f k

  -- What the machine did, taken in.
  took : Mach → Stepped R → Step
  took m (moved c ((p , nx a) ∷ _) _) = value (Mach.clock m) p a (record m { conf = c })
  took m (moved c ((p , cp) ∷ _) _)   = complete p
  took m (moved c [] _)               = silent (record m { conf = c })
  took m (starting x p k)             = silent (opening m p (timelineAt x p) k)

  -- A frame's step: a leaf gone, torn down or closed ends it; else its
  -- observer asked, then its next value delivered, a stall skipped, a
  -- close scheduling the rest.
  playing : Mach → List ℕ → Pos → ℕ → Bool → ℕ → List Turn → Poke R → Step
  playing m π u i pl     d ts gone                     = silent (record m { turns = ts })
  playing m π u i pl     d ts (leaf false l cl dv st)  = silent (record m { turns = ts })
  playing m π u i false  d ts (leaf true l true dv st)  = silent (record m { turns = ts })
  playing m π u i false  d ts (leaf true l false dv st) = silent (record m { turns = play π u i true d ∷ ts })
  playing m π u i true   d ts (leaf true (tape t (emit a k)) cl dv st) =
    silent (record m { conf = dv (nx a) (tape t (Frame∞.force k)) true (u ++ [ ix i ]) ; turns = play π u (suc i) false d ∷ ts })
  playing m π u i true   d ts (leaf true (tape t (stall k)) cl dv st) =
    silent (record m { conf = st (tape t (Frame∞.force k)) ; turns = play π u (suc i) true d ∷ ts })
  playing m π u i true   d ts (leaf true (tape t (close k)) cl dv st) =
    silent (rest (record m { turns = ts }) t (u ++ [ last ]) (From∞.force k) st)
  playing m π u i true   d ts (leaf true over cl dv st) = silent (record m { turns = ts })

  -- A completion owed: delivered under its position, the leaf spent.
  finishing : Mach → Pos → List Turn → Poke R → Step
  finishing m e ts gone                  = silent (record m { turns = ts })
  finishing m e ts (leaf b l cl dv st)   = silent (record m { conf = dv cp l false e ; turns = ts })

  played : Mach → Turn → List Turn → Step
  played m (play π u i pl d) ts = playing m π u i pl d ts (poke π (Mach.conf m))
  played m (finish π e d)    ts = finishing m e ts (poke π (Mach.conf m))

  -- Nothing running and nothing playing: the next timer fired.
  fire : Mach → List Timer → Step
  fire m []         = drained
  fire m (tm ∷ tms) = silent (record m { clock = Timer.due tm ; timers = tms ; turns = [ play (Timer.path tm) (cascade tm) 0 false 0 ] })

  -- The driver's turn: the jobs owed above the frame playing run first.
  turned : Mach → List Turn → Step
  turned m (t ∷ ts) = if depthOf t <ᵇ depth (Mach.conf m) then took m (stepᴹ (Mach.conf m)) else played m t ts
  turned m []       = if 0 <ᵇ depth (Mach.conf m) then took m (stepᴹ (Mach.conf m)) else fire m (Mach.timers m)

  step : Mach → Step
  step m = if calm (Mach.conf m) then turned m (Mach.turns m) else took m (stepᴹ (Mach.conf m))

  begin : Obs Timeline [] R → Mach
  begin o = mach (load o) 0 [] []

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
    trace : Mach → Trace
    trace m = shown (step m)

    shown : Step → Trace
    shown (silent m)      = tau (Mach.clock m) λ where .force → trace m
    shown (value t p a m) = out t p a λ where .force → trace m
    shown (complete p)    = end p
    shown drained         = idle

  -- What a reader of the first n steps has: each value at its clock, and
  -- how the run stood — cut at the last clock seen, complete, or dry.  A
  -- step past the horizon cuts it there: a looping program works forever,
  -- so it is read up to a time.
  record Read : Set where
    constructor read
    field
      log    : List (Time × R)
      ending : End
  open Read public

  reading : Time → ℕ → Time → Trace → Read
  reading h zero    c _             = read [] (cutOff c)
  reading h (suc n) c (tau t k)     = if h <ᵇ t then read [] (cutOff c) else reading h n t (force k)
  reading h (suc n) c (out t p a k) = if h <ᵇ t then read [] (cutOff c) else
    (let r = reading h n t (force k) in read ((t , a) ∷ log r) (ending r))
  reading h (suc n) c (end p)       = read [] finished
  reading h (suc n) c idle          = read [] dryᴱ

  -- The first n steps of a program's run, up to tick h, as a timeline.
  prefix : ℕ → Time → Obs Timeline [] R → ML R
  prefix n h o = frames (log r) (ending r)
    where r = reading h n 0 (trace (begin o))

-- THE PURE OPERATIONAL SEMANTICS: a program's first n steps up to tick h.
run : ∀ {R} → ℕ → Time → Obs Timeline [] R → ML R
run {R} = Driver.prefix R
