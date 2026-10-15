{-# OPTIONS --guardedness --large-indices #-}

-- THE PURE DRIVER.  `operation.AbstractObservable`'s machine, fed on a
-- virtual clock: every transition is the shared one, and what this
-- module adds is only what the pure runtime feeds it — each started
-- timeline played into its sink, a frame at a time, its later frames on
-- timers — and what it does with what the machine asks: the record's
-- effects answered at once.  `step` takes one step by structural
-- recursion and `trace` repeats it, guarded by the step: a run is a
-- coinductive stream with a silent step wherever work is done.
module operation.Machine where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Unit using (tt)
open import Level using (lower)

open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; PureObs; Out; note; fin; module Pure)
open import denotation.MonotonicList using (ML; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last)

module Machine (R : Set) where
  open Heap
  open Run (Pureᴾ R) using (Subscribe; Observer; compile)
  open Shared Timeline (Out R)
  open Pure R using (Timer; wkTimer; insert; cascade; mapList; recorder; End; finished; cutOff; frames)
  open Pure R using () renaming (dry to dryᴱ)

  ------------------------------------------------------------------------
  -- The driver's state

  -- A started timeline being played into its sink: its frame at tick t,
  -- placed under r, the next value the i-th.  `polled`: its sink has been
  -- asked whether it is closed, the answer not yet in.
  record Playing (h : World) : Set₁ where
    field
      {A}    : Set
      {u}    : Time
      sink   : Sink h A
      handle : Handle h
      at′    : Time
      under′ : Pos
      index  : ℕ
      frame  : Frame A at′
      polled : Bool

  wkPlaying : ∀ {h v} → h ⊑ v → Playing h → Playing v
  wkPlaying ρ b = record b { sink = wk∋ ρ (Playing.sink b) ; handle = wk∋ ρ (Playing.handle b) }

  -- The shared configuration, with the clock, the timers, the bursts
  -- being played (innermost first) and the root's record.
  record Mach : Set₁ where
    constructor mach
    field
      conf   : Conf
      clock  : ℕ
      timers : List (Timer (Conf.world conf))
      bursts : List (Maybe (Playing (Conf.world conf)))   -- `nothing`: a burst over, the machine to resume
      log    : List (Time × R)     -- the root's record
      ended  : Bool                -- whether the root has completed
      marks  : List Pos            -- where each entry of the record was made: a ghost

  pos : Mach → Pos
  pos m = Conf.pos (Mach.conf m)

  ------------------------------------------------------------------------
  -- One step

  -- What a step shows: nothing, a value recorded at the clock and the
  -- position it was made at, the root's completion, or a queue run dry.
  data Step : Set₁ where
    silent   : Mach → Step
    value    : Time → Pos → R → Mach → Step
    complete : Pos → Step
    drained  : Step

  -- A transition taken: the timers and bursts carried into the grown world.
  moved : (m : Mach) → Next (Conf.world (Mach.conf m)) → Mach
  moved m (next c ρ _) = record m { conf = c ; timers = mapList (wkTimer ρ) (Mach.timers m) ; bursts = mapList (mapMaybe (wkPlaying ρ)) (Mach.bursts m) }

  mutual
    -- Feed the machine one input, and answer what it asks.
    feed : (m : Mach) → Input (Mach.conf m) → Step
    feed m i = asked (moved m n) (Next.outputs n)
      where n = transition (Mach.conf m) i

    -- What the machine asked: a started timeline pushed to be played; a
    -- poll's answer, closed ending the burst; a teardown nothing, the heap
    -- holding it spent.  An effect waits in `asking` for `step`.
    asked : (m : Mach) → List (Output (Conf.world (Mach.conf m))) → Step
    asked m []                 = silent m
    asked m (start c s hd ∷ _) = starting m s hd (lower c)
    asked m (closedIs true ∷ _)  with Mach.bursts m
    ... | _ ∷ bs = feed (record m { bursts = bs }) go
    ... | []     = silent m
    asked m (closedIs false ∷ _) = silent m
    asked m (stopped hd ∷ _)     = silent m
    asked m (perform e ∷ _)      = silent m

    -- A burst's step, its sink read open: the next frame's value
    -- delivered at its position, a stall skipped, a close scheduling the
    -- rest.
    play : (m : Mach) → Playing (Conf.world (Mach.conf m)) → List (Maybe (Playing (Conf.world (Mach.conf m)))) → Step
    play m b bs with Playing.frame b
    ... | emit a k′ = feed (record m { bursts = just (record b { index = suc (Playing.index b) ; frame = Frame∞.force k′ ; polled = false }) ∷ bs })
                           (deliver (Playing.sink b) a (Playing.under′ b ++ [ ix (Playing.index b) ]))
    ... | stall k′  = silent (record m { bursts = just (record b { index = suc (Playing.index b) ; frame = Frame∞.force k′ }) ∷ bs })
    ... | close k′  = schedule (record m { bursts = bs }) (Playing.sink b) (Playing.handle b) (Playing.at′ b) (Playing.under′ b ++ [ last ]) (From∞.force k′)

    -- A timeline just started: frame 0 played now, or its frames scheduled.
    starting : (m : Mach) → ∀ {A} → Sink (Conf.world (Mach.conf m)) A → Handle (Conf.world (Mach.conf m)) → From A 0 → Step
    starting m s hd (at zero _ b) = silent (record m { bursts = just (record { sink = s ; handle = hd ; at′ = 0 ; under′ = pos m ; index = 0 ; frame = b ; polled = false })
                                                               ∷ Mach.bursts m })
    starting m s hd f             = schedule m s hd 0 (pos m ++ [ last ]) f

    -- The frames after one ending, at position e: a completion, nothing,
    -- or a timer for the next.  The burst over, the machine resumes.
    schedule : (m : Mach) → ∀ {A u} → Sink (Conf.world (Mach.conf m)) A → Handle (Conf.world (Mach.conf m)) → Time → Pos → From A u → Step
    schedule m s hd now e done        = feed (record m { bursts = nothing ∷ Mach.bursts m }) (end hd s e)
    schedule m s hd now e quiet       = feed m go
    schedule m s hd now e (at t _ fr) = feed (record m { timers = insert (record { due = Mach.clock m + (t ∸ now) ; sink = s ; handle = hd
                                                                                 ; at′ = t ; from = e ; frame = fr })
                                                                       (Mach.timers m) }) go

  -- An effect answered with no step of its own: the machine resumed.
  resumed : (m : Mach) → Input (Mach.conf m) → Mach
  resumed m i = moved m (transition (Mach.conf m) i)

  step : Mach → Step
  step m with Mach.conf m | Mach.bursts m
  -- The record's effects: a value shown unless the root has completed.
  ... | ⟨ hp , p , asking (note a) k σ s ⟩ | _ with Mach.ended m
  ...   | true  = feed m (answer tt)
  ...   | false = value (Mach.clock m) p a (resumed (record m { log = Mach.log m ++ [ (Mach.clock m , a) ] ; marks = Mach.marks m ++ [ p ] }) (answer tt))
  step m | ⟨ hp , p , asking fin k σ s ⟩ | _ with Mach.ended m
  ...   | true  = feed m (answer tt)
  ...   | false = complete p
  -- The machine running: one transition.
  step m | ⟨ _ , _ , run _ _ _ ⟩ | _ = feed m go
  step m | ⟨ _ , _ , ret _ _ _ ⟩ | _ = feed m go
  -- Held over a burst: spent, it is over; unpolled, its sink is asked
  -- whether it is closed; polled open, it plays.
  step m | ⟨ _ , _ , held _ _ ⟩ | nothing ∷ bs = feed (record m { bursts = bs }) go
  step m | ⟨ hp , _ , held _ _ ⟩ | just b ∷ bs =
    if spent? hp (Playing.handle b) then feed (record m { bursts = bs }) go
    else if Playing.polled b then play m b bs
    else feed (record m { bursts = just (record b { polled = true }) ∷ bs }) (poll (Playing.sink b))
  -- Held with nothing to play: the loop's turn, the earliest timer popped.
  step m | ⟨ _ , _ , held _ _ ⟩ | [] with Mach.timers m
  ... | []      = drained
  ... | tm ∷ ts = silent (record m { clock = Timer.due tm ; timers = ts
                                   ; bursts = just (record { sink = Timer.sink tm ; handle = Timer.handle tm ; at′ = Timer.at′ tm
                                                           ; under′ = cascade tm ; index = 0 ; frame = Timer.frame tm ; polled = false }) ∷ [] })

  -- Subscribing at the root, then the loop.
  launch : ∀ {A} → Subscribe A [] → Observer A [] → Mach
  launch s o = mach (load s o) 0 [] [] [] false []

  begin : PureObs [] R → Mach
  begin o = launch (compile o []) recorder

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

  -- What a reader of the first n steps has: where each value was shown,
  -- each value at its clock, and how the run stood — cut at the last clock
  -- seen, complete, or dry.  A completion is placed too.
  record Read : Set where
    constructor read
    field
      marks  : List Pos
      log    : List (Time × R)
      ending : End
  open Read

  noted : Pos → Time × R → Read → Read
  noted p x r = read (p ∷ marks r) (x ∷ log r) (ending r)

  -- THE TEST HARNESS'S FUEL, and the adequacy proof's approximants.
  reading : ℕ → Time → Trace → Read
  reading zero    c _             = read [] [] (cutOff c)
  reading (suc n) c (tau t k)     = reading n t (force k)
  reading (suc n) c (out t p a k) = noted p (t , a) (reading n t (force k))
  reading (suc n) c (end p)       = read [ p ] [] finished
  reading (suc n) c idle          = read [] [] dryᴱ

  -- The first n steps of a program's run, read as a timeline.
  prefix : ℕ → PureObs [] R → ML R
  prefix n o = frames (log r) (ending r)
    where r = reading n 0 (trace (begin o))
