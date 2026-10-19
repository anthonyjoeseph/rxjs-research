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
open import Data.List.Relation.Unary.All using ([])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (lower)

open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; PureObs; Out; note; fin; module Pure)
open import denotation.MonotonicList.Events using (ML; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last)

module Machine (R : Set) where
  open Heap using (World; _⊑_; _∋_; wk∋; Sink; Handle; same)
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
      sink   : Sink h A
      handle : Handle h
      at′    : Time
      under′ : Pos
      index  : ℕ
      frame  : Frame A at′
      polled : Bool

  wkPlaying : ∀ {h v} → h ⊑ v → Playing h → Playing v
  wkPlaying ρ b = record { sink = wk∋ ρ (Playing.sink b) ; handle = wk∋ ρ (Playing.handle b) ; at′ = Playing.at′ b
                         ; under′ = Playing.under′ b ; index = Playing.index b ; frame = Playing.frame b ; polled = Playing.polled b }

  -- What the driver owes the machine at its next turn: a resume, or a
  -- timeline's completion.
  data Todo (h : World) : Set₁ where
    resume : Todo h
    owing  : ∀ {A} → Handle h → Sink h A → Pos → Todo h

  wkTodo : ∀ {h v} → h ⊑ v → Todo h → Todo v
  wkTodo ρ resume          = resume
  wkTodo ρ (owing hd s e) = owing (wk∋ ρ hd) (wk∋ ρ s) e

  -- The shared configuration, with the clock, the timers, the bursts
  -- being played (innermost first) and the root's record.
  record Mach : Set₁ where
    constructor mach
    field
      conf   : Conf
      clock  : ℕ
      timers : List (Timer (Conf.world conf))
      bursts : List (Maybe (Playing (Conf.world conf)))   -- `nothing`: a burst over, the machine to resume
      todo   : List (Todo (Conf.world conf))              -- what to feed at the driver's next turn
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

  -- A transition taken: the driver's state carried into the grown world.
  moved : (m : Mach) → Next (Conf.world (Mach.conf m)) → Mach
  moved m (next c ρ _) = record m { conf = c ; timers = mapList (wkTimer ρ) (Mach.timers m)
                                  ; bursts = mapList (mapMaybe (wkPlaying ρ)) (Mach.bursts m) ; todo = mapList (wkTodo ρ) (Mach.todo m) }

  owe : (m : Mach) → Todo (Conf.world (Mach.conf m)) → Mach
  owe m t = record m { todo = Mach.todo m ++ [ t ] }

  -- The frames after one ending, at position e: a completion owed,
  -- nothing, or a timer for the next.  The burst over, the machine is
  -- owed a resume.
  schedule : (m : Mach) → ∀ {A u} → Sink (Conf.world (Mach.conf m)) A → Handle (Conf.world (Mach.conf m)) → Time → Pos → From A u → Mach
  schedule m s hd now e done        = owe (record m { bursts = nothing ∷ Mach.bursts m }) (owing hd s e)
  schedule m s hd now e quiet       = owe m resume
  schedule m s hd now e (at t _ fr) = owe (record m { timers = insert (record { due = Mach.clock m + (t ∸ now) ; sink = s ; handle = hd
                                                                            ; at′ = t ; from = e ; frame = fr })
                                                                  (Mach.timers m) }) resume

  -- A timeline just started: frame 0 played now, or its frames scheduled.
  starting : (m : Mach) → ∀ {A} → Sink (Conf.world (Mach.conf m)) A → Handle (Conf.world (Mach.conf m)) → From A 0 → Mach
  starting m s hd (at zero _ b) = record m { bursts = just (record { sink = s ; handle = hd ; at′ = 0 ; under′ = pos m ; index = 0 ; frame = b ; polled = false })
                                                      ∷ Mach.bursts m }
  starting m s hd f             = schedule m s hd 0 (pos m ++ [ last ]) f

  -- What the machine asked: a started timeline pushed to be played; a
  -- poll's answer, closed ending the burst; a teardown nothing, the heap
  -- holding it spent.  An effect waits in `asking` for `step`.
  asked : (m : Mach) → List (Output (Conf.world (Mach.conf m))) → Mach
  asked m (start c s hd ∷ _)  = starting m s hd (lower c)
  asked m (closedIs true ∷ _) with Mach.bursts m
  ... | _ ∷ bs = owe (record m { bursts = bs }) resume
  ... | []     = m
  asked m _                   = m

  -- Feed the machine one input, and answer what it asks: one transition.
  -- A world that did not grow carries the driver's state as it is, so a
  -- run of silent steps stacks no weakenings on the timers.
  fed′ : (m : Mach) → Next (Conf.world (Mach.conf m)) → Mach
  fed′ m (next ⟨ hp , p , c ⟩ same os) = asked (record m { conf = ⟨ hp , p , c ⟩ }) os
  fed′ m n                             = asked (moved m n) (Next.outputs n)

  feed : (m : Mach) → Input (Mach.conf m) → Mach
  feed m i = fed′ m (transition (Mach.conf m) i)

  -- A burst's step, its sink read open: the next frame's value
  -- delivered at its position, a stall skipped, a close scheduling the
  -- rest.
  play : (m : Mach) → Playing (Conf.world (Mach.conf m)) → List (Maybe (Playing (Conf.world (Mach.conf m)))) → Mach
  play m b bs with Playing.frame b
  ... | emit a k′ = feed (record m { bursts = just (record b { index = suc (Playing.index b) ; frame = Frame∞.force k′ ; polled = false }) ∷ bs })
                         (deliver (Playing.sink b) a (Playing.under′ b ++ [ ix (Playing.index b) ]))
  ... | stall k′  = record m { bursts = just (record b { index = suc (Playing.index b) ; frame = Frame∞.force k′ }) ∷ bs }
  ... | close k′  = schedule (record m { bursts = bs }) (Playing.sink b) (Playing.handle b) (Playing.at′ b) (Playing.under′ b ++ [ last ]) (From∞.force k′)

  -- What is owed, fed.
  paid : (m : Mach) → Todo (Conf.world (Mach.conf m)) → Input (Mach.conf m)
  paid m resume          = go
  paid m (owing hd s e) = end hd s e

  -- The driver's turn, nothing owed: a burst played, or a timer popped.
  turned : (m : Mach) → List (Maybe (Playing (Conf.world (Mach.conf m)))) → Step
  turned m (nothing ∷ bs) = silent (feed (record m { bursts = bs }) go)
  turned m (just b ∷ bs) =
    if spent? (Conf.heap (Mach.conf m)) (Playing.handle b) then silent (feed (record m { bursts = bs }) go)
    else if Playing.polled b then silent (play m b bs)
    else silent (feed (record m { bursts = just (record b { polled = true }) ∷ bs }) (poll (Playing.sink b)))
  turned m [] with Mach.timers m
  ... | []      = drained
  ... | tm ∷ ts = silent (record m { clock = Timer.due tm ; timers = ts
                                   ; bursts = just (record { sink = Timer.sink tm ; handle = Timer.handle tm ; at′ = Timer.at′ tm
                                                           ; under′ = cascade tm ; index = 0 ; frame = Timer.frame tm ; polled = false }) ∷ [] })

  -- The record's effect answered.
  answer′ : ∀ {c h hp p w B k σ s} {e : Out R ⊤} → c ≡ ⟨_,_,_⟩ {h} hp p (asking {w = w} {B = B} e k σ s) → Input c
  answer′ refl = answer tt

  step : Mach → Step
  step m with Mach.conf m in eq
  -- The record's effects: a value shown unless the root has completed.
  ... | ⟨ hp , p , asking (note a) k σ s ⟩ with Mach.ended m
  ...   | true  = silent (feed m (answer′ eq))
  ...   | false = value (Mach.clock m) p a (feed (record m { log = Mach.log m ++ [ (Mach.clock m , a) ] ; marks = Mach.marks m ++ [ p ] }) (answer′ eq))
  step m | ⟨ hp , p , asking fin k σ s ⟩ with Mach.ended m
  ...   | true  = silent (feed m (answer′ eq))
  ...   | false = complete p
  -- The machine running: one transition.
  step m | ⟨ _ , _ , run _ _ _ ⟩ = silent (feed m go)
  step m | ⟨ _ , _ , ret _ _ _ ⟩ = silent (feed m go)
  -- Held: what is owed first, then the turn.
  step m | ⟨ _ , _ , held _ _ ⟩ with Mach.todo m
  ... | t ∷ ts = silent (feed (record m { todo = ts }) (paid m t))
  ... | []     = turned m (Mach.bursts m)

  -- Subscribing at the root, then the loop.
  launch : ∀ {A} → Subscribe A [] → Observer A [] → Mach
  launch s o = mach (load s o) 0 [] [] [] [] false []

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
