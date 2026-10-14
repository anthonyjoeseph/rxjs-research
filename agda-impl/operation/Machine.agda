{-# OPTIONS --guardedness --large-indices #-}

-- THE SMALL-STEP ENGINE.  The pure runtime as a machine over first-order
-- configurations: the state, what runs next, and an explicit stack of
-- what waits on its result.  `step` takes one step by structural
-- recursion, an `Act` constructor or a frame of a cold's burst, and
-- `trace` repeats it, guarded by the step: a run is a coinductive
-- stream with a silent step wherever work is done.  So there is no
-- burst budget, no callback depth and no loop turn to count, and a
-- `defer` is compiled when the run reaches it.
--
-- The heap, the timers and the record are `PureObservable`'s, and each
-- step does what its clause of the pure monad does: a callback run
-- pushes what follows it, a burst checks its cold spent and its
-- subscriber closed before each step, a turn pops the earliest timer.
module operation.Machine where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Level using (lift; lower)

open import Tree using (Later)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (World; _⊑_; same; _⨾_; new; wk∋; Sink; Handle; Pureᴾ; PureObs; Out; note; fin; module Pure)
  renaming (here to top)
open import denotation.MonotonicList using (ML; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last)

module Machine (R : Set) where
  open Run (Pureᴾ R) using (Act; newRef; readRef; writeRef; register; send; finish; startCold; stop; eff; here; goto; diverge; unfold;
    Observer; Subscription; Subscribe; Env; compile; wkAct; wkEl)
  open Run (Pureᴾ R) using () renaming (done to doneᴬ)
  open Pure R using (State; Callbacks; get; put; extend; Timer; insert; cascade; recorder; start; End; finished; cutOff; frames)
  open Pure R using () renaming (dry to dryᴱ)

  ------------------------------------------------------------------------
  -- Configurations

  -- What waits on a result of type X, made in world w: the rest of an
  -- `Act`; a burst asking its subscriber whether it is closed; a burst
  -- whose emit is being delivered.  Y is what it hands on.
  data Wait (w : World) : Set → Set → Set₁ where
    rest   : ∀ {B} → Act w B → Wait w ⊤ B
    asked  : ∀ {A u} → Sink w A → Handle w → Time → Pos → ℕ → Frame A u → Wait w Bool ⊤
    sent   : ∀ {A u} → Sink w A → Handle w → Time → Pos → ℕ → Frame A u → Wait w ⊤ ⊤

  -- Each frame made in its own world, linked to the one below it by how
  -- that world grew.  The bottom is the loop's next turn.
  data Stack : World → Set → Set₁ where
    loop : ∀ {w} → Stack w ⊤
    push : ∀ {u w X Y} → Wait w X Y → u ⊑ w → Stack u Y → Stack w X

  -- What runs next in world h, its result going to a stack made at w.
  -- A burst stands before its step: its cold is checked spent, then its
  -- subscriber asked whether it is closed.
  data Ctl (h : World) : Set₁ where
    run   : ∀ {w B} → Act h B → w ⊑ h → Stack w B → Ctl h
    ret   : ∀ {w X} → X → w ⊑ h → Stack w X → Ctl h
    burst : ∀ {w A u} → Sink h A → Handle h → Time → Pos → ℕ → Frame A u → w ⊑ h → Stack w ⊤ → Ctl h
    turn  : Ctl h

  record Mach : Set₁ where
    constructor ⟨_,_⟩
    field
      {world} : World
      state   : State world
      ctl     : Ctl world

  ------------------------------------------------------------------------
  -- One step

  -- What a step shows: nothing, a value recorded at the clock and the
  -- position the state stands at, the root's completion, or a queue run dry.
  data Step : Set₁ where
    silent   : Mach → Step
    value    : Time → Pos → R → Mach → Step
    complete : Pos → Step
    drained  : Step

  spent? : ∀ {h} → State h → Handle h → Bool
  spent? st hd = lower (get (State.heap st) hd)

  cbs : ∀ {h A} → State h → Sink h A → Callbacks A h
  cbs st s = get (State.heap st) s

  -- The frames after one ending at tick `now`, at position e.
  schedule : ∀ {h w A u} → State h → Sink h A → Handle h → Time → Pos → From A u → w ⊑ h → Stack w ⊤ → Mach
  schedule st s hd now e done σ k =
    if spent? st hd then ⟨ st , ret tt σ k ⟩
    else ⟨ record st { heap = put (State.heap st) hd (lift true) ; pos = e } , run (Callbacks.onComplete (cbs st s)) σ k ⟩
  schedule st s hd now e quiet σ k = ⟨ st , ret tt σ k ⟩
  schedule st s hd now e (at t _ b) σ k =
    ⟨ record st { timers = insert (record { due = State.clock st + (t ∸ now) ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b })
                                  (State.timers st) }
    , ret tt σ k ⟩

  -- A burst's step, its subscriber read open.
  play : ∀ {h w A u} → State h → Sink h A → Handle h → Time → Pos → ℕ → Frame A u → w ⊑ h → Stack w ⊤ → Mach
  play st s hd t r i (emit a k′) σ k =
    if spent? st hd then ⟨ st , ret tt σ k ⟩
    else ⟨ record st { pos = r ++ [ ix i ] } , run (Callbacks.onNext (cbs st s) a) same (push (sent s hd t r (suc i) (Frame∞.force k′)) σ k) ⟩
  play st s hd t r i (stall k′) σ k = ⟨ st , burst s hd t r (suc i) (Frame∞.force k′) σ k ⟩
  play st s hd t r i (close k′) σ k = schedule st s hd t (r ++ [ last ]) (From∞.force k′) σ k

  -- A cold just started: frame 0 delivered inline, or its frames scheduled.
  first : ∀ {h w A} → State h → Sink h A → Handle h → From A 0 → w ⊑ h → Stack w ⊤ → Mach
  first st s hd (at zero _ b) σ k = ⟨ st , burst s hd 0 (State.pos st) 0 b σ k ⟩
  first st s hd m             σ k = schedule st s hd 0 (State.pos st ++ [ last ]) m σ k

  -- A `defer` reached: its body compiled one level down, as `deferᴰ`
  -- puts it, its subscription's unsubscribe a registered sink.
  unfolded : ∀ {h Γ A} → Later Timeline Γ A → Env Γ h → (A → Act h ⊤) → Act h ⊤ → Act h Bool → (∀ {v} → h ⊑ v → Sink v ⊤ → Act v ⊤) → Act h ⊤
  unfolded l e n c x k = here λ p → goto (p ++ [ ix 1 ])
    (compile (Later.force l) e same (record { next = n ; complete = c ; closed = x }) λ σ sub →
      register (λ _ → Subscription.unsubscribe sub) (doneᴬ tt) (doneᴬ false) λ τ sk → k (σ ⨾ τ) sk)

  -- The record's effects: a value shown unless the root has completed.
  effect : ∀ {h w B X} → State h → Out R X → (X → Act h B) → w ⊑ h → Stack w B → Step
  effect st (note a) k σ m with State.ended st
  ... | true  = silent ⟨ st , run (k tt) σ m ⟩
  ... | false = value (State.clock st) (State.pos st) a
                  ⟨ record st { log = State.log st ++ [ (State.clock st , a) ] ; marks = State.marks st ++ [ State.pos st ] } , run (k tt) σ m ⟩
  effect st fin k σ m with State.ended st
  ... | true  = silent ⟨ st , run (k tt) σ m ⟩
  ... | false = complete (State.pos st)

  runs : ∀ {h w B} → State h → Act h B → w ⊑ h → Stack w B → Step
  runs st (doneᴬ b)          σ k = silent ⟨ st , ret b σ k ⟩
  runs st (newRef t a k′)    σ k = silent ⟨ extend st (lift (wkEl t new a)) , run (k′ new top) (σ ⨾ new) k ⟩
  runs st (readRef r k′)     σ k = silent ⟨ st , run (k′ same (lower (get (State.heap st) r))) σ k ⟩
  runs st (writeRef r a k′)  σ k = silent ⟨ record st { heap = put (State.heap st) r (lift a) } , run k′ σ k ⟩
  runs st (register n c x k′) σ k = silent ⟨ extend st (record { onNext = λ a → wkAct new (n a) ; onComplete = wkAct new c ; isClosed = wkAct new x })
                                          , run (k′ new top) (σ ⨾ new) k ⟩
  runs st (send s a k′)      σ k = silent ⟨ st , run (Callbacks.onNext (cbs st s) a) same (push (rest k′) σ k) ⟩
  runs st (finish s k′)      σ k = silent ⟨ st , run (Callbacks.onComplete (cbs st s)) same (push (rest k′) σ k) ⟩
  runs st (startCold c s k′) σ k = silent (first (extend st (lift false)) (wk∋ new s) top (lower c) same (push (rest (k′ new top)) (σ ⨾ new) k))
  runs st (stop hd k′)       σ k = silent ⟨ record st { heap = put (State.heap st) hd (lift true) } , run k′ σ k ⟩
  runs st (eff e k′)         σ k = effect st e k′ σ k
  runs st (here k′)          σ k = silent ⟨ st , run (k′ (State.pos st)) σ k ⟩
  runs st (goto p k′)        σ k = silent ⟨ record st { pos = p } , run k′ σ k ⟩
  runs st diverge            σ k = silent ⟨ st , run diverge σ k ⟩
  runs st (unfold l e n c x k′ m) σ k = silent ⟨ st , run (unfolded l e n c x k′) same (push (rest m) σ k) ⟩

  returns : ∀ {h w X} → State h → X → w ⊑ h → Stack w X → Step
  returns st x σ loop                             = silent ⟨ st , turn ⟩
  returns st x σ (push (rest m) ρ k)              = silent ⟨ st , run (wkAct σ m) (ρ ⨾ σ) k ⟩
  returns st c σ (push (asked s hd t r i b) ρ k)  =
    silent (if c then ⟨ st , ret tt (ρ ⨾ σ) k ⟩ else play st (wk∋ σ s) (wk∋ σ hd) t r i b (ρ ⨾ σ) k)
  returns st x σ (push (sent s hd t r i b) ρ k)   = silent ⟨ st , burst (wk∋ σ s) (wk∋ σ hd) t r i b (ρ ⨾ σ) k ⟩

  step : Mach → Step
  step ⟨ st , run a σ k ⟩ = runs st a σ k
  step ⟨ st , ret x σ k ⟩ = returns st x σ k
  step ⟨ st , burst s hd t r i b σ k ⟩ =
    silent (if spent? st hd then ⟨ st , ret tt σ k ⟩
            else ⟨ st , run (Callbacks.isClosed (cbs st s)) same (push (asked s hd t r i b) σ k) ⟩)
  step ⟨ st , turn ⟩ with State.timers st
  ... | []      = drained
  ... | tm ∷ ts = silent ⟨ record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
                         , burst (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same loop ⟩

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
    shown (silent m)      = tau (State.clock (Mach.state m)) λ where .force → trace m
    shown (value t p a m) = out t p a λ where .force → trace m
    shown (complete p)    = end p
    shown drained         = idle

  -- Subscribing at the root, then the loop.
  launch : ∀ {A} → Subscribe A [] → Observer A [] → Mach
  launch s o = ⟨ start , run (s same o λ _ _ → doneᴬ tt) same loop ⟩

  begin : PureObs [] R → Mach
  begin o = launch (compile o []) recorder

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
