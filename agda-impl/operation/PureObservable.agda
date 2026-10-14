{-# OPTIONS --guardedness --large-indices #-}

-- THE PURE RUNTIME.  The shared engine, run in a state monad over a heap
-- and a virtual clock.  A cold leaf is a timeline relative to its
-- subscribe time, so the program itself says when everything happens:
-- there is no separate schedule, and quantifying over programs covers
-- every ordering.
--
-- Recursion is closed by unfolding: approximant n compiles n nested
-- `defer`s, runs callbacks n deep, takes n turns of the loop and walks a
-- burst n steps, and past that shows nothing.  Every approximant is a
-- finite run; the program's meaning is their limit, as `Denote`'s is.
--
-- The heap is TYPED BY ITS WORLD: a list saying what each entry is, so
-- reading a cell returns its content at its own type with no cast.
-- `--large-indices` only because the world lists codes, which live in
-- `Set₁`, and a name is a position in it.
module operation.PureObservable where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)

open import Tree using (Obs; Later)
open import operation.AbstractObservable using (Ty; base; Prims; module Run)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Timeline)

------------------------------------------------------------------------
-- Worlds

-- What one heap entry is: a cell, a registered observer, a started cold.
data Kind : Set₁ where
  cell : Ty → Kind
  slot : Set → Kind
  play : Kind

World : Set₁
World = List Kind

-- A name: a position in the world, newest first.
data _∋_ : World → Kind → Set where
  here  : ∀ {k w} → (k ∷ w) ∋ k
  there : ∀ {j k w} → w ∋ k → (j ∷ w) ∋ k

-- A later world: this one, with entries made since.
data _⊑_ : World → World → Set where
  same : ∀ {w} → w ⊑ w
  grow : ∀ {k w v} → w ⊑ v → w ⊑ (k ∷ v)

infixr 5 _⨾_
_⨾_ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
ρ ⨾ same   = ρ
ρ ⨾ grow σ = grow (ρ ⨾ σ)

wk∋ : ∀ {w v k} → w ⊑ v → w ∋ k → v ∋ k
wk∋ same     i = i
wk∋ (grow ρ) i = there (wk∋ ρ i)

new : ∀ {k w} → w ⊑ (k ∷ w)
new = grow same

Sink : World → Set → Set
Sink w A = w ∋ slot A

Handle : World → Set
Handle w = w ∋ play

-- No native effects: a pure observer can only write to refs, and read
-- the clock.  Refs, sinks and handles are names in the world.
Pureᴾ : Prims
Pureᴾ = record
  { World = World ; _⊑_ = _⊑_ ; ⊑-refl = same ; _⨾_ = _⨾_
  ; RefOf = λ w t _ → w ∋ cell t ; Sink = Sink ; Handle = Handle
  ; wkRef = λ _ → wk∋ ; wkSink = wk∋ ; wkHandle = wk∋
  ; Cold = Timeline ; Eff = λ X → ℕ → X }

open Run Pureᴾ

PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

------------------------------------------------------------------------
-- The heap

record Callbacks (A : Set) (h : World) : Set₁ where
  field
    onNext     : A → Act h ⊤
    onComplete : Act h ⊤
    isClosed   : Act h Bool

-- What an entry holds, in the world the heap has reached.  A started
-- cold holds whether it is spent.
Val : World → Kind → Set₁
Val h (cell t) = Lift _ (El h t)
Val h (slot A) = Callbacks A h
Val h play     = Lift _ Bool

wkVal : ∀ {h v} k → h ⊑ v → Val h k → Val v k
wkVal (cell t) ρ x  = lift (wkEl t ρ (lower x))
wkVal (slot A) ρ cb = record { onNext = λ a → wkAct ρ (Callbacks.onNext cb a) ; onComplete = wkAct ρ (Callbacks.onComplete cb)
                             ; isClosed = wkAct ρ (Callbacks.isClosed cb) }
wkVal play     ρ x  = x

private
  get : ∀ {ℓ} {P : Kind → Set ℓ} {w k} → All P w → w ∋ k → P k
  get (x ∷ xs) here      = x
  get (x ∷ xs) (there i) = get xs i

  put : ∀ {ℓ} {P : Kind → Set ℓ} {w k} → All P w → w ∋ k → P k → All P w
  put (x ∷ xs) here      y = y ∷ xs
  put (x ∷ xs) (there i) y = x ∷ put xs i y

  wkAll : ∀ {h v} {w} → h ⊑ v → All (Val h) w → All (Val v) w
  wkAll ρ []                 = []
  wkAll ρ (_∷_ {x = k} x xs) = wkVal k ρ x ∷ wkAll ρ xs

-- A frame of a started cold, due on the clock.  `at` is the frame's
-- tick on the cold's own timeline, to time the frame after it.
record Timer (h : World) : Set₁ where
  field
    {A}    : Set
    due    : ℕ
    sink   : Sink h A
    handle : Handle h
    at′    : Time
    frame  : Burst A

wkTimer : ∀ {h v} → h ⊑ v → Timer h → Timer v
wkTimer ρ tm = record { due = Timer.due tm ; sink = wk∋ ρ (Timer.sink tm) ; handle = wk∋ ρ (Timer.handle tm)
                      ; at′ = Timer.at′ tm ; frame = Timer.frame tm }

record State (h : World) : Set₁ where
  field
    heap   : All (Val h) h
    clock  : ℕ
    timers : List (Timer h)

private
  mapList : ∀ {a b} {X : Set a} {Y : Set b} → (X → Y) → List X → List Y
  mapList f []       = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  -- The state, after making an entry holding `x`.
  extend : ∀ {h k} → State h → Val (k ∷ h) k → State (k ∷ h)
  extend st x = record { heap = x ∷ wkAll new (State.heap st) ; clock = State.clock st ; timers = mapList (wkTimer new) (State.timers st) }

  -- After every timer due no later: two timers due together fire in the
  -- order they were set.
  insert : ∀ {h} → Timer h → List (Timer h) → List (Timer h)
  insert tm []         = tm ∷ []
  insert tm (t′ ∷ ts) = if Timer.due t′ ≤ᵇ Timer.due tm then t′ ∷ insert tm ts else tm ∷ t′ ∷ ts

------------------------------------------------------------------------
-- The monad

-- A run from world h: the world it reached, the state there, and the
-- result — `nothing` where it diverged, the state kept for what it showed.
record Res (h : World) (B : Set) : Set₁ where
  constructor res
  field
    {reached} : World
    grown     : h ⊑ reached
    state     : State reached
    value     : Maybe B

-- Kripke: a computation set up in world w runs in any heap since.
M : World → Set → Set₁
M w B = ∀ {h} → w ⊑ h → State h → Res h B

private
  shift : ∀ {h v B} → h ⊑ v → Res v B → Res h B
  shift ρ (res σ st b) = res (ρ ⨾ σ) st b

  ret : ∀ {w B} → B → M w B
  ret b σ st = res same st (just b)

  then : ∀ {h A B} → (A → M h B) → Res h A → Res h B
  then f (res σ st (just a)) = shift σ (f a σ st)
  then f (res σ st nothing)  = res σ st nothing

  bind : ∀ {w A B} → M w A → (A → M w B) → M w B
  bind m f σ st = then (λ a τ → f a (σ ⨾ τ)) (m σ st)

  modifyState : ∀ {w} → (∀ {h} → w ⊑ h → State h → State h) → M w ⊤
  modifyState f σ st = res same (f σ st) (just tt)

  spent : ∀ {w} → Handle w → M w Bool
  spent hd σ st = res same st (just (lower (get (State.heap st) (wk∋ σ hd))))

  spend : ∀ {w} → Handle w → M w ⊤
  spend hd = modifyState λ σ st → record st { heap = put (State.heap st) (wk∋ σ hd) (lift true) }

  unlessSpent : ∀ {w} → Handle w → M w ⊤ → M w ⊤
  unlessSpent hd m = bind (spent hd) λ s → if s then ret tt else m

  callbacks : ∀ {w A} → Sink w A → ∀ {h} → w ⊑ h → State h → Callbacks A h
  callbacks s σ st = get (State.heap st) (wk∋ σ s)

-- THE PURE MONAD at budget n.  `startColdᴿ` delivers frame 0 inline and
-- sets a timer for each later frame where the burst before it ends;
-- `nextᴿ` pops the earliest, ties in the order they were set, as
-- `operation.Observable` does.  A burst is walked at most n steps before
-- it reads as `diverge`.
module Play (n : ℕ) (run : ∀ {w B} → Act w B → M w B) where
  private
    runCb : ∀ {w A B} → Sink w A → (∀ {h} → Callbacks A h → Act h B) → M w B
    runCb s f σ st = run (f (callbacks s σ st)) same st

  -- rxjs's `subscriber.closed` as a cold sees it.
  closedᴾ : ∀ {w A} → Sink w A → Handle w → M w Bool
  closedᴾ s hd = bind (spent hd) λ sp → if sp then ret true else runCb s Callbacks.isClosed

  sendᴾ : ∀ {w A} → Sink w A → A → M w ⊤
  sendᴾ s a = runCb s λ cb → Callbacks.onNext cb a

  finishᴾ : ∀ {w A} → Sink w A → M w ⊤
  finishᴾ s = runCb s Callbacks.onComplete

  setTimer : ∀ {w A} → Sink w A → Handle w → ℕ → Time → Burst A → M w ⊤
  setTimer s hd d t b = modifyState λ σ st → record st { timers = insert (record
    { due = State.clock st + d ; sink = wk∋ σ s ; handle = wk∋ σ hd ; at′ = t ; frame = b }) (State.timers st) }

  -- The frames after one ending at tick `now` of the cold's timeline.
  schedule : ∀ {w A} → Sink w A → Handle w → Time → ML A → M w ⊤
  schedule s hd now done     = unlessSpent hd (bind (spend hd) λ _ → finishᴾ s)
  schedule s hd now quiet    = ret tt
  schedule s hd now (at t b) = setTimer s hd (t ∸ now) t b

  -- A closed subscriber or a spent cold stops the playing.
  burst : ∀ {w A} → ℕ → Sink w A → Handle w → Time → Burst A → M w ⊤
  burst zero    s hd t b = λ σ st → res same st nothing
  burst (suc f) s hd t b = bind (closedᴾ s hd) λ c → if c then ret tt else step b
    where
      step : Burst _ → M _ ⊤
      step (emit a k) = bind (unlessSpent hd (sendᴾ s a)) λ _ → unlessSpent hd (burst f s hd t (Burst∞.force k))
      step (stall k)  = burst f s hd t (Burst∞.force k)
      step (close k)  = schedule s hd t (ML∞.force k)

  first : ∀ {w A} → Sink w A → Handle w → ML A → M w ⊤
  first s hd (at 0 b) = burst n s hd 0 b
  first s hd m        = schedule s hd 0 m

  nextᴾ : ∀ {w} → M w Bool
  nextᴾ σ st with State.timers st
  ... | []       = res same st (just false)
  ... | tm ∷ ts = then (λ _ _ st′ → res same st′ (just true))
                       (unlessSpent (Timer.handle tm) (burst n (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (Timer.frame tm))
                         same (record st { clock = Timer.due tm ; timers = ts }))

Pureᴿ : ℕ → Runtime
Pureᴿ n = record
  { M          = M
  ; return     = ret
  ; _>>=_      = bind
  ; newRefᴿ    = λ t a k σ st → shift new (k (σ ⨾ new) here same (extend st (lift (wkEl t (σ ⨾ new) a))))
  ; readRefᴿ   = λ r k σ st → k σ (lower (get (State.heap st) (wk∋ σ r))) same st
  ; writeRefᴿ  = λ {_} {t} r a → modifyState λ σ st → record st { heap = put (State.heap st) (wk∋ σ r) (lift (wkEl t σ a)) }
  ; registerᴿ  = λ run nx c x k σ st → shift new (k (σ ⨾ new) here same (extend st (record
                   { onNext = λ a → wkAct (σ ⨾ new) (nx a) ; onComplete = wkAct (σ ⨾ new) c ; isClosed = wkAct (σ ⨾ new) x })))
  ; sendᴿ      = λ run → Play.sendᴾ n run
  ; finishᴿ    = λ run → Play.finishᴾ n run
  ; startColdᴿ = λ run c s k σ st → shift new (bind (Play.first n run (wk∋ new (wk∋ σ s)) here (lower c)) (λ _ → k (σ ⨾ new) here)
                   same (extend st (lift false)))
  ; stopᴿ      = spend
  ; effᴿ       = λ e σ st → res same st (just (e (State.clock st)))
  ; divergeᴿ   = λ σ st → res same st nothing
  ; nextᴿ      = λ run → Play.nextᴾ n run
  }

------------------------------------------------------------------------
-- Observing a run

private
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

  -- The world a run starts in: its record of values, and whether the
  -- root completed.
  Root : Set → World
  Root A = cell (base (List (Time × A))) ∷ cell (base Bool) ∷ []

  recorder : ∀ {A} → Observer A (Root A)
  recorder = record
    { next     = λ a → eff (λ t → t) λ t → readRef here λ σ xs → writeRef (wk∋ σ here) (xs ++ [ (t , a) ]) (done tt)
    ; complete = writeRef (there here) true (done tt)
    ; closed   = done false }

  observe : ∀ {A} → Res (Root A) ⊤ → ML A
  observe (res σ st v) = frames (lower (get (State.heap st) (wk∋ σ here))) (end v (lower (get (State.heap st) (wk∋ σ (there here)))))
    where
      end : Maybe ⊤ → Bool → End
      end _        true  = finished
      end (just _) false = dry
      end nothing  false = cutOff (State.clock st)

-- Approximant n of the compiler: a `defer` nested more than n deep shows
-- nothing.  Lines up clause for clause with `denotation.Denote.approx`.
deferredᴺ : ℕ → Deferred
deferredᴺ zero    l ρ = ⊥ᴷ
deferredᴺ (suc n) l ρ = compileWith (deferredᴺ n) (Later.force l) ρ

compileᴺ : ℕ → ∀ {Γ A w} → PureObs Γ A → Env Γ w → Subscribe A w
compileᴺ n = compileWith (deferredᴺ n)

-- Runs a subscription on approximant n of the engine, with a top-level
-- observer recording each value at the tick the clock is on, and reads
-- the record off as a timeline: done if the root completed, quiet if
-- the queue ran dry, a burst that stalls forever where the budget ran
-- out.
runPure : ℕ → ∀ {A} → Subscribe A [] → ML A
runPure n {A} s = observe (drive (runᴺ n) (loopᴺ n) (wkSub (grow (grow same)) s) recorder same start)
  where
    open Engine (Pureᴿ n)

    runᴺ : ℕ → RunAct
    runᴺ zero    = λ _ → Runtime.divergeᴿ (Pureᴿ n)
    runᴺ (suc m) = interpret (runᴺ m)

    loopᴺ : ℕ → M (Root A) ⊤
    loopᴺ zero    = Runtime.divergeᴿ (Pureᴿ n)
    loopᴺ (suc m) = loopStep (runᴺ (suc m)) (loopᴺ m)

    start : State (Root A)
    start = record { heap = lift [] ∷ lift false ∷ [] ; clock = 0 ; timers = [] }

-- Approximant n of a program's run.
toArray : ℕ → ∀ {A} → PureObs [] A → ML A
toArray n o = runPure n (compileᴺ n o [])
