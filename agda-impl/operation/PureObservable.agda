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
open import operation.AbstractObservable using (Ty; Prims; module Run)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last; root) renaming (sub to subᴾ)

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

-- THE ROOT'S RECORD, kept by the runtime rather than in the heap: no
-- `Act` can name it, so whatever runs, it only grows — a value is added
-- at the clock's tick, and once the root has completed nothing more is.
-- `R` is the type the root observes.
data Out (R : Set) : Set → Set where
  note : R → Out R ⊤
  fin  : Out R ⊤

-- Refs, sinks and handles are names in the world.  A pure observer's
-- only native effects are the record's.
Pureᴾ : Set → Prims
Pureᴾ R = record
  { World = World ; _⊑_ = _⊑_ ; ⊑-refl = same ; _⨾_ = _⨾_
  ; RefOf = λ w t _ → w ∋ cell t ; Sink = Sink ; Handle = Handle
  ; wkRef = λ _ → wk∋ ; wkSink = wk∋ ; wkHandle = wk∋
  ; Cold = Timeline ; Eff = Out R }

PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

-- Everything run on behalf of a root observing `R`.
module Pure (R : Set) where
  open Run (Pureᴾ R)

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
  -- tick on the cold's own timeline, to time the frame after it; `from`
  -- the position the timer was set at, which places the frame.
  record Timer (h : World) : Set₁ where
    field
      {A}    : Set
      due    : ℕ
      sink   : Sink h A
      handle : Handle h
      at′    : Time
      from   : Pos
      frame  : Burst A

  wkTimer : ∀ {h v} → h ⊑ v → Timer h → Timer v
  wkTimer ρ tm = record { due = Timer.due tm ; sink = wk∋ ρ (Timer.sink tm) ; handle = wk∋ ρ (Timer.handle tm)
                        ; at′ = Timer.at′ tm ; from = Timer.from tm ; frame = Timer.frame tm }

  -- A frame set at e, due at t, is a cascade rooted at ix t ∷ subᴾ e ∷ [].
  cascade : ∀ {h} → Timer h → Pos
  cascade tm = ix (Timer.due tm) ∷ subᴾ (Timer.from tm) ∷ []

  record State (h : World) : Set₁ where
    field
      heap   : All (Val h) h
      clock  : ℕ
      timers : List (Timer h)
      log    : List (Time × R)     -- the root's record
      ended  : Bool                -- whether the root has completed
      pos    : Pos                 -- where the run is: a ghost
      marks  : List Pos            -- where each entry of the record was made: a ghost

  mapList : ∀ {a b} {X : Set a} {Y : Set b} → (X → Y) → List X → List Y
  mapList f []       = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  -- The state, after making an entry holding `x`.
  extend : ∀ {h k} → State h → Val (k ∷ h) k → State (k ∷ h)
  extend st x = record { heap = x ∷ wkAll new (State.heap st) ; clock = State.clock st ; timers = mapList (wkTimer new) (State.timers st)
                       ; log = State.log st ; ended = State.ended st ; pos = State.pos st ; marks = State.marks st }

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

  hereᴾ : ∀ {w B} → (Pos → M w B) → M w B
  hereᴾ k σ st = k (State.pos st) σ st

  gotoᴾ : ∀ {w} → Pos → M w ⊤
  gotoᴾ p = modifyState λ σ st → record st { pos = p }

  callbacks : ∀ {w A} → Sink w A → ∀ {h} → w ⊑ h → State h → Callbacks A h
  callbacks s σ st = get (State.heap st) (wk∋ σ s)

  -- THE PURE MONAD at budget n.  `startColdᴿ` delivers frame 0 inline and
  -- sets a timer for each later frame where the burst before it ends;
  -- `nextᴿ` pops the earliest, ties in the order they were set, as
  -- `operation.Observable` does.  A burst is walked at most n steps before
  -- it reads as `diverge`.
  module Play (n : ℕ) (run : ∀ {w B} → Act w B → M w B) where
    runCb : ∀ {w A B} → Sink w A → (∀ {h} → Callbacks A h → Act h B) → M w B
    runCb s f σ st = run (f (callbacks s σ st)) same st

    -- rxjs's `subscriber.closed` as a cold sees it.
    closedᴾ : ∀ {w A} → Sink w A → Handle w → M w Bool
    closedᴾ s hd = bind (spent hd) λ sp → if sp then ret true else runCb s Callbacks.isClosed

    sendᴾ : ∀ {w A} → Sink w A → A → M w ⊤
    sendᴾ s a = runCb s λ cb → Callbacks.onNext cb a

    finishᴾ : ∀ {w A} → Sink w A → M w ⊤
    finishᴾ s = runCb s Callbacks.onComplete

    setTimer : ∀ {w A} → Sink w A → Handle w → ℕ → Time → Pos → Burst A → M w ⊤
    setTimer s hd d t e b = modifyState λ σ st → record st { timers = insert (record
      { due = State.clock st + d ; sink = wk∋ σ s ; handle = wk∋ σ hd ; at′ = t ; from = e ; frame = b }) (State.timers st) }

    -- The frames after one ending at tick `now` of the cold's timeline,
    -- at position e: the completion there, the next frame's timer set there.
    schedule : ∀ {w A} → Sink w A → Handle w → Time → Pos → ML A → M w ⊤
    schedule s hd now e done     = unlessSpent hd (bind (spend hd) λ _ → bind (gotoᴾ e) λ _ → finishᴾ s)
    schedule s hd now e quiet    = ret tt
    schedule s hd now e (at t b) = setTimer s hd (t ∸ now) t e b

    -- A closed subscriber or a spent cold stops the playing.  A burst at
    -- r puts its i-th step at r ++ [ ix i ] and ends at r ++ [ last ].
    mutual
      burst : ∀ {w A} → ℕ → Sink w A → Handle w → Time → Pos → ℕ → Burst A → M w ⊤
      burst zero    s hd t r i b = λ σ st → res same st nothing
      burst (suc f) s hd t r i b = bind (closedᴾ s hd) λ c → if c then ret tt else stepᴾ f s hd t r i b

      stepᴾ : ∀ {w A} → ℕ → Sink w A → Handle w → Time → Pos → ℕ → Burst A → M w ⊤
      stepᴾ f s hd t r i (emit a k) = bind (unlessSpent hd (bind (gotoᴾ (r ++ [ ix i ])) λ _ → sendᴾ s a)) λ _ →
                                        unlessSpent hd (burst f s hd t r (suc i) (Burst∞.force k))
      stepᴾ f s hd t r i (stall k)  = burst f s hd t r (suc i) (Burst∞.force k)
      stepᴾ f s hd t r i (close k)  = schedule s hd t (r ++ [ last ]) (ML∞.force k)

    first : ∀ {w A} → Sink w A → Handle w → ML A → M w ⊤
    first s hd (at 0 b) = hereᴾ λ p → burst n s hd 0 p 0 b
    first s hd m        = hereᴾ λ p → schedule s hd 0 (p ++ [ last ]) m

    fire : ∀ {h} → List (Timer h) → State h → Res h Bool
    fire []        st = res same st (just false)
    fire (tm ∷ ts) st = then (λ _ _ st′ → res same st′ (just true))
                          (unlessSpent (Timer.handle tm) (burst n (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm))
                            same (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }))

    nextᴾ : ∀ {w} → M w Bool
    nextᴾ σ st = fire (State.timers st) st

  -- The record's effects.
  outcome : ∀ {h X} → Out R X → State h → Res h X
  outcome (note a) st = res same (record st { log = if State.ended st then State.log st else State.log st ++ [ (State.clock st , a) ]
                                            ; marks = if State.ended st then State.marks st else State.marks st ++ [ State.pos st ] }) (just tt)
  outcome fin     st = res same (record st { ended = true
                                            ; marks = if State.ended st then State.marks st else State.marks st ++ [ State.pos st ] }) (just tt)

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
    ; effᴿ       = λ e σ st → outcome e st
    ; hereᴿ      = hereᴾ
    ; gotoᴿ      = gotoᴾ
    ; divergeᴿ   = λ σ st → res same st nothing
    ; nextᴿ      = λ run → Play.nextᴾ n run
    }

  ------------------------------------------------------------------------
  -- Observing a run

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

  recorder : Observer R []
  recorder = record
    { next     = λ a → eff (note a) λ _ → done tt
    ; complete = eff fin λ _ → done tt
    ; closed   = done false }

  -- Whether the root completed, whether the run finished, the clock.
  endOf : Bool → Maybe ⊤ → ℕ → End
  endOf true  _        _ = finished
  endOf false (just _) _ = dry
  endOf false nothing  c = cutOff c

  observe : Res [] ⊤ → ML R
  observe (res σ st v) = frames (State.log st) (endOf (State.ended st) v (State.clock st))

  -- Approximant n of the compiler: a `defer` nested more than n deep shows
  -- nothing.  Lines up clause for clause with `denotation.Denote.approx`.
  deferredᴺ : ℕ → Deferred
  deferredᴺ zero    l ρ = ⊥ᴷ
  deferredᴺ (suc n) l ρ = deeper (compileWith (deferredᴺ n) (Later.force l) ρ)

  compileᴺ : ℕ → ∀ {Γ A w} → PureObs Γ A → Env Γ w → Subscribe A w
  compileᴺ n = compileWith (deferredᴺ n)

  -- Approximant m of the engine on a burst budget of n: callbacks run m
  -- deep, and the loop takes m turns.
  runᴺ : ∀ n → ℕ → ∀ {w B} → Act w B → M w B
  runᴺ n zero    = λ _ → Runtime.divergeᴿ (Pureᴿ n)
  runᴺ n (suc m) = Engine.interpret (Pureᴿ n) (runᴺ n m)

  loopᴺ : ∀ n → ℕ → M [] ⊤
  loopᴺ n zero    = Runtime.divergeᴿ (Pureᴿ n)
  loopᴺ n (suc m) = Engine.loopStep (Pureᴿ n) (runᴺ n (suc m)) (loopᴺ n m)

  start : State []
  start = record { heap = [] ; clock = 0 ; timers = [] ; log = [] ; ended = false ; pos = root ; marks = [] }

  -- Runs a subscription on approximant n of the engine, with the root
  -- observer recording each value at the tick the clock is on, and reads
  -- the record off as a timeline: done if the root completed, quiet if
  -- the queue ran dry, a burst that stalls forever where the budget ran
  -- out.
  runPure : ℕ → Subscribe R [] → ML R
  runPure n s = observe (Engine.drive (Pureᴿ n) (runᴺ n n) (loopᴺ n n) s recorder same start)

-- Approximant n of a program's run.
toArray : ℕ → ∀ {A} → PureObs [] A → ML A
toArray n {A} o = Pure.runPure A n (Pure.compileᴺ A n o [])

