{-# OPTIONS --guardedness --large-indices #-}

-- THE PURE RUNTIME'S DATA.  A heap and a virtual clock, which
-- `operation.Machine` steps.  A cold leaf is a timeline relative to its
-- subscribe time, so the program itself says when everything happens:
-- there is no separate schedule, and quantifying over programs covers
-- every ordering.
--
-- The heap is TYPED BY ITS WORLD: a list saying what each entry is, so
-- reading a cell returns its content at its own type with no cast.
-- `--large-indices` only because the world lists codes, which live in
-- `Set₁`, and a name is a position in it.
module operation.PureObservable where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Nat using (ℕ; _≤ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)

open import Tree using (Obs)
open import operation.AbstractObservable using (Ty; Prims; module Run)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last; root) renaming (sub to subᴾ)

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
      frame  : Frame A at′

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


  start : State []
  start = record { heap = [] ; clock = 0 ; timers = [] ; log = [] ; ended = false ; pos = root ; marks = [] }
