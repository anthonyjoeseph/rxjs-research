{-# OPTIONS --guardedness --large-indices #-}

-- THE PURE RUNTIME'S OWN PARTS.  The heap and the machine are shared
-- (`operation.AbstractObservable`'s `Heap` and `Machine`); what is the
-- pure runtime's alone is its cold, a timeline relative to its subscribe
-- time, its virtual clock and timers, and its native effect, the root's
-- record.  So the program itself says when everything happens: there is
-- no separate schedule, and quantifying over programs covers every
-- ordering.  `operation.Machine` is the driver that plays them.
module operation.PureObservable where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.Nat using (ℕ; _≤ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Tree using (Obs)
open import operation.AbstractObservable using (Prims; prims; module Heap; module Run)
open import denotation.MonotonicList.Events using (ML; Burst; Burst∞; ML∞; From; Frame; Frame∞; From∞; done; quiet; at; emit; stall; close; Time; Timeline; Pos; ix; last; root) renaming (sub to subᴾ)

-- THE ROOT'S RECORD, kept by the runtime rather than in the heap: no
-- `Act` can name it, so whatever runs, it only grows — a value is added
-- at the clock's tick, and once the root has completed nothing more is.
-- `R` is the type the root observes.
data Out (R : Set) : Set → Set where
  note : R → Out R ⊤
  fin  : Out R ⊤

-- A pure observer's only native effects are the record's.
Pureᴾ : Set → Prims
Pureᴾ R = prims Timeline (Out R)

PureObs : List Set → Set → Set₁
PureObs = Obs Timeline

-- Everything run on behalf of a root observing `R`.
module Pure (R : Set) where
  open Heap
  open Run (Pureᴾ R)

  ------------------------------------------------------------------------
  -- The clock's timers

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

  mapList : ∀ {a b} {X : Set a} {Y : Set b} → (X → Y) → List X → List Y
  mapList f []       = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

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

