{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  Real refs, real threads, user-written colds.  Nothing
-- here is proven; it runs the same `subscribe` the pure runtime runs, and
-- is checked against the TypeScript by the oracle.
module Observable where

open import Agda.Builtin.IO using (IO)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using ([])
open import Data.Unit using (⊤; tt)

open import AbstractObservable
open import MonotonicList using (Timeline)

postulate
  IORef    : Set → Set
  -- A registered observer: its two callbacks, in the runtime's table.
  SinkSlot : Set → Set
  -- A live subscription: a started cold (its `Internal` and `teardown`)
  -- or a subscribed subtree (its own `unsubscribe`), and whether it is done.
  Slot     : Set

-- A cold, as the user writes it.  `subscription` runs on the subscribing
-- thread: every `produce` it makes before returning is the synchronous
-- burst, delivered once it returns.  A `produce` from anywhere later —
-- typically a thread it forked — is an async emission.  `teardown` runs
-- once, on completion or unsubscribe; after it, `produce` and `complete`
-- are ignored.
record Started (Internal : Set) : Set where
  field
    subscription : IO Internal
    teardown     : Internal → IO ⊤

record IOCold (A : Set) : Set₁ where
  field
    Internal : Set
    create   : (produce : A → IO ⊤) → (complete : IO ⊤) → Started Internal

IOᴾ : Prims
IOᴾ = record { Ref = IORef ; Cold = IOCold ; Handle = Slot ; Sink = SinkSlot ; Eff = IO }

open Run IOᴾ

Observable : Set → Set₁
Observable = Obs IOCold []

postulate
  -- THE IO INTERPRETER.  Refs are IORefs.  `startCold` runs the user's
  -- `subscription`, buffering its produces into the burst; later produces
  -- go on one queue, and a single loop runs each queued cascade to
  -- completion, so two threads' emissions never interleave.  `child`
  -- is unfolded here, by calling `subscribe` on the subtree: a
  -- synchronous loop really does spin, as it does in rxjs.
  runAct : Act ⊤ → IO ⊤

  -- Blocks until the observable completes.
  toArray : ∀ {A} → Observable A → IO (List A)

  -- A pure timeline played by a forked thread that sleeps between
  -- frames.  The oracle runs one program on both runtimes through this.
  fromTimeline : ∀ {A} → Timeline A → IOCold A

-- The entry point: runs forever, meant to be called once.
subscribe! : ∀ {A} → Observable A → (A → IO ⊤) → IO ⊤
subscribe! {A} o f = runAct (subscribe o [] observer λ _ → done tt)
  where
    observer : Observer A
    observer = record
      { next     = λ a → eff (f a) λ _ → done tt
      ; complete = done tt
      }

toIO : ∀ {Γ A} → Obs Timeline Γ A → Obs IOCold Γ A
toIO = mapLeaves fromTimeline
