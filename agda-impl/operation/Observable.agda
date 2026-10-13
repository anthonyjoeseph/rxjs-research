{-# OPTIONS --guardedness #-}

-- THE IO RUNTIME.  The shared engine, run in IO: real refs, real
-- threads, user-written colds.  Nothing here is proven; it is checked
-- against the TypeScript by the oracle.
--
-- `subscribe` is the one place the rules bend.  The pure runtime closes
-- the engine's recursion by unfolding it n times; a real program needs
-- every unfolding, and IO cannot re-run to take the limit, so here it is
-- closed with Haskell's `fix`.  That is sound only because nothing in the
-- engine forces a `defer`, a stored callback or the loop's next turn
-- before it is reached — which laziness then delivers.
module operation.Observable where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Unit using (⊤; tt)
open import IO.Primitive.Core using (pure; _>>=_)
open import Level using (Lift; lift; lower; 0ℓ) renaming (suc to lsuc)

open import Tree using (Obs; Later)
open import operation.AbstractObservable using (Prims; module Run)
open import denotation.MonotonicList using (Timeline)

postulate
  IORef    : Set → Set
  -- A registered observer: its two callbacks, in the runtime's table.
  SinkSlot : Set → Set
  -- A started cold: its `Internal` and `teardown`, and whether it is done.
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

-- What a cold is handed to emit with.
record Emit (A : Set) : Set where
  field
    produce  : A → IO ⊤
    complete : IO ⊤

-- `create` takes an `Emit`, not `produce` and `complete` curried: with
-- `Internal` erased MAlonzo compiles this record to a `newtype`, and GHC
-- rejects a newtype whose field mentions `IO` bare — its kind-polymorphic
-- arguments become existentials.
record IOCold (A : Set) : Set₁ where
  field
    Internal : Set
    create   : Emit A → Started Internal

IOᴾ : Prims
IOᴾ = record { Ref = IORef ; Cold = IOCold ; Handle = Slot ; Sink = SinkSlot ; Eff = IO }

open Run IOᴾ

Observable : Set → Set₁
Observable = Obs IOCold []

-- The engine's monad: IO, lifted to the universe its tables live in.
M : Set → Set₁
M A = IO (Lift (lsuc 0ℓ) A)

postulate
  -- The primitives, over IORefs.  `startColdᴿ'` runs the user's
  -- `subscription`, buffering its produces into the burst it then
  -- delivers; later produces go on one queue, and `nextᴿ'` takes from
  -- it, so two threads' emissions never interleave.
  newRefᴿ'    : ∀ {A} → A → M (IORef A)
  readRefᴿ'   : ∀ {A} → IORef A → M A
  writeRefᴿ'  : ∀ {A} → IORef A → A → M ⊤
  registerᴿ'  : ∀ {A} → (A → Act ⊤) → Act ⊤ → M (SinkSlot A)
  sendᴿ'      : (∀ {B} → Act B → M B) → ∀ {A} → SinkSlot A → A → M ⊤
  finishᴿ'    : (∀ {B} → Act B → M B) → ∀ {A} → SinkSlot A → M ⊤
  startColdᴿ' : (∀ {B} → Act B → M B) → ∀ {A} → IOCold A → SinkSlot A → M Slot
  stopᴿ'      : Slot → M ⊤
  divergeᴿ'   : ∀ {A} → M A
  nextᴿ'      : (∀ {B} → Act B → M B) → M Bool

  -- A pure timeline played by a forked thread that sleeps between
  -- frames.  The oracle runs one program on both runtimes through this.
  fromTimeline : ∀ {A} → Timeline A → IOCold A

  fix! : ∀ {ℓ} {A : Set ℓ} → (A → A) → A

{-# FOREIGN GHC import qualified Data.Function #-}
{-# COMPILE GHC fix! = \ _ _ -> Data.Function.fix #-}

IOᴿ : Runtime
IOᴿ = record
  { M          = M
  ; return     = λ a → pure (lift a)
  ; _>>=_      = λ m f → m >>= λ a → f (lower a)
  ; newRefᴿ    = newRefᴿ'
  ; readRefᴿ   = readRefᴿ'
  ; writeRefᴿ  = writeRefᴿ'
  ; registerᴿ  = registerᴿ'
  ; sendᴿ      = sendᴿ'
  ; finishᴿ    = finishᴿ'
  ; startColdᴿ = startColdᴿ'
  ; stopᴿ      = stopᴿ'
  ; effᴿ       = λ e → e >>= λ a → pure (lift a)
  ; divergeᴿ   = divergeᴿ'
  ; nextᴿ      = nextᴿ'
  }

open Engine IOᴿ

-- The recursion, closed for real.
deferred∞ : Deferred
deferred∞ = fix! λ d {Γ} {A} l ρ → compileWith (λ {Γ′} {A′} → d {Γ′} {A′}) (Later.force l) ρ

run∞ : RunAct
run∞ = fix! λ self {B} → interpret (λ {B′} → self {B′}) {B}

loop∞ : M ⊤
loop∞ = fix! (loopStep run∞)

-- THE ENTRY POINT: runs until nothing is left to wait for.
subscribe : ∀ {A} → Observable A → (A → IO ⊤) → IO ⊤
subscribe {A} o f = drive run∞ loop∞ (compileWith deferred∞ o []) observer >>= λ _ → pure tt
  where
    observer : Observer A
    observer = record
      { next     = λ a → eff (f a) λ _ → done tt
      ; complete = done tt
      }
