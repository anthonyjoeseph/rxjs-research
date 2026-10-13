{-# OPTIONS --guardedness #-}

-- THE ONE COPY OF THE OPERATIONAL SEMANTICS.  A program is a tree
-- (`Obs`, in `operation.abstraction.Tree`); compiling it gives `Act` programs, built from the operator
-- kernels; an interpreter and an event loop run them.  All of that is
-- here, written once, against a monad the runtime supplies (`Runtime`):
-- `Observable` hands it IO, `PureObservable` a state monad over a heap
-- and a virtual clock.  So the pure runtime IS the IO runtime, with a
-- different monad.
--
-- The one other difference is how recursion is closed.  Compiling a
-- `defer`, running a stored callback and taking the loop's next turn are
-- each written as one layer, open in the recursion.  The pure runtime
-- closes them by unfolding n times — approximant n, as `Denote` does —
-- and the IO runtime closes them for real, with Haskell's `fix`.
--
-- The shared code is parametric in the runtime's types (`Prims`), so it
-- can neither inspect a ref, nor look inside a cold, nor perform IO.
module operation.AbstractObservable where

open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import operation.abstraction.Tree

------------------------------------------------------------------------
-- What a runtime supplies

record Prims : Set₂ where
  field
    Ref    : Set → Set        -- one cell of operator state
    Cold   : Set → Set₁       -- the cold leaf
    Handle : Set              -- a started cold, as the runtime tracks it
    Sink   : Set → Set        -- a registered observer, as a first-order name
    Eff    : Set → Set        -- what a top-level observer may do natively

module Run (P : Prims) where
  open Prims P

  -- A connect's subject, kept in the environment.  First-order on
  -- purpose: its subscribers are `Sink`s, not callbacks.  A sink joining
  -- after the source has completed is completed at once, as in rxjs.
  record Subject (A : Set) : Set where
    field
      subscribers : Ref (List (Sink A))
      closed      : Ref Bool

  Env : List Set → Set₁
  Env = All Subject

  -- THE OPERATORS' LANGUAGE: the free monad over the runtime's
  -- primitives.  The kernels are written in it once, and every runtime
  -- runs those same programs.
  --
  -- A callback cannot be stored in a `Ref`: `Act` would have to quantify
  -- over its own universe.  So an observer is registered with the
  -- runtime and handed back as a first-order `Sink`, which is also what
  -- lets the pure runtime be an ordinary Agda state monad later — its
  -- heap holds `Act` callbacks, never its own computations.
  data Act : Set → Set₁ where
    done      : ∀ {B} → B → Act B
    newRef    : ∀ {A B} → A → (Ref A → Act B) → Act B
    readRef   : ∀ {A B} → Ref A → (A → Act B) → Act B
    writeRef  : ∀ {A B} → Ref A → A → Act B → Act B
    register  : ∀ {A B} → (A → Act ⊤) → Act ⊤ → (Sink A → Act B) → Act B
    send      : ∀ {A B} → Sink A → A → Act B → Act B
    finish    : ∀ {A B} → Sink A → Act B → Act B
    startCold : ∀ {A B} → Cold A → Sink A → (Handle → Act B) → Act B
    stop      : ∀ {B} → Handle → Act B → Act B
    eff       : ∀ {A B} → Eff A → (A → Act B) → Act B
    -- No information: what an unfolding cut off by the pure runtime's
    -- budget does.  The IO runtime never reaches it.
    diverge   : ∀ {B} → Act B

  record Observer (A : Set) : Set₁ where
    field
      next     : A → Act ⊤
      complete : Act ⊤

  record Subscription : Set₁ where
    field unsubscribe : Act ⊤

  -- Subscribing, in continuation-passing style: given an observer, and
  -- what to do once the subscription exists, describe the work.
  Subscribe : Set → Set₁
  Subscribe A = Observer A → (Subscription → Act ⊤) → Act ⊤

  -- Subscribe through the runtime: register the observer, hand the
  -- runtime its sink, wrap the handle.
  via : ∀ {A} → (Sink A → (Handle → Act ⊤) → Act ⊤) → Subscribe A
  via start o k = register (Observer.next o) (Observer.complete o) λ s →
                  start s λ h → k (record { unsubscribe = stop h (done tt) })

  ⊥ᴷ : ∀ {A} → Subscribe A
  ⊥ᴷ o k = diverge

  -- THE OPERATORS.  Each is a kernel over its children's `Subscribe`, so
  -- each is written, and later proven, on its own.  Their bodies are
  -- ordinary `Act` programs: a `Ref` for scan's accumulator, flatten's
  -- lane handles and completion count, a subject's subscribers.
  postulate
    emptyᴷ     : ∀ {A} → Subscribe A
    ofᴷ        : ∀ {A} → List A → Subscribe A
    mapᴷ       : ∀ {A B} → (A → B) → Subscribe A → Subscribe B
    scanᴷ      : ∀ {A B} → (B → A → B) → B → Subscribe A → Subscribe B
    takeWhileᴷ : ∀ {A} → (A → Bool) → Subscribe A → Subscribe A
    flattenᴷ   : ∀ {A B} → FlatOp → (A → Maybe B × Maybe (Subscribe B)) → Subscribe A → Subscribe B
    -- Allocates the subject, subscribes the body over it, THEN the
    -- source into it — body first, so the source's synchronous burst
    -- reaches whatever the body joined synchronously.  Unsubscribing
    -- stops both.  Allocated per subscription of the `connect` node, so
    -- one bound outside a `defer` is the SAME subject on every
    -- re-subscription of the deferred body.
    connectᴷ   : ∀ {A B} → Subscribe A → (Subject A → Subscribe B) → Subscribe B
    -- Adds the sink.  Nothing else: the source is already running.
    joinᴷ      : ∀ {A} → Subject A → Subscribe A

  -- What a `defer` turns into.  Recursion lives only here, and each
  -- runtime closes it its own way: the pure one by unfolding n times,
  -- the IO one for real.
  Deferred : Set₁
  Deferred = ∀ {Γ A} → Later Cold Γ A → Env Γ → Subscribe A

  -- THE TREE, COMPILED.  Structural everywhere except `defer`, which is
  -- handed to `d`, so this is total whatever recursion the tree holds.
  mutual
    compileWith : Deferred → ∀ {Γ A} → Obs Cold Γ A → Env Γ → Subscribe A
    compileWith d (cold c)         ρ = via (startCold c)
    compileWith d empty            ρ = emptyᴷ
    compileWith d (of xs)          ρ = ofᴷ xs
    compileWith d (map f s)        ρ = mapᴷ f (compileWith d s ρ)
    compileWith d (scan f z s)     ρ = scanᴷ f z (compileWith d s ρ)
    compileWith d (takeWhile p s)  ρ = takeWhileᴷ p (compileWith d s ρ)
    compileWith d (flatten op f s) ρ = flattenᴷ op (λ a → lane d (f a) ρ) (compileWith d s ρ)
    compileWith d (connect s b)    ρ = connectᴷ (compileWith d s ρ) λ st → compileWith d b (st ∷ ρ)
    compileWith d (connected i)    ρ = joinᴷ (lookup ρ i)
    compileWith d (defer l)        ρ = d l ρ

    -- a separate function, so Agda can see the lane is a subterm
    lane : ∀ {Γ B} → Deferred → Maybe B × Maybe (Obs Cold Γ B) → Env Γ → Maybe B × Maybe (Subscribe B)
    lane d (e , nothing) ρ = e , nothing
    lane d (e , just l)  ρ = e , just (compileWith d l ρ)

  -- THE MONAD, and the handful of things only it can do.  This is the
  -- whole of a runtime: `Observable` supplies IO, `PureObservable` a
  -- state monad over a heap and a virtual clock.  The operations that
  -- run a stored callback take the interpreter to run it with, since the
  -- callback lives in the runtime's tables.
  record Runtime : Set₂ where
    field
      M          : Set → Set₁
      return     : ∀ {A} → A → M A
      _>>=_      : ∀ {A B} → M A → (A → M B) → M B
      newRefᴿ    : ∀ {A} → A → M (Ref A)
      readRefᴿ   : ∀ {A} → Ref A → M A
      writeRefᴿ  : ∀ {A} → Ref A → A → M ⊤
      registerᴿ  : ∀ {A} → (A → Act ⊤) → Act ⊤ → M (Sink A)
      sendᴿ      : (∀ {B} → Act B → M B) → ∀ {A} → Sink A → A → M ⊤
      finishᴿ    : (∀ {B} → Act B → M B) → ∀ {A} → Sink A → M ⊤
      -- Delivers the cold's subscribe burst inline, and arranges for its
      -- later emissions to reach the event queue.
      startColdᴿ : (∀ {B} → Act B → M B) → ∀ {A} → Cold A → Sink A → M Handle
      stopᴿ      : Handle → M ⊤
      effᴿ       : ∀ {A} → Eff A → M A
      divergeᴿ   : ∀ {A} → M A
      -- Runs the next queued emission as one cascade; false when nothing
      -- is left to wait for.  The pure runtime pops its earliest frame
      -- (ties in the order they were queued, as two `setTimeout`s with one
      -- delay); the IO one blocks on its queue.
      nextᴿ      : (∀ {B} → Act B → M B) → M Bool

  -- THE ENGINE: interpreter, event loop and entry point, written once.
  -- Each is one layer, open in the recursion it needs — a callback run
  -- from a table, the loop's next turn — and the runtime closes it.
  module Engine (R : Runtime) where
    open Runtime R

    RunAct : Set₁
    RunAct = ∀ {B} → Act B → M B

    -- `self` runs a stored callback; everything else is structural.
    interpret : RunAct → RunAct
    interpret self (done b)          = return b
    interpret self (newRef a k)      = newRefᴿ a >>= λ r → interpret self (k r)
    interpret self (readRef r k)     = readRefᴿ r >>= λ a → interpret self (k a)
    interpret self (writeRef r a k)  = writeRefᴿ r a >>= λ _ → interpret self k
    interpret self (register n c k)  = registerᴿ n c >>= λ s → interpret self (k s)
    interpret self (send s a k)      = sendᴿ self s a >>= λ _ → interpret self k
    interpret self (finish s k)      = finishᴿ self s >>= λ _ → interpret self k
    interpret self (startCold c s k) = startColdᴿ self c s >>= λ h → interpret self (k h)
    interpret self (stop h k)        = stopᴿ h >>= λ _ → interpret self k
    interpret self (eff e k)         = effᴿ e >>= λ a → interpret self (k a)
    interpret self diverge           = divergeᴿ

    -- One turn of the event loop; `again` is the rest of it.
    loopStep : RunAct → M ⊤ → M ⊤
    loopStep run again = nextᴿ run >>= λ more → if more then again else return tt

    -- Subscribe at the root, then run the loop until nothing is left.
    drive : RunAct → M ⊤ → ∀ {A} → Subscribe A → Observer A → M ⊤
    drive run loop s o = run (s o λ _ → done tt) >>= λ _ → loop
