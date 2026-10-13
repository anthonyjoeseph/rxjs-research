{-# OPTIONS --guardedness #-}

-- THE ONE COPY OF THE OPERATOR LOGIC.  A program is a tree (`Obs`).
-- Subscribing to it does not perform anything: it builds an `Act`, a
-- description of the reads, writes and subscriptions it performs.  Each
-- runtime interprets `Act` its own way — `Observable` into real IO,
-- `PureObservable` into a virtual-clock state machine — so the operators
-- are written once and both runtimes run that code.
--
-- A runtime is a handful of choices (`Prims`).  The shared code is
-- parametric in all of them, so it can neither inspect a ref, nor look
-- inside a cold, nor perform IO — which is what makes it safe to run on
-- both sides.
module AbstractObservable where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; map₂)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Programs

-- How `flatten` handles a lane arriving while others are live: merge
-- (with an optional concurrency bound; `just 1` is concat), switch to it,
-- or ignore it.
data FlatOp : Set where
  mergeᶠ            : Maybe ℕ → FlatOp
  switchᶠ exhaustᶠ  : FlatOp

-- `C` is the cold leaf.  `Γ` lists the connects in scope.  `connect`
-- is rxjs's `connect(selector)`: subscribing it makes a fresh subject,
-- subscribes the body with that subject as its handle, then subscribes
-- the source into the subject, once.  The handle is BOUND by the body and
-- referred to by position (`connected`), so it is the one operator with
-- identity and still needs no names: the binder is the identity, and a
-- `connect` inside a lane is a fresh one per subscription, as in rxjs.
-- Every hot observable is a `connect`; a ref-counted `share` is not a
-- primitive.
--
-- Recursion is Agda's own, guarded by `defer`, which is SYNCHRONOUS as in
-- rxjs.  So a synchronous infinite loop is a legal program; the runtimes
-- report it as a burst that never closes, rather than refusing it.
--
-- THE PRIMITIVES, and nothing derivable: merge, mergeMap, switchMap and
-- the rest are `flatten` (see Derived, below).
--
-- `flatten` reads each element as an optional ECHO — a value leaving as
-- the element arrives, before its lane is handled — beside an optional
-- LANE.  The lane comes out of a function rather than an element of type
-- `Obs`, because `Obs` lives in `Set₁` and an element type is a `Set`:
-- the size of the universe, not taste, puts that `map` inside `flatten`.
mutual
  data Obs (C : Set → Set₁) : List Set → Set → Set₁ where
    cold      : ∀ {Γ A} → C A → Obs C Γ A
    empty     : ∀ {Γ A} → Obs C Γ A
    of        : ∀ {Γ A} → List A → Obs C Γ A
    map       : ∀ {Γ A B} → (A → B) → Obs C Γ A → Obs C Γ B
    scan      : ∀ {Γ A B} → (B → A → B) → B → Obs C Γ A → Obs C Γ B
    takeWhile : ∀ {Γ A} → (A → Bool) → Obs C Γ A → Obs C Γ A
    flatten   : ∀ {Γ A B} → FlatOp → (A → Maybe B × Maybe (Obs C Γ B)) → Obs C Γ A → Obs C Γ B
    connect   : ∀ {Γ A B} → Obs C Γ A → Obs C (A ∷ Γ) B → Obs C Γ B
    connected : ∀ {Γ A} → A ∈ Γ → Obs C Γ A
    defer     : ∀ {Γ A} → Later C Γ A → Obs C Γ A

  record Later (C : Set → Set₁) (Γ : List Set) (A : Set) : Set₁ where
    coinductive
    field force : Obs C Γ A

-- Move a program to a larger scope (a `connect` bound around it).
-- Corecursive through `defer`: the renamed body is produced only when
-- forced.
mutual
  rename : ∀ {C Γ Δ A} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Obs C Γ A → Obs C Δ A
  rename r (cold c)         = cold c
  rename r empty            = empty
  rename r (of xs)          = of xs
  rename r (map f s)        = map f (rename r s)
  rename r (scan f z s)     = scan f z (rename r s)
  rename r (takeWhile p s)  = takeWhile p (rename r s)
  rename r (flatten op f s) = flatten op (λ a → renameLane r (f a)) (rename r s)
  rename r (connect s b)    = connect (rename r s) (rename (ext r) b)
    where
      ext : ∀ {B Γ Δ} → (∀ {X} → X ∈ Γ → X ∈ Δ) → ∀ {X} → X ∈ B ∷ Γ → X ∈ B ∷ Δ
      ext r (here p)  = here p
      ext r (there i) = there (r i)
  rename r (connected i)   = connected (r i)
  rename r (defer l)        = defer (renameLater r l)

  renameLane : ∀ {C Γ Δ B} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Maybe B × Maybe (Obs C Γ B) → Maybe B × Maybe (Obs C Δ B)
  renameLane r (e , nothing) = e , nothing
  renameLane r (e , just l)  = e , just (rename r l)

  renameLater : ∀ {C Γ Δ A} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Later C Γ A → Later C Δ A
  renameLater r l .Later.force = rename r (Later.force l)

------------------------------------------------------------------------
-- Derived

merge : ∀ {C Γ A} → Obs C Γ A → Obs C Γ A → Obs C Γ A
merge s t = flatten (mergeᶠ nothing) (λ b → nothing , just (if b then s else t)) (of (true ∷ false ∷ []))

flatMap : ∀ {C Γ A B} → FlatOp → (A → Obs C Γ B) → Obs C Γ A → Obs C Γ B
flatMap op f = flatten op λ a → nothing , just (f a)

-- The motivating example: no μ, no binder, no restriction on where the
-- self-reference sits beyond `defer`.  Emits 1 forever, synchronously:
-- the echo, then the same program again as the lane.
ones : ∀ {C Γ} → Obs C Γ ℕ
ones = flatten (mergeᶠ nothing) (λ _ → just 1 , just (defer λ where .Later.force → ones)) (of (tt ∷ []))

postulate
  -- Swap the leaves, keeping the tree.  This is how one program runs on
  -- both runtimes: `Observable.toIO` realises each pure timeline as an
  -- IO cold.
  mapLeaves : ∀ {C C′ Γ A} → (∀ {X} → C X → C′ X) → Obs C Γ A → Obs C′ Γ A

------------------------------------------------------------------------
-- What a runtime supplies

record Prims : Set₂ where
  field
    Ref    : Set → Set        -- one cell of operator state
    Cold   : Set → Set₁       -- the cold leaf
    Handle : Set              -- a live subscription, as the runtime tracks it
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

  -- The free monad over the runtime's primitives.
  --
  -- TWO THINGS ARE PRIMITIVES BECAUSE AGDA FORCES THEM TO BE.
  --
  -- A callback cannot be stored in a `Ref`, and a primitive cannot return
  -- one: either puts `Act` to the left of an arrow in its own
  -- constructor.  So an observer is registered with the runtime and
  -- handed back as a first-order `Sink`, and a subscription comes back as
  -- a `Handle`.  This is the old evaluator's node table, but owned by
  -- each runtime, behind three constructors, and invisible to the
  -- operators.
  --
  -- Subscribing a subtree is `child`, which the RUNTIME unfolds.  If
  -- `subscribe` recursed itself, the guard on a `defer` could be eaten by
  -- the operator kernel wrapping it — a total kernel may strip a `later`,
  -- and `x = map f (defer x)` then unfolds to itself — so Agda rightly
  -- refuses.  Each runtime's interpreter is one machine whose own output
  -- guards the unfolding, so there it is productive.
  data Act : Set → Set₁ where
    done      : ∀ {B} → B → Act B
    newRef    : ∀ {A B} → A → (Ref A → Act B) → Act B
    readRef   : ∀ {A B} → Ref A → (A → Act B) → Act B
    writeRef  : ∀ {A B} → Ref A → A → Act B → Act B
    register  : ∀ {A B} → (A → Act ⊤) → Act ⊤ → (Sink A → Act B) → Act B
    send      : ∀ {A B} → Sink A → A → Act B → Act B
    finish    : ∀ {A B} → Sink A → Act B → Act B
    startCold : ∀ {A B} → Cold A → Sink A → (Handle → Act B) → Act B
    child     : ∀ {Γ A B} → Obs Cold Γ A → Env Γ → Sink A → (Handle → Act B) → Act B
    stop      : ∀ {B} → Handle → Act B → Act B
    eff       : ∀ {A B} → Eff A → (A → Act B) → Act B

  record Observer (A : Set) : Set₁ where
    field
      next     : A → Act ⊤
      complete : Act ⊤

  record Subscription : Set₁ where
    field unsubscribe : Act ⊤

  -- Subscribing, in continuation-passing style: given an observer, and
  -- what to do once the subscription handle exists, describe the work.
  Subscribe : Set → Set₁
  Subscribe A = Observer A → (Subscription → Act ⊤) → Act ⊤

  -- Subscribe through the runtime: register the observer, hand the
  -- runtime its sink, wrap the handle.
  via : ∀ {A} → (Sink A → (Handle → Act ⊤) → Act ⊤) → Subscribe A
  via start o k = register (Observer.next o) (Observer.complete o) λ s →
                  start s λ h → k (record { unsubscribe = stop h (done tt) })

  sub : ∀ {Γ A} → Obs Cold Γ A → Env Γ → Subscribe A
  sub s ρ = via (child s ρ)

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

  -- ONE LAYER.  The tree's shape picks the kernel; children are handed
  -- over as `child` requests, so nothing here recurses and `defer` is
  -- just a child like any other.
  subscribe : ∀ {Γ A} → Obs Cold Γ A → Env Γ → Subscribe A
  subscribe (cold c)         ρ = via (startCold c)
  subscribe empty            ρ = emptyᴷ
  subscribe (of xs)          ρ = ofᴷ xs
  subscribe (map f s)        ρ = mapᴷ f (sub s ρ)
  subscribe (scan f z s)     ρ = scanᴷ f z (sub s ρ)
  subscribe (takeWhile p s)  ρ = takeWhileᴷ p (sub s ρ)
  subscribe (flatten op f s) ρ = flattenᴷ op (λ a → map₂ (Maybe.map λ l → sub l ρ) (f a)) (sub s ρ)
  subscribe (connect s b)    ρ = connectᴷ (sub s ρ) λ st → sub b (st ∷ ρ)
  subscribe (connected i)    ρ = joinᴷ (lookup ρ i)
  subscribe (defer l)        ρ = sub (Later.force l) ρ
