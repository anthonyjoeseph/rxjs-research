{-# OPTIONS --guardedness #-}

-- THE ONE COPY OF THE OPERATIONAL SEMANTICS.  A program is a tree
-- (`Obs`, in `Tree`); compiling it gives `Act` programs, built from the operator
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

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List using (List; _∷_; []; _++_; [_]; null)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; Obs; cold; empty; of; map; scan; takeWhile; flatten; connect; connected; defer; Later)

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
    register  : ∀ {A B} → (A → Act ⊤) → Act ⊤ → Act Bool → (Sink A → Act B) → Act B
    send      : ∀ {A B} → Sink A → A → Act B → Act B
    finish    : ∀ {A B} → Sink A → Act B → Act B
    startCold : ∀ {A B} → Cold A → Sink A → (Handle → Act B) → Act B
    stop      : ∀ {B} → Handle → Act B → Act B
    eff       : ∀ {A B} → Eff A → (A → Act B) → Act B
    -- No information: what an unfolding cut off by the pure runtime's
    -- budget does.  The IO runtime never reaches it.
    diverge   : ∀ {B} → Act B

  -- `closed` is rxjs's `subscriber.closed`: a source polls it, and stops,
  -- so a cut reaches a source still inside its own subscribe burst.
  record Observer (A : Set) : Set₁ where
    field
      next     : A → Act ⊤
      complete : Act ⊤
      closed   : Act Bool

  record Subscription : Set₁ where
    field unsubscribe : Act ⊤

  -- Subscribing, in continuation-passing style: given an observer, and
  -- what to do once the subscription exists, describe the work.
  Subscribe : Set → Set₁
  Subscribe A = Observer A → (Subscription → Act ⊤) → Act ⊤

  -- Subscribe through the runtime: register the observer, hand the
  -- runtime its sink, wrap the handle.
  via : ∀ {A} → (Sink A → (Handle → Act ⊤) → Act ⊤) → Subscribe A
  via start o k = register (Observer.next o) (Observer.complete o) (Observer.closed o) λ s →
                  start s λ h → k (record { unsubscribe = stop h (done tt) })

  ⊥ᴷ : ∀ {A} → Subscribe A
  ⊥ᴷ o k = diverge

  -- Sequencing, which the free monad gets by walking its continuations.
  infixl 1 _>>=ᴬ_ _>>ᴬ_
  _>>=ᴬ_ : ∀ {A B} → Act A → (A → Act B) → Act B
  done b           >>=ᴬ f = f b
  newRef a k       >>=ᴬ f = newRef a λ r → k r >>=ᴬ f
  readRef r k      >>=ᴬ f = readRef r λ a → k a >>=ᴬ f
  writeRef r a k   >>=ᴬ f = writeRef r a (k >>=ᴬ f)
  register n c x k >>=ᴬ f = register n c x λ s → k s >>=ᴬ f
  send s a k       >>=ᴬ f = send s a (k >>=ᴬ f)
  finish s k       >>=ᴬ f = finish s (k >>=ᴬ f)
  startCold c s k  >>=ᴬ f = startCold c s λ h → k h >>=ᴬ f
  stop h k         >>=ᴬ f = stop h (k >>=ᴬ f)
  eff e k          >>=ᴬ f = eff e λ a → k a >>=ᴬ f
  diverge          >>=ᴬ f = diverge

  _>>ᴬ_ : ∀ {B} → Act ⊤ → Act B → Act B
  m >>ᴬ n = m >>=ᴬ λ _ → n

  private
    skipᴬ : Act ⊤
    skipᴬ = done tt

    each : ∀ {A : Set} → List A → (A → Act ⊤) → Act ⊤
    each []       f = skipᴬ
    each (x ∷ xs) f = f x >>ᴬ each xs f

    modify : ∀ {A} → Ref A → (A → A) → Act ⊤
    modify r f = readRef r λ a → writeRef r (f a) skipᴬ

    when : Bool → Act ⊤ → Act ⊤
    when b m = if b then m else skipᴬ

    noSub : Subscription
    noSub = record { unsubscribe = skipᴬ }

    -- A KILL SWITCH on one subscription.  Once `cut`, nothing more passes
    -- `guard`, and the subscription is unsubscribed — at once if it
    -- exists, or the moment it does, since a source can be cut during its
    -- own subscribe burst.  The unsubscribe is a callback, so it is kept
    -- as a registered `Sink`, the one place a `Ref` can hold one.
    record Cut : Set where
      field
        live : Ref Bool
        held : Ref (Maybe (Sink ⊤))

    newCut : ∀ {B} → (Cut → Act B) → Act B
    newCut k = newRef true λ l → newRef nothing λ h → k (record { live = l ; held = h })

    cut : Cut → Act ⊤
    cut c = writeRef (Cut.live c) false (readRef (Cut.held c) λ where
      nothing   → skipᴬ
      (just sk) → send sk tt skipᴬ)

    guard : Cut → Act ⊤ → Act ⊤
    guard c m = readRef (Cut.live c) λ b → when b m

    attach : Cut → Subscription → Act ⊤
    attach c sub = register (λ _ → Subscription.unsubscribe sub) skipᴬ (done false) λ sk →
                   writeRef (Cut.held c) (just sk) (readRef (Cut.live c) λ b →
                   if b then skipᴬ else Subscription.unsubscribe sub)

    guarded : ∀ {A} → Cut → Observer A → Observer A
    guarded c o = record { next = λ a → guard c (Observer.next o a) ; complete = guard c (Observer.complete o)
                         ; closed = readRef (Cut.live c) λ b → if b then Observer.closed o else done true }

  -- THE OPERATORS.  Each is a kernel over its children's `Subscribe`, so
  -- each is written, and later proven, on its own.  A synchronous source
  -- delivers its whole burst before its continuation runs, as an rxjs
  -- `subscribe` returns only after it.
  emptyᴷ : ∀ {A} → Subscribe A
  emptyᴷ o k = Observer.complete o >>ᴬ k noSub

  ofᴷ : ∀ {A} → List A → Subscribe A
  ofᴷ xs o k = go xs >>ᴬ k noSub
    where
      go : List _ → Act ⊤
      go []       = Observer.complete o
      go (x ∷ xs) = Observer.closed o >>=ᴬ λ c → when (not c) (Observer.next o x >>ᴬ go xs)

  mapᴷ : ∀ {A B} → (A → B) → Subscribe A → Subscribe B
  mapᴷ f s o = s (record { next = λ a → Observer.next o (f a) ; complete = Observer.complete o ; closed = Observer.closed o })

  scanᴷ : ∀ {A B} → (B → A → B) → B → Subscribe A → Subscribe B
  scanᴷ f z s o k = newRef z λ r →
    s (record { next = λ a → readRef r λ b → writeRef r (f b a) (Observer.next o (f b a))
              ; complete = Observer.complete o ; closed = Observer.closed o }) k

  -- Inclusive: the failing value leaves, then the completion, then the
  -- source is cut.
  takeWhileᴷ : ∀ {A} → (A → Bool) → Subscribe A → Subscribe A
  takeWhileᴷ p s o k = newCut λ c →
    s (guarded c (record { next = λ a → if p a then Observer.next o a
                                        else (Observer.next o a >>ᴬ Observer.complete o >>ᴬ cut c)
                         ; complete = Observer.complete o ; closed = Observer.closed o }))
      λ sub → attach c sub >>ᴬ k (record { unsubscribe = cut c })

  -- FLATTEN.  Each element's echo leaves first, then its lane is
  -- admitted.  A bounded merge queues the ELEMENT past its bound — a lane
  -- is a callback, so a `Ref` cannot hold one — and re-reads its lane
  -- when a running lane completes.  The whole completes once the outer
  -- has, with no lane running and none queued.
  --
  -- A lane completing starts the next queued one, which completes in turn:
  -- recursion through a callback.  The knot is tied in the heap, not in
  -- Agda — `refill` is a registered sink whose callback dequeues — so
  -- each runtime closes it as it closes any stored callback.
  private
    record Flat (A : Set) : Set where
      field
        active    : Ref ℕ
        outerDone : Ref Bool
        queue     : Ref (List A)
        lanes     : Ref (List Cut)
        refill    : Ref (Maybe (Sink ⊤))

    module Flatten {A B : Set} (op : FlatOp) (f : A → Maybe B × Maybe (Subscribe B)) (o : Observer B) (st : Flat A) where
      open Flat st

      settle : Act ⊤
      settle = readRef outerDone λ d → readRef active λ n → readRef queue λ q →
               when (d ∧ (n ≡ᵇ 0) ∧ null q) (Observer.complete o)

      killAll : Act ⊤
      killAll = readRef lanes λ cs → writeRef lanes [] (writeRef active 0 (each cs cut))

      -- No lane is started for a closed subscriber: that is what stops a
      -- synchronous recursion once its output is cut.
      start : Subscribe B → Act ⊤
      start l = Observer.closed o >>=ᴬ λ cl → when (not cl) (modify active suc >>ᴬ newCut λ c → modify lanes (c ∷_) >>ᴬ
        l (guarded c (record { next = Observer.next o
                             ; complete = writeRef (Cut.live c) false (modify active pred >>ᴬ readRef refill λ where
                                 nothing  → settle
                                 (just r) → send r tt skipᴬ)
                             ; closed = Observer.closed o }))
          (attach c))

      queued : Maybe (Subscribe B) → Act ⊤
      queued nothing  = settle
      queued (just l) = start l

      dequeue : Act ⊤
      dequeue = readRef queue λ where
        []       → settle
        (a ∷ as) → writeRef queue as (queued (proj₂ (f a)))

      admit : FlatOp → A → Maybe (Subscribe B) → Act ⊤
      admit _                 a nothing  = skipᴬ
      admit (mergeᶠ nothing)  a (just l) = start l
      admit (mergeᶠ (just n)) a (just l) = readRef active λ c → if c <ᵇ n then start l else modify queue (_++ [ a ])
      admit switchᶠ           a (just l) = killAll >>ᴬ start l
      admit exhaustᶠ          a (just l) = readRef active λ c → when (c ≡ᵇ 0) (start l)

      echo : Maybe B → Act ⊤
      echo nothing  = skipᴬ
      echo (just b) = Observer.next o b

      onOuter : A → Act ⊤
      onOuter a = echo (proj₁ (f a)) >>ᴬ admit op a (proj₂ (f a))

      run : Cut → Subscribe A → (Subscription → Act ⊤) → Act ⊤
      run oc s k = register (λ _ → dequeue) skipᴬ (done false) λ r → writeRef refill (just r) (
        s (guarded oc (record { next = onOuter ; complete = writeRef outerDone true settle ; closed = Observer.closed o }))
          λ sub → attach oc sub >>ᴬ k (record { unsubscribe = cut oc >>ᴬ killAll }))

  flattenᴷ : ∀ {A B} → FlatOp → (A → Maybe B × Maybe (Subscribe B)) → Subscribe A → Subscribe B
  flattenᴷ op f s o k =
    newRef 0 λ a → newRef false λ d → newRef [] λ q → newRef [] λ ls → newRef nothing λ r → newCut λ oc →
    Flatten.run op f o (record { active = a ; outerDone = d ; queue = q ; lanes = ls ; refill = r }) oc s k

  -- Allocates the subject, subscribes the body over it, THEN the source
  -- into it — body first, so the source's synchronous burst reaches
  -- whatever the body joined synchronously.  The source sees only the
  -- subject's own closing, as in rxjs: cutting the body does not stop a
  -- source still in its burst.  Each value goes to the
  -- subscribers the subject had when that value arrived, as an rxjs
  -- Subject's `next` does.  Allocated per subscription of the `connect`
  -- node, so one bound outside a `defer` is the SAME subject on every
  -- re-subscription of the deferred body.
  connectᴷ : ∀ {A B} → Subscribe A → (Subject A → Subscribe B) → Subscribe B
  connectᴷ s b o k = newRef [] λ subs → newRef false λ closed →
    b (record { subscribers = subs ; closed = closed }) o λ body →
    s (record { next = λ a → readRef subs λ ss → each ss λ sk → send sk a skipᴬ
              ; complete = writeRef closed true (readRef subs λ ss → each ss λ sk → finish sk skipᴬ)
              ; closed = readRef closed done })
      λ src → k (record { unsubscribe = Subscription.unsubscribe src >>ᴬ Subscription.unsubscribe body })

  -- Adds the sink, guarded so that unsubscribing silences it.  Nothing
  -- else: the source is already running.  Joining a completed subject
  -- completes at once.
  joinᴷ : ∀ {A} → Subject A → Subscribe A
  joinᴷ st o k = readRef (Subject.closed st) λ where
    true  → Observer.complete o >>ᴬ k noSub
    false → newRef true λ l →
      register (λ a → readRef l λ b → when b (Observer.next o a)) (readRef l λ b → when b (Observer.complete o))
               (readRef l λ b → if b then Observer.closed o else done true) λ sk →
      modify (Subject.subscribers st) (_++ [ sk ]) >>ᴬ k (record { unsubscribe = writeRef l false skipᴬ })

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
      registerᴿ  : (∀ {B} → Act B → M B) → ∀ {A} → (A → Act ⊤) → Act ⊤ → Act Bool → M (Sink A)
      sendᴿ      : (∀ {B} → Act B → M B) → ∀ {A} → Sink A → A → M ⊤
      finishᴿ    : (∀ {B} → Act B → M B) → ∀ {A} → Sink A → M ⊤
      -- Delivers the cold's subscribe burst inline, and arranges for its
      -- later emissions to reach the event queue.
      startColdᴿ : (∀ {B} → Act B → M B) → ∀ {A} → Cold A → Sink A → M Handle
      stopᴿ      : Handle → M ⊤
      effᴿ       : ∀ {A} → Eff A → M A
      divergeᴿ   : ∀ {A} → M A
      -- Runs the next timer as one cascade; false when none is left.  Both
      -- runtimes pop the earliest, ties in the order they were set, as two
      -- `setTimeout`s with one delay.
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
    interpret self (register n c x k) = registerᴿ self n c x >>= λ s → interpret self (k s)
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
