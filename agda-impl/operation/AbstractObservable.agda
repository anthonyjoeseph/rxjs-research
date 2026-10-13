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
open import Data.List.Relation.Unary.All using (All; _∷_; []; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; Obs; cold; empty; of; map; scan; takeWhile; flatten; connect; connected; defer; Later)

------------------------------------------------------------------------
-- What a runtime supplies

-- WHAT A CELL HOLDS.  A cell may hold a ref or a sink, and the pure
-- runtime's heap must say what each holds in terms it can WEAKEN as the
-- heap grows, so the operators' state is described by codes; the user's
-- own types are `base`.  A cell can then point at a cell made after it,
-- as a lane list does at each new lane.
data Ty : Set₁ where
  base  : Set → Ty
  ref   : Ty → Ty
  sink  : Set → Ty
  list  : Ty → Ty
  maybe : Ty → Ty
  _⊗_   : Ty → Ty → Ty

-- A runtime's names live in a WORLD — what has been allocated — and stay
-- valid in every larger one (`_⊑_`).  IO has one world; the pure heap's
-- world is its typing.  `RefOf`'s last index is the decoded content,
-- which `wkRef` lets change with the world.
record Prims : Set₂ where
  infixr 5 _⨾_
  field
    World    : Set₁
    _⊑_      : World → World → Set
    ⊑-refl   : ∀ {w} → w ⊑ w
    _⨾_      : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
    RefOf    : World → Ty → Set → Set
    Sink     : World → Set → Set      -- a registered observer, as a first-order name
    Handle   : World → Set            -- a started cold, as the runtime tracks it
    wkRef    : ∀ {w v t} (X : World → Set) → w ⊑ v → RefOf w t (X w) → RefOf v t (X v)
    wkSink   : ∀ {w v A} → w ⊑ v → Sink w A → Sink v A
    wkHandle : ∀ {w v} → w ⊑ v → Handle w → Handle v
    Cold     : Set → Set₁             -- the cold leaf
    Eff      : Set → Set              -- what a top-level observer may do natively

module Run (P : Prims) where
  open Prims P

  El : World → Ty → Set
  El w (base X)  = X
  El w (ref t)   = RefOf w t (El w t)
  El w (sink A)  = Sink w A
  El w (list t)  = List (El w t)
  El w (maybe t) = Maybe (El w t)
  El w (s ⊗ t)   = El w s × El w t

  Ref : World → Ty → Set
  Ref w t = El w (ref t)

  wkEl : ∀ {w v} t → w ⊑ v → El w t → El v t
  wkEl (base X)  ρ x        = x
  wkEl (ref t)   ρ r        = wkRef (λ u → El u t) ρ r
  wkEl (sink A)  ρ s        = wkSink ρ s
  wkEl (list t)  ρ []       = []
  wkEl (list t)  ρ (x ∷ xs) = wkEl t ρ x ∷ wkEl (list t) ρ xs
  wkEl (maybe t) ρ nothing  = nothing
  wkEl (maybe t) ρ (just x) = just (wkEl t ρ x)
  wkEl (s ⊗ t)   ρ (x , y)  = wkEl s ρ x , wkEl t ρ y

  wkR : ∀ {w v t} → w ⊑ v → Ref w t → Ref v t
  wkR {t = t} = wkEl (ref t)

  -- THE OPERATORS' LANGUAGE: the free monad over the runtime's
  -- primitives.  The kernels are written in it once, and every runtime
  -- runs those same programs.
  --
  -- A callback cannot be stored in a `Ref`: `Act` would have to quantify
  -- over its own universe.  So an observer is registered with the
  -- runtime and handed back as a first-order `Sink`, which is also what
  -- lets the pure runtime be an ordinary Agda state monad — its heap
  -- holds `Act` callbacks, never its own computations.
  --
  -- Every continuation that receives a name, or a cell's content, is
  -- KRIPKE: it runs in whatever larger world the runtime has reached by
  -- then, since a callback run in between may have allocated, and what a
  -- cell holds may point at a cell newer than the reader.
  data Act : World → Set → Set₁ where
    done      : ∀ {w B} → B → Act w B
    newRef    : ∀ {w B} t → El w t → (∀ {v} → w ⊑ v → Ref v t → Act v B) → Act w B
    readRef   : ∀ {w B t} → Ref w t → (∀ {v} → w ⊑ v → El v t → Act v B) → Act w B
    writeRef  : ∀ {w B t} → Ref w t → El w t → Act w B → Act w B
    register  : ∀ {w A B} → (A → Act w ⊤) → Act w ⊤ → Act w Bool → (∀ {v} → w ⊑ v → Sink v A → Act v B) → Act w B
    send      : ∀ {w A B} → Sink w A → A → Act w B → Act w B
    finish    : ∀ {w A B} → Sink w A → Act w B → Act w B
    startCold : ∀ {w A B} → Cold A → Sink w A → (∀ {v} → w ⊑ v → Handle v → Act v B) → Act w B
    stop      : ∀ {w B} → Handle w → Act w B → Act w B
    eff       : ∀ {w A B} → Eff A → (A → Act w B) → Act w B
    -- No information: what an unfolding cut off by the pure runtime's
    -- budget does.  The IO runtime never reaches it.
    diverge   : ∀ {w B} → Act w B

  wkAct : ∀ {w v B} → w ⊑ v → Act w B → Act v B
  wkAct ρ (done b)                 = done b
  wkAct ρ (newRef t a k)           = newRef t (wkEl t ρ a) λ σ → k (ρ ⨾ σ)
  wkAct ρ (readRef r k)            = readRef (wkR ρ r) λ σ → k (ρ ⨾ σ)
  wkAct ρ (writeRef {t = t} r a k) = writeRef (wkR ρ r) (wkEl t ρ a) (wkAct ρ k)
  wkAct ρ (register n c x k)       = register (λ a → wkAct ρ (n a)) (wkAct ρ c) (wkAct ρ x) λ σ → k (ρ ⨾ σ)
  wkAct ρ (send s a k)             = send (wkSink ρ s) a (wkAct ρ k)
  wkAct ρ (finish s k)             = finish (wkSink ρ s) (wkAct ρ k)
  wkAct ρ (startCold c s k)        = startCold c (wkSink ρ s) λ σ → k (ρ ⨾ σ)
  wkAct ρ (stop h k)               = stop (wkHandle ρ h) (wkAct ρ k)
  wkAct ρ (eff e k)                = eff e λ a → wkAct ρ (k a)
  wkAct ρ diverge                  = diverge

  -- `closed` is rxjs's `subscriber.closed`: a source polls it, and stops,
  -- so a cut reaches a source still inside its own subscribe burst.
  record Observer (A : Set) (w : World) : Set₁ where
    field
      next     : A → Act w ⊤
      complete : Act w ⊤
      closed   : Act w Bool

  wkObs : ∀ {A w v} → w ⊑ v → Observer A w → Observer A v
  wkObs ρ o = record { next = λ a → wkAct ρ (Observer.next o a) ; complete = wkAct ρ (Observer.complete o)
                     ; closed = wkAct ρ (Observer.closed o) }

  record Subscription (w : World) : Set₁ where
    field unsubscribe : Act w ⊤

  wkSubn : ∀ {w v} → w ⊑ v → Subscription w → Subscription v
  wkSubn ρ s = record { unsubscribe = wkAct ρ (Subscription.unsubscribe s) }

  -- What to do once a subscription exists.
  Kont : World → Set₁
  Kont w = ∀ {v} → w ⊑ v → Subscription v → Act v ⊤

  -- Subscribing, in continuation-passing style: given an observer, and
  -- what to do once the subscription exists, describe the work — in any
  -- world reached since the subscriber was made.
  Subscribe : Set → World → Set₁
  Subscribe A w = ∀ {v} → w ⊑ v → Observer A v → Kont v → Act v ⊤

  wkKont : ∀ {w v} → w ⊑ v → Kont w → Kont v
  wkKont ρ k σ = k (ρ ⨾ σ)

  wkSub : ∀ {A w v} → w ⊑ v → Subscribe A w → Subscribe A v
  wkSub ρ s σ = s (ρ ⨾ σ)

  -- A connect's subject, kept in the environment.  First-order on
  -- purpose: its subscribers are `Sink`s, not callbacks.  A sink joining
  -- after the source has completed is completed at once, as in rxjs.
  record Subject (A : Set) (w : World) : Set where
    field
      subscribers : Ref w (list (sink A))
      closed      : Ref w (base Bool)

  wkSubject : ∀ {A w v} → w ⊑ v → Subject A w → Subject A v
  wkSubject ρ st = record { subscribers = wkR ρ (Subject.subscribers st) ; closed = wkR ρ (Subject.closed st) }

  Env : List Set → World → Set₁
  Env Γ w = All (λ A → Subject A w) Γ

  wkEnv : ∀ {Γ w v} → w ⊑ v → Env Γ w → Env Γ v
  wkEnv ρ []         = []
  wkEnv ρ (st ∷ sts) = wkSubject ρ st ∷ wkEnv ρ sts

  -- Subscribe through the runtime: register the observer, hand the
  -- runtime its sink, wrap the handle.
  via : ∀ {A w} → (∀ {v} → Sink v A → (∀ {u} → v ⊑ u → Handle u → Act u ⊤) → Act v ⊤) → Subscribe A w
  via start ρ o k = register (Observer.next o) (Observer.complete o) (Observer.closed o) λ σ s →
                    start s λ τ h → k (σ ⨾ τ) (record { unsubscribe = stop h (done tt) })

  ⊥ᴷ : ∀ {A w} → Subscribe A w
  ⊥ᴷ ρ o k = diverge

  -- Sequencing, which the free monad gets by walking its continuations.
  infixl 1 _>>=ᴬ_ _>>ᴬ_
  _>>=ᴬ_ : ∀ {w A B} → Act w A → (A → Act w B) → Act w B
  done b           >>=ᴬ f = f b
  newRef t a k     >>=ᴬ f = newRef t a λ σ r → k σ r >>=ᴬ λ x → wkAct σ (f x)
  readRef r k      >>=ᴬ f = readRef r λ σ a → k σ a >>=ᴬ λ x → wkAct σ (f x)
  writeRef r a k   >>=ᴬ f = writeRef r a (k >>=ᴬ f)
  register n c x k >>=ᴬ f = register n c x λ σ s → k σ s >>=ᴬ λ x → wkAct σ (f x)
  send s a k       >>=ᴬ f = send s a (k >>=ᴬ f)
  finish s k       >>=ᴬ f = finish s (k >>=ᴬ f)
  startCold c s k  >>=ᴬ f = startCold c s λ σ h → k σ h >>=ᴬ λ x → wkAct σ (f x)
  stop h k         >>=ᴬ f = stop h (k >>=ᴬ f)
  eff e k          >>=ᴬ f = eff e λ a → k a >>=ᴬ f
  diverge          >>=ᴬ f = diverge

  _>>ᴬ_ : ∀ {w B} → Act w ⊤ → Act w B → Act w B
  m >>ᴬ n = m >>=ᴬ λ _ → n

  private
    skipᴬ : ∀ {w} → Act w ⊤
    skipᴬ = done tt

    each : ∀ {w} {A : Set} → List A → (A → Act w ⊤) → Act w ⊤
    each []       f = skipᴬ
    each (x ∷ xs) f = f x >>ᴬ each xs f

    newB : ∀ {w B X} → X → (∀ {v} → w ⊑ v → Ref v (base X) → Act v B) → Act w B
    newB = newRef (base _)

    -- A read whose content is the user's, so needs no weakening.
    readB : ∀ {w B X} → Ref w (base X) → (X → Act w B) → Act w B
    readB r k = readRef r λ σ x → wkAct σ (k x)

    modify : ∀ {w t} → Ref w t → (∀ {v} → w ⊑ v → El v t → El v t) → Act w ⊤
    modify r f = readRef r λ σ x → writeRef (wkR σ r) (f σ x) skipᴬ

    modifyB : ∀ {w X} → Ref w (base X) → (X → X) → Act w ⊤
    modifyB r f = modify r λ _ → f

    when : ∀ {w} → Bool → Act w ⊤ → Act w ⊤
    when b m = if b then m else skipᴬ

    noSub : ∀ {w} → Subscription w
    noSub = record { unsubscribe = skipᴬ }

    -- A KILL SWITCH on one subscription.  Once `cut`, nothing more passes
    -- `guard`, and the subscription is unsubscribed — at once if it
    -- exists, or the moment it does, since a source can be cut during its
    -- own subscribe burst.  The unsubscribe is a callback, so it is kept
    -- as a registered `Sink`, the one place a `Ref` can hold one.  A code,
    -- not a record, because a lane list holds them.
    cutTy : Ty
    cutTy = ref (base Bool) ⊗ ref (maybe (sink ⊤))

    Cut : World → Set
    Cut w = El w cutTy

    live : ∀ {w} → Cut w → Ref w (base Bool)
    live = proj₁

    held : ∀ {w} → Cut w → Ref w (maybe (sink ⊤))
    held = proj₂

    wkCut : ∀ {w v} → w ⊑ v → Cut w → Cut v
    wkCut = wkEl cutTy

    newCut : ∀ {w B} → (∀ {v} → w ⊑ v → Cut v → Act v B) → Act w B
    newCut k = newB true λ σ l → newRef (maybe (sink ⊤)) nothing λ τ h → k (σ ⨾ τ) (wkR τ l , h)

    cut : ∀ {w} → Cut w → Act w ⊤
    cut c = writeRef (live c) false (readRef (held c) λ _ → λ where
      nothing   → skipᴬ
      (just sk) → send sk tt skipᴬ)

    guard : ∀ {w} → Cut w → Act w ⊤ → Act w ⊤
    guard c m = readB (live c) λ b → when b m

    attach : ∀ {w} → Cut w → Subscription w → Act w ⊤
    attach c sub = register (λ _ → Subscription.unsubscribe sub) skipᴬ (done false) λ σ sk →
                   writeRef (held (wkCut σ c)) (just sk) (readB (live (wkCut σ c)) λ b →
                   if b then skipᴬ else Subscription.unsubscribe (wkSubn σ sub))

    guarded : ∀ {A w} → Cut w → Observer A w → Observer A w
    guarded c o = record { next = λ a → guard c (Observer.next o a) ; complete = guard c (Observer.complete o)
                         ; closed = readB (live c) λ b → if b then Observer.closed o else done true }

  -- THE OPERATORS.  Each is a kernel over its children's `Subscribe`, so
  -- each is written, and later proven, on its own.  A synchronous source
  -- delivers its whole burst before its continuation runs, as an rxjs
  -- `subscribe` returns only after it.
  emptyᴷ : ∀ {A w} → Subscribe A w
  emptyᴷ ρ o k = Observer.complete o >>ᴬ k ⊑-refl noSub

  ofᴷ : ∀ {A w} → List A → Subscribe A w
  ofᴷ {A} xs {v} ρ o k = go xs >>ᴬ k ⊑-refl noSub
    where
      go : List A → Act v ⊤
      go []       = Observer.complete o
      go (x ∷ xs) = Observer.closed o >>=ᴬ λ c → when (not c) (Observer.next o x >>ᴬ go xs)

  mapᴷ : ∀ {A B w} → (A → B) → Subscribe A w → Subscribe B w
  mapᴷ f s ρ o = s ρ (record { next = λ a → Observer.next o (f a) ; complete = Observer.complete o ; closed = Observer.closed o })

  scanᴷ : ∀ {A B w} → (B → A → B) → B → Subscribe A w → Subscribe B w
  scanᴷ f z s ρ o k = newB z λ σ r → let o′ = wkObs σ o in
    s (ρ ⨾ σ) (record { next = λ a → readB r λ b → writeRef r (f b a) (Observer.next o′ (f b a))
                      ; complete = Observer.complete o′ ; closed = Observer.closed o′ }) (wkKont σ k)

  -- The failing value leaves only when inclusive; then the completion,
  -- then the source is cut.
  takeWhileᴷ : ∀ {A w} → Bool → (A → Bool) → Subscribe A w → Subscribe A w
  takeWhileᴷ i p s ρ o k = newCut λ σ c → let o′ = wkObs σ o in
    s (ρ ⨾ σ) (guarded c (record { next = λ a → if p a then Observer.next o′ a
                                               else (when i (Observer.next o′ a) >>ᴬ Observer.complete o′ >>ᴬ cut c)
                                 ; complete = Observer.complete o′ ; closed = Observer.closed o′ }))
      λ τ sub → attach (wkCut τ c) sub >>ᴬ k (σ ⨾ τ) (record { unsubscribe = cut (wkCut τ c) })

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
  Lane : Set → World → Set₁
  Lane B w = Maybe B × Maybe (Subscribe B w)

  wkLane : ∀ {B w v} → w ⊑ v → Lane B w → Lane B v
  wkLane ρ (e , nothing) = e , nothing
  wkLane ρ (e , just s)  = e , just (wkSub ρ s)

  private
    record Flat (A : Set) (w : World) : Set where
      field
        active    : Ref w (base ℕ)
        outerDone : Ref w (base Bool)
        queue     : Ref w (base (List A))
        lanes     : Ref w (list cutTy)
        refill    : Ref w (maybe (sink ⊤))

    wkFlat : ∀ {A w v} → w ⊑ v → Flat A w → Flat A v
    wkFlat ρ st = record { active = wkR ρ (Flat.active st) ; outerDone = wkR ρ (Flat.outerDone st) ; queue = wkR ρ (Flat.queue st)
                         ; lanes = wkR ρ (Flat.lanes st) ; refill = wkR ρ (Flat.refill st) }

    newFlat : ∀ {A w B} → (∀ {v} → w ⊑ v → Flat A v → Act v B) → Act w B
    newFlat k = newB 0 λ σ₁ a → newB false λ σ₂ d → newB [] λ σ₃ q → newRef (list cutTy) [] λ σ₄ ls → newRef (maybe (sink ⊤)) nothing λ σ₅ r →
      k (σ₁ ⨾ σ₂ ⨾ σ₃ ⨾ σ₄ ⨾ σ₅) (record { active = wkR (σ₂ ⨾ σ₃ ⨾ σ₄ ⨾ σ₅) a ; outerDone = wkR (σ₃ ⨾ σ₄ ⨾ σ₅) d
                                       ; queue = wkR (σ₄ ⨾ σ₅) q ; lanes = wkR σ₅ ls ; refill = r })

    module Flatten {A B : Set} {w} (op : FlatOp) (f : A → Lane B w) (o : Observer B w) (st : Flat A w) where
      open Flat st

      settle : Act w ⊤
      settle = readB outerDone λ d → readB active λ n → readB queue λ q →
               when (d ∧ (n ≡ᵇ 0) ∧ null q) (Observer.complete o)

      killAll : Act w ⊤
      killAll = readRef lanes λ σ cs → writeRef (wkR σ lanes) [] (writeRef (wkR σ active) 0 (each cs cut))

      -- No lane is started for a closed subscriber: that is what stops a
      -- synchronous recursion once its output is cut.
      start : Subscribe B w → Act w ⊤
      start l = Observer.closed o >>=ᴬ λ cl → when (not cl) (modifyB active suc >>ᴬ newCut λ σ c →
        let st′ = wkFlat σ st ; o′ = wkObs σ o in
        modify (Flat.lanes st′) (λ τ cs → wkCut τ c ∷ cs) >>ᴬ
        l σ (guarded c (record { next = Observer.next o′
                               ; complete = writeRef (live c) false (modifyB (Flat.active st′) pred >>ᴬ readRef (Flat.refill st′) λ τ → λ where
                                   nothing  → wkAct (σ ⨾ τ) settle
                                   (just r) → send r tt skipᴬ)
                               ; closed = Observer.closed o′ }))
          λ τ → attach (wkCut τ c))

      queued : Maybe (Subscribe B w) → Act w ⊤
      queued nothing  = settle
      queued (just l) = start l

      dequeue : Act w ⊤
      dequeue = readB queue λ where
        []       → settle
        (a ∷ as) → writeRef queue as (queued (proj₂ (f a)))

      admit : FlatOp → A → Maybe (Subscribe B w) → Act w ⊤
      admit _                 a nothing  = skipᴬ
      admit (mergeᶠ nothing)  a (just l) = start l
      admit (mergeᶠ (just n)) a (just l) = readB active λ c → if c <ᵇ n then start l else modifyB queue (_++ [ a ])
      admit switchᶠ           a (just l) = killAll >>ᴬ start l
      admit exhaustᶠ          a (just l) = readB active λ c → when (c ≡ᵇ 0) (start l)

      echo : Maybe B → Act w ⊤
      echo nothing  = skipᴬ
      echo (just b) = Observer.next o b

      onOuter : A → Act w ⊤
      onOuter a = echo (proj₁ (f a)) >>ᴬ admit op a (proj₂ (f a))

      run : Cut w → Subscribe A w → Kont w → Act w ⊤
      run oc s k = register (λ _ → dequeue) skipᴬ (done false) λ σ r → writeRef (Flat.refill (wkFlat σ st)) (just r) (
        s σ (guarded (wkCut σ oc) (record { next = λ a → wkAct σ (onOuter a) ; complete = writeRef (Flat.outerDone (wkFlat σ st)) true (wkAct σ settle)
                                          ; closed = Observer.closed (wkObs σ o) }))
          λ τ sub → attach (wkCut (σ ⨾ τ) oc) sub >>ᴬ k (σ ⨾ τ) (record { unsubscribe = cut (wkCut (σ ⨾ τ) oc) >>ᴬ wkAct (σ ⨾ τ) killAll }))

  flattenᴷ : ∀ {A B w} → FlatOp → (A → Lane B w) → Subscribe A w → Subscribe B w
  flattenᴷ op f s ρ o k = newFlat λ σ st → newCut λ τ oc →
    Flatten.run op (λ a → wkLane (ρ ⨾ σ ⨾ τ) (f a)) (wkObs (σ ⨾ τ) o) (wkFlat τ st) oc (wkSub (ρ ⨾ σ ⨾ τ) s) (wkKont (σ ⨾ τ) k)

  -- Allocates the subject, subscribes the body over it, THEN the source
  -- into it — body first, so the source's synchronous burst reaches
  -- whatever the body joined synchronously.  The source sees only the
  -- subject's own closing, as in rxjs: cutting the body does not stop a
  -- source still in its burst.  Each value goes to the
  -- subscribers the subject had when that value arrived, as an rxjs
  -- Subject's `next` does.  Allocated per subscription of the `connect`
  -- node, so one bound outside a `defer` is the SAME subject on every
  -- re-subscription of the deferred body.
  connectᴷ : ∀ {A B w} → Subscribe A w → (∀ {v} → w ⊑ v → Subject A v → Subscribe B v) → Subscribe B w
  connectᴷ {A} s b ρ o k = newRef (list (sink A)) [] λ σ subs → newB false λ τ cl →
    let st = record { subscribers = wkR τ subs ; closed = cl } in
    b (ρ ⨾ σ ⨾ τ) st ⊑-refl (wkObs (σ ⨾ τ) o) λ π body → let st′ = wkSubject π st in
    s (ρ ⨾ σ ⨾ τ ⨾ π) (record { next = λ a → readRef (Subject.subscribers st′) λ _ ss → each ss λ sk → send sk a skipᴬ
                              ; complete = writeRef (Subject.closed st′) true (readRef (Subject.subscribers st′) λ _ ss → each ss λ sk → finish sk skipᴬ)
                              ; closed = readB (Subject.closed st′) done })
      λ υ src → k (σ ⨾ τ ⨾ π ⨾ υ) (record { unsubscribe = Subscription.unsubscribe src >>ᴬ Subscription.unsubscribe (wkSubn υ body) })

  -- Adds the sink, guarded so that unsubscribing silences it.  Nothing
  -- else: the source is already running.  Joining a completed subject
  -- completes at once.
  joinᴷ : ∀ {A w} → Subject A w → Subscribe A w
  joinᴷ st ρ o k = readB (Subject.closed (wkSubject ρ st)) λ where
    true  → Observer.complete o >>ᴬ k ⊑-refl noSub
    false → newB true λ σ l → let o′ = wkObs σ o in
      register (λ a → readB l λ b → when b (Observer.next o′ a)) (readB l λ b → when b (Observer.complete o′))
               (readB l λ b → if b then Observer.closed o′ else done true) λ τ sk →
      modify (Subject.subscribers (wkSubject (ρ ⨾ σ ⨾ τ) st)) (λ π ss → ss ++ [ wkSink π sk ]) >>ᴬ
      k (σ ⨾ τ) (record { unsubscribe = writeRef (wkR τ l) false skipᴬ })

  -- What a `defer` turns into.  Recursion lives only here, and each
  -- runtime closes it its own way: the pure one by unfolding n times,
  -- the IO one for real.
  Deferred : Set₁
  Deferred = ∀ {Γ A w} → Later Cold Γ A → Env Γ w → Subscribe A w

  -- THE TREE, COMPILED.  Structural everywhere except `defer`, which is
  -- handed to `d`, so this is total whatever recursion the tree holds.
  mutual
    compileWith : Deferred → ∀ {Γ A w} → Obs Cold Γ A → Env Γ w → Subscribe A w
    compileWith d (cold c)         ρ = via (startCold c)
    compileWith d empty            ρ = emptyᴷ
    compileWith d (of xs)          ρ = ofᴷ xs
    compileWith d (map f s)        ρ = mapᴷ f (compileWith d s ρ)
    compileWith d (scan f z s)     ρ = scanᴷ f z (compileWith d s ρ)
    compileWith d (takeWhile i p s) ρ = takeWhileᴷ i p (compileWith d s ρ)
    compileWith d (flatten op f s) ρ = flattenᴷ op (λ a → lane d (f a) ρ) (compileWith d s ρ)
    compileWith d (connect s b)    ρ = connectᴷ (compileWith d s ρ) λ σ st → compileWith d b (st ∷ wkEnv σ ρ)
    compileWith d (connected i)    ρ = joinᴷ (lookup ρ i)
    compileWith d (defer l)        ρ = d l ρ

    -- a separate function, so Agda can see the lane is a subterm
    lane : ∀ {Γ B w} → Deferred → Maybe B × Maybe (Obs Cold Γ B) → Env Γ w → Lane B w
    lane d (e , nothing) ρ = e , nothing
    lane d (e , just l)  ρ = e , just (compileWith d l ρ)

  -- THE MONAD, and the handful of things only it can do.  This is the
  -- whole of a runtime: `Observable` supplies IO, `PureObservable` a
  -- state monad over a heap and a virtual clock.  The operations that
  -- run a stored callback take the interpreter to run it with, since the
  -- callback lives in the runtime's tables.  Those that make a name hand
  -- it to a Kripke continuation, as `Act` does.
  record Runtime : Set₂ where
    field
      M          : World → Set → Set₁
      return     : ∀ {w A} → A → M w A
      _>>=_      : ∀ {w A B} → M w A → (A → M w B) → M w B
      newRefᴿ    : ∀ {w B} t → El w t → (∀ {v} → w ⊑ v → Ref v t → M v B) → M w B
      readRefᴿ   : ∀ {w B t} → Ref w t → (∀ {v} → w ⊑ v → El v t → M v B) → M w B
      writeRefᴿ  : ∀ {w t} → Ref w t → El w t → M w ⊤
      registerᴿ  : (∀ {w B} → Act w B → M w B) → ∀ {w A B} → (A → Act w ⊤) → Act w ⊤ → Act w Bool
                 → (∀ {v} → w ⊑ v → Sink v A → M v B) → M w B
      sendᴿ      : (∀ {w B} → Act w B → M w B) → ∀ {w A} → Sink w A → A → M w ⊤
      finishᴿ    : (∀ {w B} → Act w B → M w B) → ∀ {w A} → Sink w A → M w ⊤
      -- Delivers the cold's subscribe burst inline, and arranges for its
      -- later emissions to reach the event queue.
      startColdᴿ : (∀ {w B} → Act w B → M w B) → ∀ {w A B} → Cold A → Sink w A → (∀ {v} → w ⊑ v → Handle v → M v B) → M w B
      stopᴿ      : ∀ {w} → Handle w → M w ⊤
      effᴿ       : ∀ {w A} → Eff A → M w A
      divergeᴿ   : ∀ {w A} → M w A
      -- Runs the next timer as one cascade; false when none is left.  Both
      -- runtimes pop the earliest, ties in the order they were set, as two
      -- `setTimeout`s with one delay.
      nextᴿ      : (∀ {w B} → Act w B → M w B) → ∀ {w} → M w Bool

  -- THE ENGINE: interpreter, event loop and entry point, written once.
  -- Each is one layer, open in the recursion it needs — a callback run
  -- from a table, the loop's next turn — and the runtime closes it.
  module Engine (R : Runtime) where
    open Runtime R

    RunAct : Set₁
    RunAct = ∀ {w B} → Act w B → M w B

    -- `self` runs a stored callback; everything else is structural.
    interpret : RunAct → RunAct
    interpret self (done b)           = return b
    interpret self (newRef t a k)     = newRefᴿ t a λ σ r → interpret self (k σ r)
    interpret self (readRef r k)      = readRefᴿ r λ σ a → interpret self (k σ a)
    interpret self (writeRef r a k)   = writeRefᴿ r a >>= λ _ → interpret self k
    interpret self (register n c x k) = registerᴿ self n c x λ σ s → interpret self (k σ s)
    interpret self (send s a k)       = sendᴿ self s a >>= λ _ → interpret self k
    interpret self (finish s k)       = finishᴿ self s >>= λ _ → interpret self k
    interpret self (startCold c s k)  = startColdᴿ self c s λ σ h → interpret self (k σ h)
    interpret self (stop h k)         = stopᴿ h >>= λ _ → interpret self k
    interpret self (eff e k)          = effᴿ e >>= λ a → interpret self (k a)
    interpret self diverge            = divergeᴿ

    -- One turn of the event loop; `again` is the rest of it.
    loopStep : RunAct → ∀ {w} → M w ⊤ → M w ⊤
    loopStep run again = nextᴿ run >>= λ more → if more then again else return tt

    -- Subscribe at the root, then run the loop until nothing is left.
    drive : RunAct → ∀ {w} → M w ⊤ → ∀ {A} → Subscribe A w → Observer A w → M w ⊤
    drive run loop s o = run (s ⊑-refl o λ _ _ → done tt) >>= λ _ → loop
