{-# OPTIONS --guardedness --large-indices #-}

-- THE ONE COPY OF THE OPERATIONAL SEMANTICS.  A program is a tree
-- (`Obs`, in `Tree`); compiling it gives `Act` programs, built from the
-- operator kernels.  Both runtimes run those same programs on the SAME
-- MACHINE (`Machine`, below): one pure transition, `conf → input → conf ×
-- outputs`, over one heap (`Heap`).  A runtime is only a DRIVER: what it
-- feeds the machine (a cold's emissions, an effect's answer) and what it
-- does with what the machine asks (start a cold, perform an effect).  The
-- pure driver plays timelines on a virtual clock (`operation.Machine`);
-- the IO driver runs real colds on a real one (`operation.Observable`).
--
-- A `defer` compiles to an `unfold`, its body compiled only when the
-- machine reaches it, so compiling is total.
--
-- The shared code is parametric in a runtime's cold and its native
-- effects, so it can neither look inside a cold nor perform IO.
module operation.AbstractObservable where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List using (List; _∷_; []; _++_; [_]; null)
open import Data.List.Relation.Unary.All using (All; _∷_; []; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)

open import denotation.MonotonicList using (Pos; Label; ix; last; root) renaming (sub to subᴾ)
open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)

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
  quiet : Ty
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
    Quiet    : World → Set            -- a stored unsubscribe, as a first-order name
    Handle   : World → Set            -- a started cold, as the runtime tracks it
    wkRef    : ∀ {w v t} (X : World → Set) → w ⊑ v → RefOf w t (X w) → RefOf v t (X v)
    wkSink   : ∀ {w v A} → w ⊑ v → Sink w A → Sink v A
    wkQuiet  : ∀ {w v} → w ⊑ v → Quiet w → Quiet v
    wkHandle : ∀ {w v} → w ⊑ v → Handle w → Handle v
    Cold     : Set → Set₁             -- the cold leaf
    Eff      : Set → Set              -- what a top-level observer may do natively

------------------------------------------------------------------------
-- THE HEAP, shared: worlds and names

-- Named, not opened, so `Prims`' fields of the same names do not clash.
module Heap where
  -- What one heap entry is: a cell, a registered observer, a stored
  -- unsubscribe, a started cold.
  data Kind : Set₁ where
    cell : Ty → Kind
    slot : Set → Kind
    hush : Kind
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

  Quiet : World → Set
  Quiet w = w ∋ hush

  Handle : World → Set
  Handle w = w ∋ play

-- A runtime's primitives: the shared heap's names, its cold, its effects.
prims : (Set → Set₁) → (Set → Set) → Prims
prims C E = record
  { World = Heap.World ; _⊑_ = Heap._⊑_ ; ⊑-refl = Heap.same ; _⨾_ = Heap._⨾_
  ; RefOf = λ w t _ → w Heap.∋ Heap.cell t ; Sink = Heap.Sink ; Quiet = Heap.Quiet ; Handle = Heap.Handle
  ; wkRef = λ _ → Heap.wk∋ ; wkSink = Heap.wk∋ ; wkQuiet = Heap.wk∋ ; wkHandle = Heap.wk∋
  ; Cold = C ; Eff = E }

module Run (P : Prims) where
  open Prims P

  El : World → Ty → Set
  El w (base X)  = X
  El w (ref t)   = RefOf w t (El w t)
  El w (sink A)  = Sink w A
  El w quiet     = Quiet w
  El w (list t)  = List (El w t)
  El w (maybe t) = Maybe (El w t)
  El w (s ⊗ t)   = El w s × El w t

  Ref : World → Ty → Set
  Ref w t = El w (ref t)

  wkEl : ∀ {w v} t → w ⊑ v → El w t → El v t
  wkEl (base X)  ρ x        = x
  wkEl (ref t)   ρ r        = wkRef (λ u → El u t) ρ r
  wkEl (sink A)  ρ s        = wkSink ρ s
  wkEl quiet     ρ t        = wkQuiet ρ t
  wkEl (list t)  ρ []       = []
  wkEl (list t)  ρ (x ∷ xs) = wkEl t ρ x ∷ wkEl (list t) ρ xs
  wkEl (maybe t) ρ nothing  = nothing
  wkEl (maybe t) ρ (just x) = just (wkEl t ρ x)
  wkEl (s ⊗ t)   ρ (x , y)  = wkEl s ρ x , wkEl t ρ y

  wkR : ∀ {w v t} → w ⊑ v → Ref w t → Ref v t
  wkR {t = t} = wkEl (ref t)

  -- A connect's subject, kept in the environment.  First-order on
  -- purpose: its subscribers are `Sink`s, not callbacks, each with the
  -- position it joined at, which places what it is delivered.  A sink joining
  -- after the source has completed is completed at once, as in rxjs.
  record Subject (A : Set) (w : World) : Set where
    field
      subscribers : Ref w (list (sink A ⊗ base Pos))
      closed      : Ref w (base Bool)

  wkSubject : ∀ {A w v} → w ⊑ v → Subject A w → Subject A v
  wkSubject ρ st = record { subscribers = wkR ρ (Subject.subscribers st) ; closed = wkR ρ (Subject.closed st) }

  Env : List Set → World → Set₁
  Env Γ w = All (λ A → Subject A w) Γ

  wkEnv : ∀ {Γ w v} → w ⊑ v → Env Γ w → Env Γ v
  wkEnv ρ []         = []
  wkEnv ρ (st ∷ sts) = wkSubject ρ st ∷ wkEnv ρ sts

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
    -- An unsubscribe, kept to run later: delivering nothing, it is not a
    -- `Sink`, whose callbacks deliver where they are run.
    stash     : ∀ {w B} → Act w ⊤ → (∀ {v} → w ⊑ v → Quiet v → Act v B) → Act w B
    cancel    : ∀ {w B} → Quiet w → Act w B → Act w B
    eff       : ∀ {w A B} → Eff A → (A → Act w B) → Act w B
    -- WHERE THE RUN IS, as `denotation.MonotonicList` places an event: a
    -- ghost the pure runtime keeps and the IO runtime ignores; nothing
    -- ever branches on it.  It is SCOPED: `under l m k` runs `m` one
    -- level down, at the position extended by `l`, and puts the position
    -- back before `k`.  So the position is always the path of labels the
    -- run is under, and no kernel ever names an absolute position.
    here      : ∀ {w B} → (Pos → Act w B) → Act w B
    under     : ∀ {w B} → Label → Act w ⊤ → Act w B → Act w B
    -- No information: what a ghost check's unfolding cut off at its
    -- budget does.  A compiled tree never reaches it.
    diverge   : ∀ {w B} → Act w B
    -- A `defer`, subscribed but not yet compiled: the tree, the connects
    -- in scope, the observer's three parts, and what to do once the
    -- subscription exists — its unsubscribe stashed, since an `Act`
    -- cannot take an `Act` as an argument — then the rest.
    unfold    : ∀ {w Γ A B} → Later Cold Γ A → Env Γ w → (A → Act w ⊤) → Act w ⊤ → Act w Bool
              → (∀ {v} → w ⊑ v → Quiet v → Act v ⊤) → Act w B → Act w B

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
  wkAct ρ (stash m k)              = stash (wkAct ρ m) λ σ → k (ρ ⨾ σ)
  wkAct ρ (cancel t k)             = cancel (wkQuiet ρ t) (wkAct ρ k)
  wkAct ρ (eff e k)                = eff e λ a → wkAct ρ (k a)
  wkAct ρ (here k)                 = here λ p → wkAct ρ (k p)
  wkAct ρ (under l m k)            = under l (wkAct ρ m) (wkAct ρ k)
  wkAct ρ diverge                  = diverge
  wkAct ρ (unfold l e n c x k m)   = unfold l (wkEnv ρ e) (λ a → wkAct ρ (n a)) (wkAct ρ c) (wkAct ρ x) (λ σ → k (ρ ⨾ σ)) (wkAct ρ m)

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

  -- Subscribe through the runtime: register the observer, hand the
  -- runtime its sink, wrap the handle.
  via : ∀ {A w} → (∀ {v} → Sink v A → (∀ {u} → v ⊑ u → Handle u → Act u ⊤) → Act v ⊤) → Subscribe A w
  via start ρ o k = register (Observer.next o) (Observer.complete o) (Observer.closed o) λ σ s →
                    start s λ τ h → k (σ ⨾ τ) (record { unsubscribe = stop h (done tt) })

  ⊥ᴷ : ∀ {A w} → Subscribe A w
  ⊥ᴷ ρ o k = diverge

  -- One level down, where `deferᴰ` puts its body: at p ++ [ ix 1 ].
  deeper : ∀ {A w} → Subscribe A w → Subscribe A w
  deeper s ρ o k = under (ix 1) (s ρ o k) (done tt)

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
  stash m k        >>=ᴬ f = stash m λ σ t → k σ t >>=ᴬ λ x → wkAct σ (f x)
  cancel t k       >>=ᴬ f = cancel t (k >>=ᴬ f)
  eff e k          >>=ᴬ f = eff e λ a → k a >>=ᴬ f
  here k           >>=ᴬ f = here λ p → k p >>=ᴬ f
  under l m k      >>=ᴬ f = under l m (k >>=ᴬ f)
  diverge          >>=ᴬ f = diverge
  unfold l e n c x k m >>=ᴬ f = unfold l e n c x k (m >>=ᴬ f)

  _>>ᴬ_ : ∀ {w B} → Act w ⊤ → Act w B → Act w B
  m >>ᴬ n = m >>=ᴬ λ _ → n

  -- The kernels' toolkit, named so that proofs about the kernels can
  -- name it too.
  module Kit where
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
    -- as a stashed `Quiet`, the one place a `Ref` can hold one.  A code,
    -- not a record, because a lane list holds them.
    cutTy : Ty
    cutTy = ref (base Bool) ⊗ ref (maybe quiet)

    Cut : World → Set
    Cut w = El w cutTy

    live : ∀ {w} → Cut w → Ref w (base Bool)
    live = proj₁

    held : ∀ {w} → Cut w → Ref w (maybe quiet)
    held = proj₂

    wkCut : ∀ {w v} → w ⊑ v → Cut w → Cut v
    wkCut = wkEl cutTy

    newCut : ∀ {w B} → (∀ {v} → w ⊑ v → Cut v → Act v B) → Act w B
    newCut k = newB true λ σ l → newRef (maybe quiet) nothing λ τ h → k (σ ⨾ τ) (wkR τ l , h)

    cut : ∀ {w} → Cut w → Act w ⊤
    cut c = writeRef (live c) false (readRef (held c) λ _ → λ where
      nothing   → skipᴬ
      (just t)  → cancel t skipᴬ)

    guard : ∀ {w} → Cut w → Act w ⊤ → Act w ⊤
    guard c m = readB (live c) λ b → when b m

    attach : ∀ {w} → Cut w → Subscription w → Act w ⊤
    attach c sub = stash (Subscription.unsubscribe sub) λ σ t →
                   writeRef (held (wkCut σ c)) (just t) (readB (live (wkCut σ c)) λ b →
                   if b then skipᴬ else Subscription.unsubscribe (wkSubn σ sub))

    guarded : ∀ {A w} → Cut w → Observer A w → Observer A w
    guarded c o = record { next = λ a → guard c (Observer.next o a) ; complete = guard c (Observer.complete o)
                         ; closed = readB (live c) λ b → if b then Observer.closed o else done true }

    -- A subscription kept stashed, unsubscribed through it.
    unsubscribeVia : ∀ {w} → Maybe (Quiet w) → Act w ⊤
    unsubscribeVia nothing  = skipᴬ
    unsubscribeVia (just t) = cancel t skipᴬ

  open Kit

  -- THE OPERATORS.  Each is a kernel over its children's `Subscribe`, so
  -- each is written, and later proven, on its own.  A synchronous source
  -- delivers its whole burst before its continuation runs, as an rxjs
  -- `subscribe` returns only after it.
  emptyᴷ : ∀ {A w} → Subscribe A w
  emptyᴷ ρ o k = under last (Observer.complete o) (k ⊑-refl noSub)

  -- Each value, then the completion, while the observer stays open: the
  -- i-th of a burst sits under `ix i`, the completion under `last`.
  emitAll : ∀ {A w} → Observer A w → ℕ → List A → Act w ⊤
  emitAll o i []       = under last (Observer.complete o) skipᴬ
  emitAll o i (x ∷ xs) = Observer.closed o >>=ᴬ λ c → when (not c) (under (ix i) (Observer.next o x) (emitAll o (suc i) xs))

  ofᴷ : ∀ {A w} → List A → Subscribe A w
  ofᴷ xs ρ o k = emitAll o 0 xs >>ᴬ k ⊑-refl noSub

  mapᴷ : ∀ {A B w} → (A → B) → Subscribe A w → Subscribe B w
  mapᴷ f s ρ o = s ρ (record { next = λ a → Observer.next o (f a) ; complete = Observer.complete o ; closed = Observer.closed o })

  scanᴷ : ∀ {A B w} → (B → A → B) → B → Subscribe A w → Subscribe B w
  scanᴷ f z s ρ o k = newB z λ σ r → let o′ = wkObs σ o in
    s (ρ ⨾ σ) (record { next = λ a → readB r λ b → writeRef r (f b a) (Observer.next o′ (f b a))
                      ; complete = Observer.complete o′ ; closed = Observer.closed o′ }) (wkKont σ k)

  -- The failing value leaves only when inclusive, under `ix 0`; then the
  -- completion under `last`, then the source is cut.  Two callbacks in
  -- one scope each get their own label.
  takeWhileᴷ : ∀ {A w} → Bool → (A → Bool) → Subscribe A w → Subscribe A w
  takeWhileᴷ i p s ρ o k = newCut λ σ c → let o′ = wkObs σ o in
    s (ρ ⨾ σ) (guarded c (record { next = λ a → if p a then Observer.next o′ a
                                               else (when i (under (ix 0) (Observer.next o′ a) skipᴬ) >>ᴬ under last (Observer.complete o′) (cut c))
                                 ; complete = Observer.complete o′ ; closed = Observer.closed o′ }))
      λ τ sub → attach (wkCut τ c) sub >>ᴬ k (σ ⨾ τ) (record { unsubscribe = cut (wkCut τ c) })

  -- FLATMAP.  Each element's lane is admitted.  A bounded merge queues the ELEMENT past its bound — a lane
  -- is a callback, so a `Ref` cannot hold one — and re-reads its lane
  -- when a running lane completes.  The whole completes once the outer
  -- has, with no lane running and none queued.
  --
  -- A lane completing starts the next queued one, which completes in turn:
  -- recursion through a callback.  The knot is tied in the heap, not in
  -- Agda — `refill` is a registered sink whose callback dequeues — so
  -- each runtime closes it as it closes any stored callback.
  module FlatKit where
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

    module FlatMap {A B : Set} {w} (op : FlatOp) (f : A → Subscribe B w) (o : Observer B w) (st : Flat A w) where
      open Flat st

      settle : Act w ⊤
      settle = readB outerDone λ d → readB active λ n → readB queue λ q →
               when (d ∧ (n ≡ᵇ 0) ∧ null q) (Observer.complete o)

      killAll : Act w ⊤
      killAll = readRef lanes λ σ cs → writeRef (wkR σ lanes) [] (writeRef (wkR σ active) 0 (each cs cut))

      -- No lane is started for a closed subscriber: that is what stops a
      -- synchronous recursion once its output is cut.
      -- A freed slot goes to the refill sink once it exists, else settles.
      handOn : ∀ {v} → w ⊑ v → Maybe (Sink v ⊤) → Act v ⊤
      handOn σ nothing  = wkAct σ settle
      handOn σ (just r) = send r tt skipᴬ

      -- A lane's observer: its completion frees its slot, and hands it on.
      lane : ∀ {v} → w ⊑ v → Cut v → Observer B v
      lane σ c = let st′ = wkFlat σ st ; o′ = wkObs σ o in
        record { next = Observer.next o′
               ; complete = writeRef (live c) false (modifyB (Flat.active st′) pred >>ᴬ readRef (Flat.refill st′) λ τ → handOn (σ ⨾ τ))
               ; closed = Observer.closed o′ }

      start : Subscribe B w → Act w ⊤
      -- A lane started where the run is is subscribed under `ix 1`.
      start l = Observer.closed o >>=ᴬ λ cl → when (not cl) (modifyB active suc >>ᴬ newCut λ σ c →
        modify (Flat.lanes (wkFlat σ st)) (λ τ cs → wkCut τ c ∷ cs) >>ᴬ under (ix 1) (l σ (guarded c (lane σ c)) λ τ → attach (wkCut τ c)) skipᴬ)

      dequeue : Act w ⊤
      dequeue = readB queue λ where
        []       → settle
        (a ∷ as) → writeRef queue as (start (f a))

      admit : FlatOp → A → Act w ⊤
      admit (mergeᶠ nothing)  a = start (f a)
      admit (mergeᶠ (just n)) a = readB active λ c → if c <ᵇ n then start (f a) else modifyB queue (_++ [ a ])
      admit switchᶠ           a = killAll >>ᴬ start (f a)
      admit exhaustᶠ          a = readB active λ c → when (c ≡ᵇ 0) (start (f a))

      run : Cut w → Subscribe A w → Kont w → Act w ⊤
      run oc s k = register (λ _ → dequeue) skipᴬ (done false) λ σ r → writeRef (Flat.refill (wkFlat σ st)) (just r) (
        s σ (guarded (wkCut σ oc) (record { next = λ a → wkAct σ (admit op a) ; complete = writeRef (Flat.outerDone (wkFlat σ st)) true (wkAct σ settle)
                                          ; closed = Observer.closed (wkObs σ o) }))
          λ τ sub → attach (wkCut (σ ⨾ τ) oc) sub >>ᴬ k (σ ⨾ τ) (record { unsubscribe = cut (wkCut (σ ⨾ τ) oc) >>ᴬ wkAct (σ ⨾ τ) killAll }))

  open FlatKit

  flatMapᴷ : ∀ {A B w} → FlatOp → (A → Subscribe B w) → Subscribe A w → Subscribe B w
  flatMapᴷ op f s ρ o k = newFlat λ σ st → newCut λ τ oc →
    FlatMap.run op (λ a → wkSub (ρ ⨾ σ ⨾ τ) (f a)) (wkObs (σ ⨾ τ) o) (wkFlat τ st) oc (wkSub (ρ ⨾ σ ⨾ τ) s) (wkKont (σ ⨾ τ) k)

  -- Allocates the subject, subscribes the body over it, THEN the source
  -- into it — body first, so the source's synchronous burst reaches
  -- whatever the body joined synchronously.  The body's completion cuts
  -- the source, as an rxjs subscriber's completion tears down what it
  -- holds — a source subscribed after that runs its burst, then is cut,
  -- and a source still in its burst runs it out.  Each value goes to the
  -- subscribers the subject had when that value arrived, as an rxjs
  -- Subject's `next` does.  Allocated per subscription of the `connect`
  -- node, so one bound outside a `defer` is the SAME subject on every
  -- re-subscription of the deferred body.
  connectᴷ : ∀ {A B w} → Subscribe A w → (∀ {v} → w ⊑ v → Subject A v → Subscribe B v) → Subscribe B w
  --
  -- The body runs under `ix 0` and the source under `ix 1`, one after the
  -- other: the source is NOT subscribed from the body's continuation,
  -- which runs inside the body's scope.  The body's subscription is kept
  -- in a cell until the source's exists.  A `Kont` never moves the
  -- position, so a continuation run inside a scope places nothing.
  connectᴷ {A} s b ρ o k = newRef (list (sink A ⊗ base Pos)) [] λ σ subs → newB false λ τ cl → newCut λ υ c →
    newRef (maybe quiet) nothing λ υ′ bodyRef →
    let st = record { subscribers = wkR (τ ⨾ υ ⨾ υ′) subs ; closed = wkR (υ ⨾ υ′) cl } ; o′ = wkObs (σ ⨾ τ ⨾ υ ⨾ υ′) o
        c′ = wkCut υ′ c in
    under (ix 0) (b (ρ ⨾ σ ⨾ τ ⨾ υ ⨾ υ′) st ⊑-refl (record { next = Observer.next o′ ; complete = Observer.complete o′ >>ᴬ cut c′ ; closed = Observer.closed o′ })
      λ π body → stash (Subscription.unsubscribe body) λ π′ t → writeRef (wkR (π ⨾ π′) bodyRef) (just t) skipᴬ)
    (under (ix 1) (s (ρ ⨾ σ ⨾ τ ⨾ υ ⨾ υ′) (record
      { next = λ a → readRef (Subject.subscribers st) λ _ ss → each ss λ j → under (subᴾ (proj₂ j)) (send (proj₁ j) a skipᴬ) skipᴬ
      ; complete = writeRef (Subject.closed st) true (readRef (Subject.subscribers st) λ _ ss →
                   each ss λ j → under (subᴾ (proj₂ j)) (finish (proj₁ j) skipᴬ) skipᴬ)
      ; closed = readB (Subject.closed st) done })
      λ ψ src → attach (wkCut ψ c′) src >>ᴬ readRef (wkR ψ bodyRef) λ ψ′ mb →
        k (σ ⨾ τ ⨾ υ ⨾ υ′ ⨾ ψ ⨾ ψ′) (record { unsubscribe = Subscription.unsubscribe (wkSubn ψ′ src) >>ᴬ unsubscribeVia mb }))
     skipᴬ)

  -- Adds the sink, guarded so that unsubscribing silences it.  Nothing
  -- else: the source is already running.  Joining a completed subject
  -- completes at once.
  joinᴷ : ∀ {A w} → Subject A w → Subscribe A w
  joinᴷ st ρ o k = here λ j → readB (Subject.closed (wkSubject ρ st)) λ where
    true  → under last (Observer.complete o) (k ⊑-refl noSub)
    false → newB true λ σ l → let o′ = wkObs σ o in
      register (λ a → readB l λ b → when b (Observer.next o′ a)) (readB l λ b → when b (Observer.complete o′))
               (readB l λ b → if b then Observer.closed o′ else done true) λ τ sk →
      modify (Subject.subscribers (wkSubject (ρ ⨾ σ ⨾ τ) st)) (λ π ss → ss ++ [ (wkSink π sk , j) ]) >>ᴬ
      k (σ ⨾ τ) (record { unsubscribe = writeRef (wkR τ l) false skipᴬ })

  -- THE TREE, COMPILED.  Structural everywhere except `defer`, which
  -- becomes an `unfold`: its body is compiled only when the runtime
  -- reaches it, so this is total whatever recursion the tree holds, and
  -- that recursion is the runtime's.
  compile : ∀ {Γ A w} → Obs Cold Γ A → Env Γ w → Subscribe A w
  compile (cold c)          ρ = via (startCold c)
  compile empty             ρ = emptyᴷ
  compile (of xs)           ρ = ofᴷ xs
  compile (map f s)         ρ = mapᴷ f (compile s ρ)
  compile (scan f z s)      ρ = scanᴷ f z (compile s ρ)
  compile (takeWhile i p s) ρ = takeWhileᴷ i p (compile s ρ)
  compile (flatMap op f s)  ρ = flatMapᴷ op (λ a → compile (f a) ρ) (compile s ρ)
  compile (connect s b)     ρ = connectᴷ (compile s ρ) λ σ st → compile b (st ∷ wkEnv σ ρ)
  compile (connected i)     ρ = joinᴷ (lookup ρ i)
  compile (defer l)         ρ σ o k = unfold l (wkEnv σ ρ) (Observer.next o) (Observer.complete o) (Observer.closed o)
                                        (λ τ t → k τ (record { unsubscribe = cancel t (done tt) })) (done tt)



------------------------------------------------------------------------
-- THE DRIVER'S SHAPE

-- A pure transition: a state, an input that state admits, what follows.
-- Both runtimes are this one transition, fed by different drivers.
record Driver (S : Set₁) (I : S → Set₁) (N : S → Set₁) : Set₁ where
  field transition : (s : S) → I s → N s

------------------------------------------------------------------------
-- THE MACHINE, shared: the one interpreter of `Act`

module Machine (C : Set → Set₁) (E : Set → Set) where
  open Heap
  open Run (prims C E)
  open Kit using (skipᴬ)

  ----------------------------------------------------------------------
  -- The heap's contents

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
  Val h hush     = Act h ⊤
  Val h play     = Lift _ Bool

  wkVal : ∀ {h v} k → h ⊑ v → Val h k → Val v k
  wkVal (cell t) ρ x  = lift (wkEl t ρ (lower x))
  wkVal (slot A) ρ cb = record { onNext = λ a → wkAct ρ (Callbacks.onNext cb a) ; onComplete = wkAct ρ (Callbacks.onComplete cb)
                               ; isClosed = wkAct ρ (Callbacks.isClosed cb) }
  wkVal hush     ρ m  = wkAct ρ m
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

  Heapᴹ : World → Set₁
  Heapᴹ h = All (Val h) h

  extend : ∀ {h k} → Heapᴹ h → Val (k ∷ h) k → Heapᴹ (k ∷ h)
  extend hp x = x ∷ wkAll new hp

  cbs : ∀ {h A} → Heapᴹ h → Sink h A → Callbacks A h
  cbs hp s = get hp s

  spent? : ∀ {h} → Heapᴹ h → Handle h → Bool
  spent? hp hd = lower (get hp hd)

  ----------------------------------------------------------------------
  -- Configurations

  -- What waits on a result of type X, made in world w.  `back`: a scope
  -- returning, its position put back.  `rehold`: a delivery the driver
  -- fed, after which the driver has the turn again.  `told`: a poll the
  -- driver fed, its answer handed out.
  data Wait (w : World) : Set → Set → Set₁ where
    rest   : ∀ {B} → Act w B → Wait w ⊤ B
    back   : ∀ {B} → Pos → Act w B → Wait w ⊤ B
    rehold : Wait w ⊤ ⊤
    told   : Wait w Bool ⊤

  -- Each frame made in its own world, linked to the one below it by how
  -- that world grew.  The bottom hands the turn to the driver for good.
  data Stack : World → Set → Set₁ where
    bottom : ∀ {w} → Stack w ⊤
    push   : ∀ {u w X Y} → Wait w X Y → u ⊑ w → Stack u Y → Stack w X

  -- What runs next in world h.  `held`: the DRIVER'S TURN — a cold's
  -- burst being played, or nothing at all over `bottom`; the driver feeds
  -- deliveries and polls, then `go` resumes the stack.  `asking`: an
  -- effect's answer awaited.
  data Ctl (h : World) : Set₁ where
    run    : ∀ {w B} → Act h B → w ⊑ h → Stack w B → Ctl h
    ret    : ∀ {w X} → X → w ⊑ h → Stack w X → Ctl h
    held   : ∀ {w} → w ⊑ h → Stack w ⊤ → Ctl h
    asking : ∀ {w X B} → E X → (X → Act h B) → w ⊑ h → Stack w B → Ctl h

  record Conf : Set₁ where
    constructor ⟨_,_,_⟩
    field
      {world} : World
      heap    : Heapᴹ world
      pos     : Pos          -- where the run is: a ghost the IO driver ignores
      ctl     : Ctl world
  open Conf

  -- What the machine asks of its driver.
  data Output (h : World) : Set₁ where
    perform  : ∀ {X} → E X → Output h                        -- run it, `answer` its result
    start    : ∀ {A} → C A → Sink h A → Handle h → Output h  -- play it into the sink: its burst now
    stopped  : Handle h → Output h                            -- tear it down
    closedIs : Bool → Output h                                -- a poll's answer

  -- What an `asking` machine waits for.
  Awaited : Conf → Set
  Awaited ⟨ _ , _ , asking {X = X} _ _ _ _ ⟩ = X
  Awaited _                                = ⊤

  -- What a driver may feed.  A delivery carries the position its
  -- emission is placed at; the IO driver passes `[]`.
  data Input (c : Conf) : Set₁ where
    go      : Input c
    answer  : Awaited c → Input c
    deliver : ∀ {A} → Sink (world c) A → A → Pos → Input c
    end     : ∀ {A} → Handle (world c) → Sink (world c) A → Pos → Input c   -- the cold completed: spent, then its sink's completion
    poll    : ∀ {A} → Sink (world c) A → Input c

  -- One transition's result: the next configuration, how the world grew,
  -- and what is asked of the driver.
  record Next (h : World) : Set₁ where
    constructor next
    field
      conf    : Conf
      grew    : h ⊑ world conf
      outputs : List (Output (world conf))

  ----------------------------------------------------------------------
  -- One transition

  still : ∀ {h} → Heapᴹ h → Pos → Ctl h → Next h
  still hp p c = next ⟨ hp , p , c ⟩ same []

  -- A `defer` reached: its body compiled one level down, as `deferᴰ`
  -- puts it, its subscription's unsubscribe stashed.
  unfolded : ∀ {h Γ A} → Later C Γ A → Env Γ h → (A → Act h ⊤) → Act h ⊤ → Act h Bool → (∀ {v} → h ⊑ v → Quiet v → Act v ⊤) → Act h ⊤
  unfolded l e n c x k = under (ix 1)
    (compile (Later.force l) e same (record { next = n ; complete = c ; closed = x }) λ σ sub →
      stash (Subscription.unsubscribe sub) λ τ t → k (σ ⨾ τ) t)
    (done tt)

  runs : ∀ {h w B} → Heapᴹ h → Pos → Act h B → w ⊑ h → Stack w B → Next h
  runs hp p (done b)            σ k = still hp p (ret b σ k)
  runs hp p (newRef t a k′)     σ k = next ⟨ extend hp (lift (wkEl t new a)) , p , run (k′ new here) (σ ⨾ new) k ⟩ new []
  runs hp p (readRef r k′)      σ k = still hp p (run (k′ same (lower (get hp r))) σ k)
  runs hp p (writeRef r a k′)   σ k = still (put hp r (lift a)) p (run k′ σ k)
  runs hp p (register n c x k′) σ k = next ⟨ extend hp (record { onNext = λ a → wkAct new (n a) ; onComplete = wkAct new c ; isClosed = wkAct new x })
                                           , p , run (k′ new here) (σ ⨾ new) k ⟩ new []
  runs hp p (send s a k′)       σ k = still hp p (run (Callbacks.onNext (cbs hp s) a) same (push (rest k′) σ k))
  runs hp p (finish s k′)       σ k = still hp p (run (Callbacks.onComplete (cbs hp s)) same (push (rest k′) σ k))
  -- The cold's burst is the driver's: it holds, feeding deliveries, until
  -- it says `go`.
  runs hp p (startCold c s k′)  σ k = next ⟨ extend hp (lift false) , p , held same (push (rest (k′ new here)) (σ ⨾ new) k) ⟩ new
                                           [ start c (wk∋ new s) here ]
  runs hp p (stop hd k′)        σ k = next ⟨ put hp hd (lift true) , p , run k′ σ k ⟩ same [ stopped hd ]
  runs hp p (stash m k′)        σ k = next ⟨ extend hp (wkAct new m) , p , run (k′ new here) (σ ⨾ new) k ⟩ new []
  runs hp p (cancel t k′)       σ k = still hp p (run (get hp t) same (push (rest k′) σ k))
  runs hp p (eff e k′)          σ k = next ⟨ hp , p , asking e k′ σ k ⟩ same [ perform e ]
  runs hp p (here k′)           σ k = still hp p (run (k′ p) σ k)
  runs hp p (under l m k′)      σ k = still hp (p ++ [ l ]) (run m same (push (back p k′) σ k))
  runs hp p diverge             σ k = still hp p (run diverge σ k)
  runs hp p (unfold l e n c x k′ m) σ k = still hp p (run (unfolded l e n c x k′) same (push (rest m) σ k))

  returns : ∀ {h w X} → Heapᴹ h → Pos → X → w ⊑ h → Stack w X → Next h
  returns hp p x σ bottom              = still hp p (held σ bottom)
  returns hp p x σ (push (rest m) ρ k)   = still hp p (run (wkAct σ m) (ρ ⨾ σ) k)
  returns hp p x σ (push (back q m) ρ k) = still hp q (run (wkAct σ m) (ρ ⨾ σ) k)
  returns hp p x σ (push rehold ρ k)     = still hp p (held (ρ ⨾ σ) k)
  returns hp p b σ (push told ρ k)       = next ⟨ hp , p , held (ρ ⨾ σ) k ⟩ same [ closedIs b ]

  -- A callback the driver fed, run while it holds: at the position fed,
  -- the old one put back, then the driver's turn again.
  fed : ∀ {h w} → Heapᴹ h → Pos → Pos → Act h ⊤ → w ⊑ h → Stack w ⊤ → Next h
  fed hp p q a σ k = still hp q (run a same (push (back p (done tt)) same (push rehold σ k)))

  transition : (c : Conf) → Input c → Next (world c)
  transition ⟨ hp , p , run a σ k ⟩      go          = runs hp p a σ k
  transition ⟨ hp , p , ret x σ k ⟩      go          = returns hp p x σ k
  transition ⟨ hp , p , held σ k ⟩       go          = returns hp p tt σ k
  transition ⟨ hp , p , asking e k′ σ k ⟩ (answer x) = still hp p (run (k′ x) σ k)
  transition ⟨ hp , p , held σ k ⟩       (deliver s a q) = fed hp p q (Callbacks.onNext (cbs hp s) a) σ k
  transition ⟨ hp , p , held σ k ⟩       (end hd s q) = fed (put hp hd (lift true)) p q (Callbacks.onComplete (cbs hp s)) σ k
  transition ⟨ hp , p , held σ k ⟩       (poll s)    = still hp p (run (Callbacks.isClosed (cbs hp s)) same (push told σ k))
  transition ⟨ hp , p , c ⟩              _           = still hp p c

  -- THE MACHINE: the one transition both drivers feed.
  machine : Driver Conf Input (λ c → Next (world c))
  machine = record { transition = transition }

  -- Subscribing at the root: the machine's first configuration.
  load : ∀ {A} → Subscribe A [] → Observer A [] → Conf
  load s o = ⟨ [] , root , run (s same o λ _ _ → done tt) same bottom ⟩
