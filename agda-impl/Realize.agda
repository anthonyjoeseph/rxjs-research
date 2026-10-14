{-# OPTIONS --guardedness --large-indices #-}

-- REALIZING A CONFIGURATION: what the machine's state holds when the
-- meaning's configuration (`denotation.Unfold`'s `Node`) is what is
-- running, between two turns of its loop.
--
-- The machine keeps no tree.  Its heap holds cells, registered observers
-- and started colds; its queue holds timers.  So the relation is carried
-- by a witness, `Sub`: every subscription the run still reaches, with the
-- names its kernel allocated.  Which of them are open is read off the
-- heap — a spent handle, a cut flag, a subject's `closed` — and the open
-- part is the configuration (`part`), exactly, positions included.  The
-- witness carries what the meaning keeps and the run does not: a
-- connect's source as it started, which every joiner's copy and every
-- lane subscribed later starts from; a joiner's count of events dropped;
-- a cold's timeline, subscription tick and position between frames.
--
-- A registered observer is a callback, so it is related by what it is:
-- up to `_≗_`, the same program whatever world its continuations reach,
-- against the observer its kernel would build now from its parent's and
-- its own names (`Canon`).
--
-- What is no longer reachable is dropped from the witness: a lane killed
-- by a switch is unsubscribed whole, so its timers are spent and its
-- joiners silenced, and only those two leave a trace the run still
-- reads.  A spent timer is DEAD: popping it runs nothing, so the
-- simulation's measure between two shows is the number of them.
module Realize where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList using (Events; Time; Pos; From; Frame; Timeline; at; last; ix; _<ᵖ_) renaming (sub to subᴾ)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (base; module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; Kind; cell; slot; play; _∋_; Sink; Handle; same; note; fin; module Pure)
open import operation.Machine using (module Machine)

module Realizing (R : Set) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (State; Timer; Callbacks; get; cascade)
  open Machine R using (Mach; ⟨_,_⟩; turn; burst; loop)

  ------------------------------------------------------------------------
  -- The same program, whatever world its continuations reach

  -- Weakening a stored callback rebuilds its continuations, each
  -- composing the extensions, so two programs written alike differ in
  -- how their worlds were reached.  Related pointwise, never by
  -- extensionality.
  infix 4 _≗_
  data _≗_ : ∀ {w B} → Act w B → Act w B → Set₁ where
    done≗      : ∀ {w B} {b : B} → done {w} b ≗ done b
    newRef≗    : ∀ {w B} {t a} {k k′ : ∀ {v} → w ⊑ v → Ref v t → Act v B}
               → (∀ {v} (σ : w ⊑ v) r → k σ r ≗ k′ σ r) → newRef t a k ≗ newRef t a k′
    readRef≗   : ∀ {w B t} {r : Ref w t} {k k′ : ∀ {v} → w ⊑ v → El v t → Act v B}
               → (∀ {v} (σ : w ⊑ v) x → k σ x ≗ k′ σ x) → readRef r k ≗ readRef r k′
    writeRef≗  : ∀ {w B t} {r : Ref w t} {a} {k k′ : Act w B} → k ≗ k′ → writeRef r a k ≗ writeRef r a k′
    register≗  : ∀ {w A B} {n n′ : A → Act w ⊤} {c c′ x x′} {k k′ : ∀ {v} → w ⊑ v → Sink v A → Act v B}
               → (∀ a → n a ≗ n′ a) → c ≗ c′ → x ≗ x′ → (∀ {v} (σ : w ⊑ v) s → k σ s ≗ k′ σ s)
               → register n c x k ≗ register n′ c′ x′ k′
    send≗      : ∀ {w A B} {s : Sink w A} {a} {k k′ : Act w B} → k ≗ k′ → send s a k ≗ send s a k′
    finish≗    : ∀ {w A B} {s : Sink w A} {k k′ : Act w B} → k ≗ k′ → finish s k ≗ finish s k′
    startCold≗ : ∀ {w A B} {c s} {k k′ : ∀ {v} → w ⊑ v → Handle v → Act v B}
               → (∀ {v} (σ : w ⊑ v) h → k σ h ≗ k′ σ h) → startCold {A = A} c s k ≗ startCold c s k′
    stop≗      : ∀ {w B} {h : Handle w} {k k′ : Act w B} → k ≗ k′ → stop h k ≗ stop h k′
    eff≗       : ∀ {w B X} {e} {k k′ : X → Act w B} → (∀ a → k a ≗ k′ a) → eff e k ≗ eff e k′
    here≗      : ∀ {w B} {k k′ : Pos → Act w B} → (∀ p → k p ≗ k′ p) → here k ≗ here k′
    goto≗      : ∀ {w B} {p} {k k′ : Act w B} → k ≗ k′ → goto p k ≗ goto p k′
    diverge≗   : ∀ {w B} → diverge {w} {B} ≗ diverge
    unfold≗    : ∀ {w Γ A B} {l : Later Timeline Γ A} {e} {n n′ : A → Act w ⊤} {c c′ x x′} {k k′ : ∀ {v} → w ⊑ v → Sink v ⊤ → Act v ⊤} {m m′ : Act w B}
               → (∀ a → n a ≗ n′ a) → c ≗ c′ → x ≗ x′ → (∀ {v} (σ : w ⊑ v) s → k σ s ≗ k′ σ s) → m ≗ m′
               → unfold l e n c x k m ≗ unfold l e n′ c′ x′ k′ m′

  -- A registered observer, part for part.
  CbRel : ∀ {A h} → Callbacks A h → Callbacks A h → Set₁
  CbRel c c′ = (∀ a → Callbacks.onNext c a ≗ Callbacks.onNext c′ a)
             × Callbacks.onComplete c ≗ Callbacks.onComplete c′ × Callbacks.isClosed c ≗ Callbacks.isClosed c′

  ------------------------------------------------------------------------
  -- The observers a kernel builds, in the world the run has reached

  module Canon {h : World} where
    cbOf : ∀ {A} → Observer A h → Callbacks A h
    cbOf o = record { onNext = Observer.next o ; onComplete = Observer.complete o ; isClosed = Observer.closed o }

    mapO : ∀ {A B} → (A → B) → Observer B h → Observer A h
    mapO f o = record { next = λ a → Observer.next o (f a) ; complete = Observer.complete o ; closed = Observer.closed o }

    scanO : ∀ {A B} → (B → A → B) → Ref h (base B) → Observer B h → Observer A h
    scanO f r o = record { next = λ a → readB r λ b → writeRef r (f b a) (Observer.next o (f b a))
                         ; complete = Observer.complete o ; closed = Observer.closed o }

    takeWhileO : ∀ {A} → Bool → (A → Bool) → Cut h → Observer A h → Observer A h
    takeWhileO i p c o = guarded c (record
      { next = λ a → here λ q → if p a then Observer.next o a
                                else (when i (Observer.next o a) >>ᴬ goto (q ++ [ last ]) (Observer.complete o) >>ᴬ cut c)
      ; complete = Observer.complete o ; closed = Observer.closed o })

    -- What `attach` registers, and what a `defer` registers: the
    -- subscription's unsubscribe.
    attachCb : Act h ⊤ → Callbacks ⊤ h
    attachCb u = record { onNext = λ _ → u ; onComplete = skipᴬ ; isClosed = done false }

    -- A connect's body: its completion cuts the source.
    bodyO : ∀ {B} → Cut h → Observer B h → Observer B h
    bodyO c o = record { next = Observer.next o ; complete = Observer.complete o >>ᴬ cut c ; closed = Observer.closed o }

    -- A connect's source feeds its subject.
    feeder : ∀ {A} → Subject A h → Observer A h
    feeder S = record
      { next = λ a → here λ q → readRef (Subject.subscribers S) λ _ ss → each ss λ j → goto (q ++ [ subᴾ (proj₂ j) ]) (send (proj₁ j) a skipᴬ)
      ; complete = here λ c → writeRef (Subject.closed S) true (readRef (Subject.subscribers S) λ _ ss →
                   each ss λ j → goto (c ++ [ subᴾ (proj₂ j) ]) (finish (proj₁ j) skipᴬ))
      ; closed = readB (Subject.closed S) done }

    -- What a join registers, silenced once its flag drops.
    joinerCb : ∀ {A} → Ref h (base Bool) → Observer A h → Callbacks A h
    joinerCb l o = record { onNext = λ a → readB l λ b → when b (Observer.next o a)
                          ; onComplete = readB l λ b → when b (Observer.complete o)
                          ; isClosed = readB l λ b → if b then Observer.closed o else done true }

    -- A flatMap's, over its cells.
    module Flat′ {Δ A B} (op : T.FlatOp) (f : A → Obs Timeline Δ B) (E : Env Δ h) (o : Observer B h) (fl : Flat A h) where
      open FlatMap op (λ a → compile (f a) E) o fl public

      outerO : Cut h → Observer A h
      outerO oc = guarded oc (record { next = admit op ; complete = writeRef (Flat.outerDone fl) true settle ; closed = Observer.closed o })

      laneO : Cut h → Observer B h
      laneO c = guarded c (lane same c)

      refillCb : Callbacks ⊤ h
      refillCb = record { onNext = λ _ → dequeue ; onComplete = skipᴬ ; isClosed = done false }

  open Canon

  -- Cuts every lane in flight, over a flatMap's cells alone.
  killAllᶜ : ∀ {A h} → Flat A h → Act h ⊤
  killAllᶜ fl = readRef (Flat.lanes fl) λ σ cs → writeRef (wkR σ (Flat.lanes fl)) [] (writeRef (wkR σ (Flat.active fl)) 0 (each cs cut))

  ------------------------------------------------------------------------
  -- Every subscription the run still reaches, with its names

  -- A started cold, subscribed at tick `τ`: between frames, its timeline
  -- from the frame it waits for, the frame's timer set at `e`; its frame
  -- at `t` popped from the queue and not yet stepped; at step `i` of the
  -- frame at `r`.
  data Phase (A : Set) : Set where
    waiting : ∀ {u} → Time → Pos → From A u → Phase A
    popped  : ∀ {u} → Time → Pos → (t : Time) → u ≤ t → Frame A t → Phase A
    playing : ∀ {t} → Time → Pos → ℕ → Frame A t → Phase A

  mutual
    data Sub (h : World) : List Set → Set → Set₁ where
      coldˢ      : ∀ {Δ A} → Sink h A → Handle h → Phase A → Sub h Δ A
      -- A subscription with nothing left: `empty`, `of`, a join after the
      -- subject completed.
      doneˢ      : ∀ {Δ A} → Sub h Δ A
      mapˢ       : ∀ {Δ A B} → (A → B) → Sub h Δ A → Sub h Δ B
      scanˢ      : ∀ {Δ A B} → (B → A → B) → Ref h (base B) → Sub h Δ A → Sub h Δ B
      -- Its kill switch, the unsubscribe `attach` registered, the source.
      takeWhileˢ : ∀ {Δ A} → Bool → (A → Bool) → Cut h → Sink h ⊤ → Sub h Δ A → Sub h Δ A
      -- Its cells, the outer's kill switch and attached unsubscribe, the
      -- refill sink, the outer, and the lanes its `lanes` cell lists.
      flatMapˢ   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Sink h ⊤ → Sink h ⊤
                 → Sub h Δ A → List (Lane h Δ B) → Sub h Δ B
      -- The subject, the source's kill switch and attached unsubscribe,
      -- the source as it started, the source, the body.
      connectˢ   : ∀ {Δ A B} → Subject A h → Cut h → Sink h ⊤ → U.Node A → Sub h Δ A → Sub h (A ∷ Δ) B → Sub h Δ B
      -- Joined at `j`, `i` of the source's events dropped: the registered
      -- sink and its flag.
      joinˢ      : ∀ {Δ A} → Pos → ℕ → Sink h A → Ref h (base Bool) → A ∈ Δ → Sub h Δ A
      -- A `defer` reached: the unsubscribe it registered, its body.
      deferˢ     : ∀ {Δ A} → Sink h ⊤ → Sub h Δ A → Sub h Δ A

    record Lane (h : World) (Δ : List Set) (B : Set) : Set₁ where
      inductive
      constructor lane
      field
        switch   : Cut h
        detacher : Sink h ⊤
        inner    : Sub h Δ B

  -- WHAT UNSUBSCRIBING DOES, as each kernel's subscription says.
  unsub : ∀ {h Δ A} → Sub h Δ A → Act h ⊤
  unsub (coldˢ s hd _)                   = stop hd (done tt)
  unsub doneˢ                            = skipᴬ
  unsub (mapˢ f s)                       = unsub s
  unsub (scanˢ f r s)                    = unsub s
  unsub (takeWhileˢ i p c k s)           = cut c
  unsub (flatMapˢ op f fl oc k r so ls)  = cut oc >>ᴬ killAllᶜ fl
  unsub (connectˢ S c k s₀ src body)     = unsub src >>ᴬ unsub body
  unsub (joinˢ j i sk l x)               = writeRef l false skipᴬ
  unsub (deferˢ k s)                     = send k tt (done tt)

  -- What a name names.
  Name : World → Set₁
  Name h = Σ Kind (h ∋_)

  cutNames : ∀ {h} → Cut h → List (Name h)
  cutNames c = (cell (base Bool) , Kit.live c) ∷ (cell _ , Kit.held c) ∷ []

  subjectNames : ∀ {A h} → Subject A h → List (Name h)
  subjectNames S = (cell _ , Subject.subscribers S) ∷ (cell _ , Subject.closed S) ∷ []

  flatNames : ∀ {A h} → Flat A h → List (Name h)
  flatNames fl = (cell _ , Flat.active fl) ∷ (cell _ , Flat.outerDone fl) ∷ (cell _ , Flat.queue fl) ∷ (cell _ , Flat.lanes fl)
               ∷ (cell _ , Flat.refill fl) ∷ []

  -- EVERY NAME A SUBSCRIPTION'S KERNEL ALLOCATED.
  mutual
    names : ∀ {h Δ A} → Sub h Δ A → List (Name h)
    names (coldˢ s hd _)                  = (slot _ , s) ∷ (play , hd) ∷ []
    names doneˢ                           = []
    names (mapˢ f s)                      = names s
    names (scanˢ f r s)                   = (cell _ , r) ∷ names s
    names (takeWhileˢ i p c k s)          = cutNames c ++ (slot _ , k) ∷ names s
    names (flatMapˢ op f fl oc k r so ls) = flatNames fl ++ cutNames oc ++ (slot _ , k) ∷ (slot _ , r) ∷ names so ++ laneNames ls
    names (connectˢ S c k s₀ src body)    = subjectNames S ++ cutNames c ++ (slot _ , k) ∷ names src ++ names body
    names (joinˢ j i sk l x)              = (slot _ , sk) ∷ (cell _ , l) ∷ []
    names (deferˢ k s)                    = (slot _ , k) ∷ names s

    laneNames : ∀ {h Δ B} → List (Lane h Δ B) → List (Name h)
    laneNames []                  = []
    laneNames (lane c k s ∷ ls)   = cutNames c ++ (slot _ , k) ∷ names s ++ laneNames ls

  -- The frame a cold waits for, as the timer that should be queued.
  timerOf : ∀ {h A} → Sink h A → Handle h → Phase A → List (Timer h)
  timerOf s hd (waiting τ e (at t _ b)) = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
  timerOf s hd (waiting τ e _)          = []
  timerOf s hd (popped _ _ _ _ _)       = []
  timerOf s hd (playing _ _ _ _)        = []

  -- The configuration a cold's phase is.
  nodeOf : ∀ {A} → Phase A → U.Node A
  nodeOf (waiting τ e m)     = U.framesᶜ τ e m
  nodeOf (popped τ e t le b) = U.framesᶜ τ e (at t le b)
  nodeOf (playing τ r i b)   = U.burstᶜ τ r i b

  -- A frame the machine is bursting: its cold's sink and handle, the tick
  -- its timeline was subscribed at, the frame's position, the step it
  -- stands before, what is left of it.
  record Firing (h : World) : Set₁ where
    constructor firing
    field
      {A}    : Set
      {u}    : Time
      sink   : Sink h A
      handle : Handle h
      since  : Time
      at′    : Pos
      index  : ℕ
      frame  : Frame A u

  firingOf : ∀ {h A} → Sink h A → Handle h → Phase A → List (Firing h)
  firingOf s hd (waiting _ _ _)     = []
  firingOf s hd (popped τ e t le b) = firing s hd τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 b ∷ []
  firingOf s hd (playing τ r i b)   = firing s hd τ r i b ∷ []

  -- The frames being burst.
  mutual
    firings : ∀ {h Δ A} → Sub h Δ A → List (Firing h)
    firings (coldˢ s hd ph)                 = firingOf s hd ph
    firings doneˢ                           = []
    firings (mapˢ f s)                      = firings s
    firings (scanˢ f r s)                   = firings s
    firings (takeWhileˢ i p c k s)          = firings s
    firings (flatMapˢ op f fl oc k r so ls) = firings so ++ laneFirings ls
    firings (connectˢ S c k s₀ src body)    = firings src ++ firings body
    firings (joinˢ j i sk l x)              = []
    firings (deferˢ k s)                    = firings s

    laneFirings : ∀ {h Δ B} → List (Lane h Δ B) → List (Firing h)
    laneFirings []                = []
    laneFirings (lane c k s ∷ ls) = firings s ++ laneFirings ls

  -- The frames pending.
  mutual
    pendings : ∀ {h Δ A} → Sub h Δ A → List (Timer h)
    pendings (coldˢ s hd ph)                     = timerOf s hd ph
    pendings doneˢ                               = []
    pendings (mapˢ f s)                          = pendings s
    pendings (scanˢ f r s)                       = pendings s
    pendings (takeWhileˢ i p c k s)              = pendings s
    pendings (flatMapˢ op f fl oc k r so ls)     = pendings so ++ lanePendings ls
    pendings (connectˢ S c k s₀ src body)        = pendings src ++ pendings body
    pendings (joinˢ j i sk l x)                  = []
    pendings (deferˢ k s)                        = pendings s

    lanePendings : ∀ {h Δ B} → List (Lane h Δ B) → List (Timer h)
    lanePendings []                = []
    lanePendings (lane c k s ∷ ls) = pendings s ++ lanePendings ls

  -- WHERE A COLD SITS in a witness, and the witness with its phase moved.
  mutual
    data Spot {h} : ∀ {Δ A B} → Sub h Δ A → Sink h B → Handle h → Set₁ where
      cold-here : ∀ {Δ A} {s : Sink h A} {hd ph} → Spot {Δ = Δ} (coldˢ s hd ph) s hd
      in-map    : ∀ {Δ A B C} {f : A → B} {t : Sub h Δ A} {s : Sink h C} {hd} → Spot t s hd → Spot (mapˢ f t) s hd
      in-scan   : ∀ {Δ A B C} {f : B → A → B} {r} {t : Sub h Δ A} {s : Sink h C} {hd} → Spot t s hd → Spot (scanˢ f r t) s hd
      in-take   : ∀ {Δ A C} {i p c k} {t : Sub h Δ A} {s : Sink h C} {hd} → Spot t s hd → Spot (takeWhileˢ i p c k t) s hd
      in-outer  : ∀ {Δ A B C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {s : Sink h C} {hd}
                → Spot t s hd → Spot (flatMapˢ op f fl oc k r t ls) s hd
      in-lanes  : ∀ {Δ A B C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {s : Sink h C} {hd}
                → SpotLanes ls s hd → Spot (flatMapˢ op f fl oc k r t ls) s hd
      in-source : ∀ {Δ A B C} {S c k s₀} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B} {s : Sink h C} {hd}
                → Spot t s hd → Spot (connectˢ S c k s₀ t u) s hd
      in-body   : ∀ {Δ A B C} {S c k s₀} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B} {s : Sink h C} {hd}
                → Spot u s hd → Spot (connectˢ S c k s₀ t u) s hd
      in-defer  : ∀ {Δ A C} {k} {t : Sub h Δ A} {s : Sink h C} {hd} → Spot t s hd → Spot (deferˢ k t) s hd

    data SpotLanes {h} : ∀ {Δ B C} → List (Lane h Δ B) → Sink h C → Handle h → Set₁ where
      this-lane : ∀ {Δ B C} {c k} {t : Sub h Δ B} {ls} {s : Sink h C} {hd} → Spot t s hd → SpotLanes (lane c k t ∷ ls) s hd
      next-lane : ∀ {Δ B C} {l} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → SpotLanes (l ∷ ls) s hd

  mutual
    setAt : ∀ {h Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Phase B → Sub h Δ A
    setAt (cold-here {s = s} {hd})                                    ph = coldˢ s hd ph
    setAt (in-map {f = f} p)                                          ph = mapˢ f (setAt p ph)
    setAt (in-scan {f = f} {r} p)                                     ph = scanˢ f r (setAt p ph)
    setAt (in-take {i = i} {q} {c} {k} p)                             ph = takeWhileˢ i q c k (setAt p ph)
    setAt (in-outer {op = op} {f} {fl} {oc} {k} {r} {ls = ls} p)      ph = flatMapˢ op f fl oc k r (setAt p ph) ls
    setAt (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t} p)            ph = flatMapˢ op f fl oc k r t (setAtLanes p ph)
    setAt (in-source {S = S} {c} {k} {s₀} {u = u} p)                  ph = connectˢ S c k s₀ (setAt p ph) u
    setAt (in-body {S = S} {c} {k} {s₀} {t} p)                        ph = connectˢ S c k s₀ t (setAt p ph)
    setAt (in-defer {k = k} p)                                        ph = deferˢ k (setAt p ph)

    setAtLanes : ∀ {h Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Phase C → List (Lane h Δ B)
    setAtLanes (this-lane {c = c} {k} {ls = ls} p) ph = lane c k (setAt p ph) ∷ ls
    setAtLanes (next-lane {l = l} p)               ph = l ∷ setAtLanes p ph

  private
    one : ∀ {X : Set₁} {x : X} xs ys → xs ++ ys ≡ x ∷ [] → (xs ≡ x ∷ [] × ys ≡ []) ⊎ (xs ≡ [] × ys ≡ x ∷ [])
    one []           ys e    = inj₂ (refl , e)
    one (_ ∷ [])     []  refl = inj₁ (refl , refl)
    one (_ ∷ [])     (_ ∷ _) ()
    one (_ ∷ _ ∷ _)  ys  ()

  -- The one frame being burst, found.
  mutual
    spot-of : ∀ {h Δ A} (t : Sub h Δ A) {f} → firings t ≡ f ∷ [] → Spot t (Firing.sink f) (Firing.handle f)
    spot-of (coldˢ s hd (waiting _ _ _))    ()
    spot-of (coldˢ s hd (popped _ _ _ _ _)) refl = cold-here
    spot-of (coldˢ s hd (playing _ _ _ _))  refl = cold-here
    spot-of doneˢ                           ()
    spot-of (mapˢ f t)                      e = in-map (spot-of t e)
    spot-of (scanˢ f r t)                   e = in-scan (spot-of t e)
    spot-of (takeWhileˢ i p c k t)          e = in-take (spot-of t e)
    spot-of (flatMapˢ op f fl oc k r so ls) e with one (firings so) (laneFirings ls) e
    ... | inj₁ (e′ , _) = in-outer (spot-of so e′)
    ... | inj₂ (_ , e′) = in-lanes (spot-lanes ls e′)
    spot-of (connectˢ S c k s₀ src body)    e with one (firings src) (firings body) e
    ... | inj₁ (e′ , _) = in-source (spot-of src e′)
    ... | inj₂ (_ , e′) = in-body (spot-of body e′)
    spot-of (joinˢ j i sk l x)              ()
    spot-of (deferˢ k t)                    e = in-defer (spot-of t e)

    spot-lanes : ∀ {h Δ B} (ls : List (Lane h Δ B)) {f} → laneFirings ls ≡ f ∷ [] → SpotLanes ls (Firing.sink f) (Firing.handle f)
    spot-lanes []                ()
    spot-lanes (lane c k t ∷ ls) e with one (firings t) (laneFirings ls) e
    ... | inj₁ (e′ , _) = this-lane (spot-of t e′)
    ... | inj₂ (_ , e′) = next-lane (spot-lanes ls e′)

  -- A subject the tree holds, and a joiner of one.
  record Joiner (h : World) : Set₁ where
    constructor joiner
    field
      {A}     : Set
      subject : Subject A h
      sink′   : Sink h A
      at′     : Pos

  mutual
    subjects : ∀ {h Δ A} → Sub h Δ A → List (Σ Set λ A → Subject A h)
    subjects (coldˢ s hd _)                  = []
    subjects doneˢ                           = []
    subjects (mapˢ f s)                      = subjects s
    subjects (scanˢ f r s)                   = subjects s
    subjects (takeWhileˢ i p c k s)          = subjects s
    subjects (flatMapˢ op f fl oc k r so ls) = subjects so ++ laneSubjects ls
    subjects (connectˢ S c k s₀ src body)    = (_ , S) ∷ subjects src ++ subjects body
    subjects (joinˢ j i sk l x)              = []
    subjects (deferˢ k s)                    = subjects s

    laneSubjects : ∀ {h Δ B} → List (Lane h Δ B) → List (Σ Set λ A → Subject A h)
    laneSubjects []                = []
    laneSubjects (lane c k s ∷ ls) = subjects s ++ laneSubjects ls

  mutual
    joiners : ∀ {h Δ A} → Sub h Δ A → Env Δ h → List (Joiner h)
    joiners (coldˢ s hd _)                  E = []
    joiners doneˢ                           E = []
    joiners (mapˢ f s)                      E = joiners s E
    joiners (scanˢ f r s)                   E = joiners s E
    joiners (takeWhileˢ i p c k s)          E = joiners s E
    joiners (flatMapˢ op f fl oc k r so ls) E = joiners so E ++ laneJoiners ls E
    joiners (connectˢ S c k s₀ src body)    E = joiners src E ++ joiners body (S ∷ E)
    joiners (joinˢ j i sk l x)              E = joiner (lookup E x) sk j ∷ []
    joiners (deferˢ k s)                    E = joiners s E

    laneJoiners : ∀ {h Δ B} → List (Lane h Δ B) → Env Δ h → List (Joiner h)
    laneJoiners []                E = []
    laneJoiners (lane c k s ∷ ls) E = joiners s E ++ laneJoiners ls E

  ------------------------------------------------------------------------
  -- Against a heap

  module At {h : World} (H : All (Pure.Val R h) h) where
    val : ∀ {t} → Ref h t → El h t
    val r = lower (get H r)

    spentʰ : Handle h → Bool
    spentʰ hd = lower (get H hd)

    -- A registered observer, up to `_≗_` against `c`.
    slotIs : ∀ {A} → Sink h A → Callbacks A h → Set₁
    slotIs s c = CbRel (get H s) c

    -- An unsubscribe attached to a kill switch.
    heldIs : Cut h → Sink h ⊤ → Act h ⊤ → Set₁
    heldIs c k u = val (Kit.held c) ≡ just k × slotIs k (attachCb u)

    mapᴹ : ∀ {X Y : Set₁} → (X → Y) → Maybe X → Maybe Y
    mapᴹ f nothing  = nothing
    mapᴹ f (just x) = just (f x)

    consᴹ : ∀ {X : Set₁} → Maybe X → List X → List X
    consᴹ nothing  xs = xs
    consᴹ (just x) xs = x ∷ xs

    -- A flatMap is open while its outer, a lane or the queue is.
    merged : ∀ {A B} → T.FlatOp → (A → Pos → U.Node B) → Maybe (U.Node A) → List (U.Node B) → List A → Maybe (U.Node B)
    merged op g nothing []       []       = nothing
    merged op g o       ls       qs       = just (U.flatMapᶜ op g o ls qs)

    -- A connect is open while its body is; once its source has completed
    -- the body runs alone, as the meaning drops a completed source.
    connected : ∀ {A B} → Maybe (U.Node A) → Maybe (U.Node B) → Maybe (U.Node B)
    connected s        nothing  = nothing
    connected (just s) (just b) = just (U.connectᶜ b s)
    connected nothing  (just b) = just b

    -- The lanes still open.
    count : ∀ {Δ B} → List (Lane h Δ B) → ℕ
    count []                = 0
    count (lane c _ _ ∷ ls) = if val (Kit.live c) then suc (count ls) else count ls

    switches : ∀ {Δ B} → List (Lane h Δ B) → List (Cut h)
    switches []                = []
    switches (lane c _ _ ∷ ls) = c ∷ switches ls

    -- Each connect in scope, its source as it stands now: a joiner's copy
    -- has caught up with it between turns.
    Now : List Set → Set₁
    Now = All (λ A → Maybe (U.Node A))

    ----------------------------------------------------------------------
    -- What is still open: the configuration, exactly

    mutual
      part : ∀ {Δ A} → Sub h Δ A → Env Δ h → Srcs Δ → Now Δ → Maybe (U.Node A)
      part (coldˢ s hd ph)                 E ρ ν = if spentʰ hd then nothing else just (nodeOf ph)
      part doneˢ                           E ρ ν = nothing
      part (mapˢ f s)                      E ρ ν = mapᴹ (U.mapᶜ f) (part s E ρ ν)
      part (scanˢ f r s)                   E ρ ν = mapᴹ (U.scanᶜ f (val r)) (part s E ρ ν)
      part (takeWhileˢ i p c k s)          E ρ ν = if val (Kit.live c) then mapᴹ (U.takeWhileᶜ i p) (part s E ρ ν) else nothing
      part (flatMapˢ op f fl oc k r so ls) E ρ ν =
        merged op (λ a q → U.subscribe (f a) ρ q) (part so E ρ ν) (partLanes ls E ρ ν) (val (Flat.queue fl))
      part (connectˢ S c k s₀ src body)    E ρ ν = connected s′ (part body (S ∷ E) (s₀ ∷ ρ) (s′ ∷ ν))
        where s′ = part src E ρ ν
      part (joinˢ j i sk l x)              E ρ ν = joining (val l) (lookup ν x)
        where joining : Bool → Maybe (U.Node _) → Maybe (U.Node _)
              joining true (just c) = just (U.joinᶜ j i c)
              joining _    _        = nothing
      part (deferˢ k s)                    E ρ ν = part s E ρ ν

      partLanes : ∀ {Δ B} → List (Lane h Δ B) → Env Δ h → Srcs Δ → Now Δ → List (U.Node B)
      partLanes []                E ρ ν = []
      partLanes (lane c k s ∷ ls) E ρ ν = if val (Kit.live c) then consᴹ (part s E ρ ν) (partLanes ls E ρ ν) else partLanes ls E ρ ν

    ----------------------------------------------------------------------
    -- Every subscription against its kernel

    mutual
      Holds : ∀ {Δ A} → Sub h Δ A → Env Δ h → Observer A h → Set₁
      Holds (coldˢ s hd p)                  E o = slotIs s (cbOf o)
      Holds doneˢ                           E o = Lift _ ⊤
      Holds (mapˢ f s)                      E o = Holds s E (mapO f o)
      Holds (scanˢ f r s)                   E o = Holds s E (scanO f r o)
      Holds (takeWhileˢ i p c k s)          E o = heldIs c k (unsub s) × Holds s E (takeWhileO i p c o)
      Holds (flatMapˢ op f fl oc k r so ls) E o =
        val (Flat.refill fl) ≡ just r × slotIs r (Flat′.refillCb op f E o fl)
        × heldIs oc k (unsub so) × Holds so E (Flat′.outerO op f E o fl oc)
        × val (Flat.active fl) ≡ count ls
        × val (Flat.lanes fl) ≡ switches ls
        × HoldsLanes op f E o fl ls
      Holds (connectˢ S c k s₀ src body)    E o =
        heldIs c k (unsub src) × Holds src E (feeder S) × Holds body (S ∷ E) (bodyO c o)
      Holds (joinˢ j i sk l x)              E o = slotIs sk (joinerCb l o)
      Holds (deferˢ k s)                    E o = slotIs k (attachCb (unsub s)) × Holds s E o

      HoldsLanes : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Env Δ h → Observer B h → Flat A h → List (Lane h Δ B) → Set₁
      HoldsLanes op f E o fl []                = Lift _ ⊤
      HoldsLanes op f E o fl (lane c k s ∷ ls) = heldIs c k (unsub s) × Holds s E (Flat′.laneO op f E o fl c) × HoldsLanes op f E o fl ls

    ----------------------------------------------------------------------
    -- The queue, the subjects

    -- Every live timer is a pending frame's, and every pending frame of a
    -- cold not spent is queued.
    Timed : List (Timer h) → List (Timer h) → Set₁
    Timed ts ps = All (λ tm → spentʰ (Timer.handle tm) ≡ true ⊎ tm ∈ ps) ts
                × All (λ tm → spentʰ (Timer.handle tm) ≡ false → tm ∈ ts) ps

    -- A subscriber no joiner the tree holds: silenced for good.
    Silenced : ∀ {A} → Sink h A × Pos → Set₁
    Silenced {A} (sk , j) = Σ (Ref h (base Bool)) λ l → Σ (Observer A h) λ o → val l ≡ false × slotIs sk (joinerCb l o)

    -- Every subject's subscribers are its joiners, in the order they
    -- joined, and those the tree no longer holds, silenced.
    Joined : List (Σ Set λ A → Subject A h) → List (Joiner h) → Set₁
    Joined ss js = All (λ { (A , S) → let xs = val (Subject.subscribers S) in
                          All (λ { (sk , j) → joiner S sk j ∈ js ⊎ Silenced (sk , j) }) xs
                        × Linked (λ x y → proj₂ x <ᵖ proj₂ y ≡ true) xs }) ss
                 × All (λ { (joiner S sk j) → (sk , j) ∈ val (Subject.subscribers S) }) js

  ------------------------------------------------------------------------
  -- THE ORDER, THE ROOT

  -- Timers in the order their cascades sit, each due no earlier than
  -- now, its cascade past where the run is.
  Ordered : ∀ {h} → State h → Set₁
  Ordered st = Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (State.timers st)
             × All (λ t → State.clock st ≤ Timer.due t × State.pos st <ᵖ cascade t ≡ true) (State.timers st)

  -- The root's observer, in any world: it only records.
  rootObs : ∀ {h} → Observer R h
  rootObs = record { next = λ a → eff (note a) λ _ → done tt ; complete = eff fin λ _ → done tt ; closed = done false }

  -- THE CONFIGURATION `c` IS WHAT IS RUNNING: a witness holding every
  -- subscription the run reaches, against its kernel, whose open part is
  -- `c`; the frames being burst `fs`, the queue its pending frames and
  -- dead ones, the subjects' subscribers its joiners, the names all
  -- distinct, the root not done.
  --
  -- DEAD ROUTE: a relation per operator (a `Below s d`, against any
  --   observer that keeps an abstract interface) cannot be carried.
  --   Siblings that share one observer — a merge's lanes, a subject's
  --   joiners — each hold a remainder only the shared state records, and
  --   an abstract step returns its sibling's as an existential witness,
  --   forgotten; and a merge's order needs every sibling's pending
  --   positions, which an abstract subscription does not expose.
  record Holding {h} (fs : List (Firing h)) (c : U.Node R) (st : State h) : Set₁ where
    open At (State.heap st)
    field
      tree    : Sub h [] R
      holds   : Holds tree [] rootObs
      open≡   : part tree [] [] [] ≡ just c
      firing≡ : firings tree ≡ fs
      clocked : All (λ f → Firing.since f + Firing.u f ≡ State.clock st) fs
      timed   : Timed (State.timers st) (pendings tree)
      joined  : Joined (subjects tree) (joiners tree [])
      ordered : Ordered st
      fresh   : AllPairs _≢_ (names tree)
      running : State.ended st ≡ false

  -- CALM POINTS, where what is running is what the meaning has left to
  -- show: the machine at its loop, or about to step a live cold's frame
  -- from it.
  data Calm : Mach → Events R → Set₁ where
    calm     : ∀ {h} {st : State h} {c} → Holding [] c st → Calm ⟨ st , turn ⟩ (U.unfold c)
    bursting : ∀ {h} {st : State h} {c A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
             → Holding (firing s hd τ r i b ∷ []) c st → lower (get (State.heap st) hd) ≡ false
             → Calm ⟨ st , burst s hd u r i b same loop ⟩ (U.unfold c)

  -- The timers whose cold is spent: popping one runs nothing.
  spentIn : ∀ {h} → All (Pure.Val R h) h → List (Timer h) → ℕ
  spentIn H []       = 0
  spentIn H (t ∷ ts) = if lower (get H (Timer.handle t)) then suc (spentIn H ts) else spentIn H ts

  dead : Mach → ℕ
  dead ⟨ st , _ ⟩ = spentIn (State.heap st) (State.timers st)

  postulate
    -- With no timer queued, what is running has nothing to show: every
    -- cold it holds gone quiet, every joiner's copy of a quiet source.
    dry-hush : ∀ {h c} {st : State h} → Holding [] c st → State.timers st ≡ [] → U.step c ≡ U.hushˢ

    -- A dead timer popped: the clock and the run's position move to it,
    -- and nothing else does.
    pop-dead : ∀ {h c} {st : State h} {tm ts} → Holding [] c st → State.timers st ≡ tm ∷ ts
             → lower (get (State.heap st) (Timer.handle tm)) ≡ true
             → Holding [] c (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })

    -- A live timer popped: its cold's frame is being burst, and what is
    -- running has not moved — the frame's first step is the meaning's
    -- next event either way.
    pop-live : ∀ {h c} {st : State h} {tm ts} → Holding [] c st → State.timers st ≡ tm ∷ ts
             → lower (get (State.heap st) (Timer.handle tm)) ≡ false
             → Σ Time λ τ → Holding (firing (Timer.sink tm) (Timer.handle tm) τ (cascade tm) 0 (Timer.frame tm) ∷ []) c
                                     (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
