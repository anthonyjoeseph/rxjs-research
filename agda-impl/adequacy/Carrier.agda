{-# OPTIONS --guardedness --large-indices #-}

-- WHAT THE SIMULATION RE-ENTERS ON: the machine's state against the
-- meaning's configuration (`denotation.Unfold`'s `Node`), at the states
-- where `sim`'s corecursion pairs a step of each.  Every other state is
-- passed one side at a time, inside `adequacy.Simulation`'s `Wait`.
--
-- The machine keeps no tree, so the relation is carried by a witness,
-- `Sub`: every subscription the run still reaches, one constructor per
-- kernel, with the names it allocated and what the meaning keeps that
-- the run does not.  A subscription the run has reached but not begun
-- is `pendingˢ`; its meaning is the program `subscribe`d where it stands.
-- Which subscriptions are open is read off the heap, and the open part
-- is the configuration (`part`), positions included.
--
-- What the machine does next is read off the witness too.  A `Path`
-- locates a node; `walk` rebuilds, along it, the observer and the
-- continuation its kernel was handed.  What is owed after the current
-- callback returns is an agenda of `Call`s, each the code a kernel runs
-- at a node, and the machine's control and stack are that agenda up to
-- `_≗_`.  So a delivery deep inside a connect's feed or a lane's burst
-- is located where it happens, with nothing refocused on the way.
module adequacy.Carrier where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Level using (Lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList using (Time; Pos; From; Frame; Timeline; at; last; ix; tick; _<ᵖ_) renaming (sub to subᴾ; done to doneᶠ)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (base; module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; Kind; cell; slot; play; _∋_; wk∋; Sink; Handle; same; _⨾_; note; fin; module Pure)
open import operation.Machine using (module Machine)

module Carrying (R : Set) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (State; Timer; Callbacks; Val; get; cascade)
  open Machine R using (Mach; ⟨_,_⟩; Ctl; run; burst; turn; Stack; loop; push; rest; sent)

  ------------------------------------------------------------------------
  -- The same program, whatever world its names were weakened through

  -- Two programs written alike differ in how their worlds were reached:
  -- a name weakened along `σ ⨾ τ` and one weakened along `σ` then `τ`
  -- are equal only propositionally.  So names are related by `_≡_`, and
  -- continuations pointwise, never by extensionality.
  infix 4 _≗_
  data _≗_ : ∀ {w B} → Act w B → Act w B → Set₁ where
    done≗      : ∀ {w B} {b b′ : B} → b ≡ b′ → done {w} b ≗ done b′
    newRef≗    : ∀ {w B} {t a a′} {k k′ : ∀ {v} → w ⊑ v → Ref v t → Act v B}
               → a ≡ a′ → (∀ {v} (σ : w ⊑ v) r → k σ r ≗ k′ σ r) → newRef t a k ≗ newRef t a′ k′
    readRef≗   : ∀ {w B t} {r r′ : Ref w t} {k k′ : ∀ {v} → w ⊑ v → El v t → Act v B}
               → r ≡ r′ → (∀ {v} (σ : w ⊑ v) x → k σ x ≗ k′ σ x) → readRef r k ≗ readRef r′ k′
    writeRef≗  : ∀ {w B t} {r r′ : Ref w t} {a a′} {k k′ : Act w B} → r ≡ r′ → a ≡ a′ → k ≗ k′ → writeRef r a k ≗ writeRef r′ a′ k′
    register≗  : ∀ {w A B} {n n′ : A → Act w ⊤} {c c′ x x′} {k k′ : ∀ {v} → w ⊑ v → Sink v A → Act v B}
               → (∀ a → n a ≗ n′ a) → c ≗ c′ → x ≗ x′ → (∀ {v} (σ : w ⊑ v) s → k σ s ≗ k′ σ s)
               → register n c x k ≗ register n′ c′ x′ k′
    send≗      : ∀ {w A B} {s s′ : Sink w A} {a} {k k′ : Act w B} → s ≡ s′ → k ≗ k′ → send s a k ≗ send s′ a k′
    finish≗    : ∀ {w A B} {s s′ : Sink w A} {k k′ : Act w B} → s ≡ s′ → k ≗ k′ → finish s k ≗ finish s′ k′
    startCold≗ : ∀ {w A B} {c} {s s′ : Sink w A} {k k′ : ∀ {v} → w ⊑ v → Handle v → Act v B}
               → s ≡ s′ → (∀ {v} (σ : w ⊑ v) h → k σ h ≗ k′ σ h) → startCold c s k ≗ startCold c s′ k′
    stop≗      : ∀ {w B} {h h′ : Handle w} {k k′ : Act w B} → h ≡ h′ → k ≗ k′ → stop h k ≗ stop h′ k′
    eff≗       : ∀ {w B X} {e} {k k′ : X → Act w B} → (∀ a → k a ≗ k′ a) → eff e k ≗ eff e k′
    here≗      : ∀ {w B} {k k′ : Pos → Act w B} → (∀ p → k p ≗ k′ p) → here k ≗ here k′
    goto≗      : ∀ {w B} {p} {k k′ : Act w B} → k ≗ k′ → goto p k ≗ goto p k′
    diverge≗   : ∀ {w B} → diverge {w} {B} ≗ diverge
    unfold≗    : ∀ {w Γ A B} {l : Later Timeline Γ A} {e e′} {n n′ : A → Act w ⊤} {c c′ x x′}
                   {k k′ : ∀ {v} → w ⊑ v → Sink v ⊤ → Act v ⊤} {m m′ : Act w B}
               → e ≡ e′ → (∀ a → n a ≗ n′ a) → c ≗ c′ → x ≗ x′ → (∀ {v} (σ : w ⊑ v) s → k σ s ≗ k′ σ s) → m ≗ m′
               → unfold l e n c x k m ≗ unfold l e′ n′ c′ x′ k′ m′

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

  unsubscribing : ∀ {h} → Act h ⊤ → Subscription h
  unsubscribing u = record { unsubscribe = u }

  ------------------------------------------------------------------------
  -- The continuations a kernel hands its source, in the world the run has reached

  takeK : ∀ {h} → Cut h → Kont h → Kont h
  takeK c k τ sub = attach (wkCut τ c) sub >>ᴬ k τ (unsubscribing (cut (wkCut τ c)))

  flatK : ∀ {h A} → Cut h → Flat A h → Kont h → Kont h
  flatK oc fl k τ sub = attach (wkCut τ oc) sub >>ᴬ k τ (unsubscribing (cut (wkCut τ oc) >>ᴬ killAllᶜ (wkFlat τ fl)))

  laneK : ∀ {h} → Cut h → Kont h
  laneK c τ sub = attach (wkCut τ c) sub

  -- A connect's source, the body's subscription already made.
  srcK : ∀ {h} → Cut h → Subscription h → Kont h → Kont h
  srcK c body k ψ src = attach (wkCut ψ c) src >>ᴬ k ψ (unsubscribing (Subscription.unsubscribe src >>ᴬ Subscription.unsubscribe (wkSubn ψ body)))

  -- A connect's body: once subscribed, the source is, beside it.
  bodyK : ∀ {h Δ A} → Obs Timeline Δ A → Env Δ h → Subject A h → Cut h → Pos → Kont h → Kont h
  bodyK s E S c p k π body = goto (p ++ [ ix 1 ])
    (compile s (wkEnv π E) same (feeder (wkSubject π S)) (srcK (wkCut π c) body (wkKont π k)))

  deferK : ∀ {h} → Kont h → Kont h
  deferK k σ sub = register (λ _ → Subscription.unsubscribe sub) (done tt) (done false) λ τ sk →
                   k (σ ⨾ τ) (unsubscribing (send sk tt (done tt)))


  ------------------------------------------------------------------------
  -- Every subscription the run still reaches, with its names

  -- A started cold, subscribed at tick `τ`: between frames, its timeline
  -- from the frame it waits for, the frame's timer set at `e`; or at step
  -- `i` of the frame at `r`.
  data Phase (A : Set) : Set where
    waiting : ∀ {u} → Time → Pos → From A u → Phase A
    playing : ∀ {t} → Time → Pos → ℕ → Frame A t → Phase A

  -- A takeWhile running; its failing value passed, its completion at the
  -- position given owed; its completion delivered, its cut owed.
  data Taking : Set where
    taking : Taking
    ending : Pos → Taking
    taken  : Taking

  -- A connect's feed: none under way; a value from the source at `q`,
  -- owed still to the subscribers listed; the source's completion at `q`,
  -- likewise.  The list is the subject's as the feed read it.
  data Feed (A : Set) (h : World) : Set where
    idle      : Feed A h
    feeding   : A → Pos → List (Sink h A × Pos) → Feed A h
    finishing : Pos → List (Sink h A × Pos) → Feed A h

  mutual
    data Sub (h : World) : List Set → Set → Set₁ where
      -- Reached at `q`, its kernel not yet begun.
      pendingˢ   : ∀ {Δ A} → Obs Timeline Δ A → Pos → Sub h Δ A
      coldˢ      : ∀ {Δ A} → Sink h A → Handle h → Phase A → Sub h Δ A
      -- `of`, subscribed at `p`, `i` emitted, the rest to come.
      ofˢ        : ∀ {Δ A} → Pos → ℕ → List A → Sub h Δ A
      -- A subscription with nothing left: `empty`, a spent `of`, a join
      -- after the subject completed.
      doneˢ      : ∀ {Δ A} → Sub h Δ A
      mapˢ       : ∀ {Δ A B} → (A → B) → Sub h Δ A → Sub h Δ B
      scanˢ      : ∀ {Δ A B} → (B → A → B) → Ref h (base B) → Sub h Δ A → Sub h Δ B
      -- Its kill switch, the unsubscribe `attach` registered once the
      -- source's subscription exists, the source.
      takeWhileˢ : ∀ {Δ A} → Bool → (A → Bool) → Cut h → Maybe (Sink h ⊤) → Taking → Sub h Δ A → Sub h Δ A
      -- Its cells, the outer's kill switch and attached unsubscribe, the
      -- refill sink, the outer, and every lane it subscribed.
      flatMapˢ   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Maybe (Sink h ⊤) → Sink h ⊤
                 → Sub h Δ A → List (Lane h Δ B) → Sub h Δ B
      -- The source's program and where the connect was subscribed, the
      -- subject, the source's kill switch and attached unsubscribe, the
      -- feed, the source as it started, the source as the meaning holds
      -- it, the source, the body.
      connectˢ   : ∀ {Δ A B} → Obs Timeline Δ A → Pos → Subject A h → Cut h → Maybe (Sink h ⊤) → Feed A h
                 → U.Node A → Maybe (U.Node A) → Sub h Δ A → Sub h (A ∷ Δ) B → Sub h Δ B
      -- Joined at `j`, `i` of the source's events dropped: the registered
      -- sink and its flag, and its copy of the source as the meaning
      -- steps it, gone once its completion is delivered.
      joinˢ      : ∀ {Δ A} → Pos → ℕ → Sink h A → Ref h (base Bool) → A ∈ Δ → Maybe (U.Node A) → Sub h Δ A
      -- A `defer` reached: the unsubscribe it registered once its body's
      -- subscription exists, its body.
      deferˢ     : ∀ {Δ A} → Maybe (Sink h ⊤) → Sub h Δ A → Sub h Δ A

    record Lane (h : World) (Δ : List Set) (B : Set) : Set₁ where
      inductive
      constructor lane
      field
        switch   : Cut h
        detacher : Maybe (Sink h ⊤)
        inner    : Sub h Δ B

  -- WHAT UNSUBSCRIBING DOES, as each kernel's subscription says.  A
  -- subscription not yet made has nothing to undo.
  unsub : ∀ {h Δ A} → Sub h Δ A → Act h ⊤
  unsub (pendingˢ s q)                       = skipᴬ
  unsub (coldˢ s hd _)                       = stop hd (done tt)
  unsub (ofˢ p i xs)                         = skipᴬ
  unsub doneˢ                                = skipᴬ
  unsub (mapˢ f s)                           = unsub s
  unsub (scanˢ f r s)                        = unsub s
  unsub (takeWhileˢ i p c k tk s)            = cut c
  unsub (flatMapˢ op f fl oc k r so ls)      = cut oc >>ᴬ killAllᶜ fl
  unsub (connectˢ s₁ p S c k fd s₀ m src body) = unsub src >>ᴬ unsub body
  unsub (joinˢ j i sk l x cp)                = writeRef l false skipᴬ
  unsub (deferˢ nothing s)                   = skipᴬ
  unsub (deferˢ (just k) s)                  = send k tt (done tt)

  ------------------------------------------------------------------------
  -- Where a node sits, and what its kernel was handed

  mutual
    data Path {h} : ∀ {Δ A Δ′ A′} → Sub h Δ A → Sub h Δ′ A′ → Set₁ where
      here      : ∀ {Δ A} {t : Sub h Δ A} → Path t t
      in-map    : ∀ {Δ A B Δ′ C} {f : A → B} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (mapˢ f t) u
      in-scan   : ∀ {Δ A B Δ′ C} {f : B → A → B} {r} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (scanˢ f r t) u
      in-take   : ∀ {Δ A Δ′ C} {i p c k tk} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (takeWhileˢ i p c k tk t) u
      in-outer  : ∀ {Δ A B Δ′ C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C}
                → Path t u → Path (flatMapˢ op f fl oc k r t ls) u
      in-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C}
                → PathLanes ls u → Path (flatMapˢ op f fl oc k r t ls) u
      in-source : ∀ {Δ A B Δ′ C} {s₁ p S c k fd s₀ m} {t : Sub h Δ A} {b : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path t u → Path (connectˢ s₁ p S c k fd s₀ m t b) u
      in-body   : ∀ {Δ A B Δ′ C} {s₁ p S c k fd s₀ m} {t : Sub h Δ A} {b : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path b u → Path (connectˢ s₁ p S c k fd s₀ m t b) u
      in-defer  : ∀ {Δ A Δ′ C} {k} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (deferˢ k t) u

    data PathLanes {h} : ∀ {Δ B Δ′ C} → List (Lane h Δ B) → Sub h Δ′ C → Set₁ where
      this-lane : ∀ {Δ B Δ′ C} {c k} {t : Sub h Δ B} {ls} {u : Sub h Δ′ C} → Path t u → PathLanes (lane c k t ∷ ls) u
      next-lane : ∀ {Δ B Δ′ C} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → PathLanes ls u → PathLanes (l ∷ ls) u

  -- What a kernel at a node was handed: its observer, its continuation,
  -- the subjects in scope, and the sources the meaning starts them from.
  record Here (h : World) (Δ : List Set) (A : Set) : Set₁ where
    constructor ctx
    field
      obs  : Observer A h
      kont : Kont h
      env  : Env Δ h
      srcs : Srcs Δ
  open Here

  mutual
    walk : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Here h Δ A → Here h Δ′ A′
    walk here                                     H = H
    walk (in-map {f = f} p)                       H = walk p (ctx (mapO f (obs H)) (kont H) (env H) (srcs H))
    walk (in-scan {f = f} {r} p)                  H = walk p (ctx (scanO f r (obs H)) (kont H) (env H) (srcs H))
    walk (in-take {i = i} {q} {c} p)              H = walk p (ctx (takeWhileO i q c (obs H)) (takeK c (kont H)) (env H) (srcs H))
    walk (in-outer {op = op} {f} {fl} {oc} p)     H =
      walk p (ctx (Flat′.outerO op f (env H) (obs H) fl oc) (flatK oc fl (kont H)) (env H) (srcs H))
    walk (in-lanes {op = op} {f} {fl} p)          H = walkLanes op f fl H p
    walk (in-source {S = S} {c} {b = b} p)        H = walk p (ctx (feeder S) (srcK c (unsubscribing (unsub b)) (kont H)) (env H) (srcs H))
    walk (in-body {s₁ = s₁} {q} {S} {c} {s₀ = s₀} p) H =
      walk p (ctx (bodyO c (obs H)) (bodyK s₁ (env H) S c q (kont H)) (S ∷ env H) (s₀ ∷ srcs H))
    walk (in-defer p)                             H = walk p (ctx (obs H) (deferK (kont H)) (env H) (srcs H))

    walkLanes : ∀ {h Δ A B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h
              → Here h Δ B → PathLanes ls u → Here h Δ′ C
    walkLanes op f fl H (this-lane {c = c} p) = walk p (ctx (Flat′.laneO op f (env H) (obs H) fl c) (laneK c) (env H) (srcs H))
    walkLanes op f fl H (next-lane p)         = walkLanes op f fl H p

  -- The root's observer, in any world: it only records.
  rootObs : ∀ {h} → Observer R h
  rootObs = record { next = λ a → eff (note a) λ _ → done tt ; complete = eff fin λ _ → done tt ; closed = done false }

  top : ∀ {h} → Here h [] R
  top = ctx rootObs (λ _ _ → done tt) [] []

  ------------------------------------------------------------------------
  -- What is owed once the current callback returns

  -- Each, the code a kernel runs at a node: the rest of an `of`'s burst;
  -- a subscription's continuation, handed what unsubscribes it; a
  -- takeWhile's completion and cut, or its cut; a connect's cut once its
  -- body completes; the rest of a connect's feed.
  data Call {h} (t : Sub h [] R) : Set₁ where
    emitC  : ∀ {Δ A} {p i xs} → Path t (ofˢ {Δ = Δ} {A} p i xs) → Call t
    kontC  : ∀ {Δ A} {u : Sub h Δ A} → Path t u → Call t
    take1C : ∀ {Δ A} {i p c k q} {s : Sub h Δ A} → Path t (takeWhileˢ i p c k (ending q) s) → Call t
    take2C : ∀ {Δ A} {i p c k} {s : Sub h Δ A} → Path t (takeWhileˢ i p c k taken s) → Call t
    bodyC  : ∀ {Δ A B} {s₁ q S c k fd s₀ m} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B} → Path t (connectˢ s₁ q S c k fd s₀ m s b) → Call t
    feedC  : ∀ {Δ A B} {s₁ q S c k x r ss s₀ m} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
           → Path t (connectˢ s₁ q S c k (feeding x r ss) s₀ m s b) → Call t
    finC   : ∀ {Δ A B} {s₁ q S c k r ss s₀ m} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
           → Path t (connectˢ s₁ q S c k (finishing r ss) s₀ m s b) → Call t

  code : ∀ {h} {t : Sub h [] R} → Call t → Act h ⊤
  code (emitC {p = p} {i} {xs} π)        = emitAll (obs (walk π top)) p i xs
  code (kontC {u = u} π)                 = kont (walk π top) same (unsubscribing (unsub u))
  code (take1C {c = c} {q = q} π)        = goto q (Observer.complete (obs (walk π top))) >>ᴬ cut c
  code (take2C {c = c} π)                = cut c
  code (bodyC {c = c} π)                 = cut c
  code (feedC {x = x} {r} {ss} π)        = each ss λ j → goto (r ++ [ subᴾ (proj₂ j) ]) (send (proj₁ j) x skipᴬ)
  code (finC {r = r} {ss} π)             = each ss λ j → goto (r ++ [ subᴾ (proj₂ j) ]) (finish (proj₁ j) skipᴬ)

  ⟦_⟧ : ∀ {h} {t : Sub h [] R} → List (Call t) → Act h ⊤
  ⟦_⟧ = foldr (λ k m → code k >>ᴬ m) (done tt)

  ------------------------------------------------------------------------
  -- The machine's control and stack, against the witness

  module Against {h : World} (t : Sub h [] R) where
    -- Each frame, run in the current world, the agenda up to `_≗_`; a
    -- burst's delivery returns to the cold the witness has playing.
    data StackAs : ∀ {w X} → w ⊑ h → Stack w X → Set₁ where
      loopAs : ∀ {w} {σ : w ⊑ h} → StackAs σ loop
      restAs : ∀ {u w B} {m : Act w B} {ρ : u ⊑ w} {σ : w ⊑ h} {K} (ks : List (Call t))
             → (∀ b → wkAct σ m ≗ (⟦ ks ⟧ >>ᴬ done b)) → StackAs (ρ ⨾ σ) K → StackAs σ (push (rest m) ρ K)
      sentAs : ∀ {u w A v} {s : Sink w A} {hd τ τ′ r i} {b : Frame A v} {ρ : u ⊑ w} {σ : w ⊑ h} {K}
             → Path t (coldˢ {Δ = []} (wk∋ σ s) (wk∋ σ hd) (playing τ′ r i b)) → StackAs (ρ ⨾ σ) K
             → StackAs σ (push (sent s hd τ r i b) ρ K)

    -- The states the simulation re-enters at: the loop between turns; a
    -- value just recorded, the agenda left; a subscription about to
    -- begin at its pending node, compiled in some world its subjects were
    -- weakened from; a cold's frame about to step.
    data CtlAs : Ctl h → Set₁ where
      calmAs  : CtlAs turn
      noteAs  : ∀ {w} {act : Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → act ≗ ⟦ ks ⟧ → StackAs σ K → CtlAs (run act σ K)
      subAs   : ∀ {w Δ A} {s : Obs Timeline Δ A} {q} {act : Act h ⊤} {σ : w ⊑ h} {K} (π : Path t (pendingˢ s q)) (ks : List (Call t))
              → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ env (walk π top)
                   × act ≗ (compile s E′ υ (obs (walk π top)) (kont (walk π top)) >>ᴬ ⟦ ks ⟧))
              → StackAs σ K → CtlAs (run act σ K)
      burstAs : ∀ {w A v} {s : Sink h A} {hd τ τ′ r i} {b : Frame A v} {σ : w ⊑ h} {K}
              → Path t (coldˢ {Δ = []} s hd (playing τ′ r i b)) → StackAs σ K → CtlAs (burst s hd τ r i b σ K)

  ------------------------------------------------------------------------
  -- Against a heap

  over : ∀ {A} → U.Step A → Bool
  over (U.endˢ _) = true
  over U.hushˢ    = true
  over _          = false

  -- The configuration a cold's phase is.
  nodeOf : ∀ {A} → Phase A → U.Node A
  nodeOf (waiting τ e m)   = U.framesᶜ τ e m
  nodeOf (playing τ r i b) = U.burstᶜ τ r i b

  -- The frame a cold waits for, as the timer that should be queued.
  timerOf : ∀ {h A} → Sink h A → Handle h → Phase A → List (Timer h)
  timerOf s hd (waiting τ e (at t _ b)) = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
  timerOf s hd (waiting τ e _)          = []
  timerOf s hd (playing _ _ _ _)        = []

  -- A node reached by silent steps of the meaning, and by any steps.
  -- A joiner's copy behind its source, as a joiner at `j` steps it: by
  -- silent steps, and by values at positions not past `j`, which the
  -- joiner drops.  A joiner subscribed after the source has shown values
  -- starts from the source as it started, so it lags by those.
  data Lags {A} (j : Pos) : U.Node A → U.Node A → Set₁ where
    stay : ∀ {c} → Lags j c c
    skip : ∀ {c c′ c″ q} → U.step c ≡ U.skipˢ q c′ → Lags j c′ c″ → Lags j c c″
    drop : ∀ {c c′ c″ q a} → U.step c ≡ U.outˢ q a c′ → j <ᵖ q ≡ false → Lags j c′ c″ → Lags j c c″

  data Steps {A} : U.Node A → U.Node A → Set₁ where
    stay : ∀ {c} → Steps c c
    skip : ∀ {c c′ c″ q} → U.step c ≡ U.skipˢ q c′ → Steps c′ c″ → Steps c c″
    out  : ∀ {c c′ c″ q a} → U.step c ≡ U.outˢ q a c′ → Steps c′ c″ → Steps c c″

  -- Each connect in scope: its source as the run holds it, and its feed.
  Now : World → List Set → Set₁
  Now h = All (λ A → Maybe (U.Node A) × Feed A h)

  -- What the joiners of each subject are, the frames pending.
  record Joiner (h : World) : Set₁ where
    constructor joiner
    field
      {A}     : Set
      subject : Subject A h
      sink′   : Sink h A
      at′     : Pos

  mutual
    pendings : ∀ {h Δ A} → Sub h Δ A → List (Timer h)
    pendings (coldˢ s hd ph)                        = timerOf s hd ph
    pendings (mapˢ f s)                             = pendings s
    pendings (scanˢ f r s)                          = pendings s
    pendings (takeWhileˢ i p c k tk s)              = pendings s
    pendings (flatMapˢ op f fl oc k r so ls)        = pendings so ++ lanePendings ls
    pendings (connectˢ s₁ p S c k fd s₀ m src body) = pendings src ++ pendings body
    pendings (deferˢ k s)                           = pendings s
    pendings _                                      = []

    lanePendings : ∀ {h Δ B} → List (Lane h Δ B) → List (Timer h)
    lanePendings []                = []
    lanePendings (lane c k s ∷ ls) = pendings s ++ lanePendings ls

  mutual
    subjects : ∀ {h Δ A} → Sub h Δ A → List (Σ Set λ A → Subject A h)
    subjects (mapˢ f s)                             = subjects s
    subjects (scanˢ f r s)                          = subjects s
    subjects (takeWhileˢ i p c k tk s)              = subjects s
    subjects (flatMapˢ op f fl oc k r so ls)        = subjects so ++ laneSubjects ls
    subjects (connectˢ s₁ p S c k fd s₀ m src body) = (_ , S) ∷ subjects src ++ subjects body
    subjects (deferˢ k s)                           = subjects s
    subjects _                                      = []

    laneSubjects : ∀ {h Δ B} → List (Lane h Δ B) → List (Σ Set λ A → Subject A h)
    laneSubjects []                = []
    laneSubjects (lane c k s ∷ ls) = subjects s ++ laneSubjects ls

  mutual
    joiners : ∀ {h Δ A} → Sub h Δ A → Env Δ h → List (Joiner h)
    joiners (mapˢ f s)                             E = joiners s E
    joiners (scanˢ f r s)                          E = joiners s E
    joiners (takeWhileˢ i p c k tk s)              E = joiners s E
    joiners (flatMapˢ op f fl oc k r so ls)        E = joiners so E ++ laneJoiners ls E
    joiners (connectˢ s₁ p S c k fd s₀ m src body) E = joiners src E ++ joiners body (S ∷ E)
    joiners (joinˢ j i sk l x cp)                  E = joiner (lookup E x) sk j ∷ []
    joiners (deferˢ k s)                           E = joiners s E
    joiners _                                      E = []

    laneJoiners : ∀ {h Δ B} → List (Lane h Δ B) → Env Δ h → List (Joiner h)
    laneJoiners []                E = []
    laneJoiners (lane c k s ∷ ls) E = joiners s E ++ laneJoiners ls E

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

  maybeName : ∀ {h} → Maybe (Sink h ⊤) → List (Name h)
  maybeName nothing  = []
  maybeName (just k) = (slot _ , k) ∷ []

  -- EVERY NAME A SUBSCRIPTION'S KERNEL ALLOCATED.
  mutual
    names : ∀ {h Δ A} → Sub h Δ A → List (Name h)
    names (coldˢ s hd _)                         = (slot _ , s) ∷ (play , hd) ∷ []
    names (mapˢ f s)                             = names s
    names (scanˢ f r s)                          = (cell _ , r) ∷ names s
    names (takeWhileˢ i p c k tk s)              = cutNames c ++ maybeName k ++ names s
    names (flatMapˢ op f fl oc k r so ls)        = flatNames fl ++ cutNames oc ++ maybeName k ++ (slot _ , r) ∷ names so ++ laneNames ls
    names (connectˢ s₁ p S c k fd s₀ m src body) = subjectNames S ++ cutNames c ++ maybeName k ++ names src ++ names body
    names (joinˢ j i sk l x cp)                  = (slot _ , sk) ∷ (cell _ , l) ∷ []
    names (deferˢ k s)                           = maybeName k ++ names s
    names _                                      = []

    laneNames : ∀ {h Δ B} → List (Lane h Δ B) → List (Name h)
    laneNames []                = []
    laneNames (lane c k s ∷ ls) = cutNames c ++ maybeName k ++ names s ++ laneNames ls

  module At {h : World} (H : All (Val h) h) where
    val : ∀ {t} → Ref h t → El h t
    val r = lower (get H r)

    spentʰ : Handle h → Bool
    spentʰ hd = lower (get H hd)

    -- A registered observer, up to `_≗_` against `c`.
    slotIs : ∀ {A} → Sink h A → Callbacks A h → Set₁
    slotIs s c = CbRel (get H s) c

    -- A kill switch's attachment: none until the subscription exists,
    -- then the registered unsubscribe.
    Attached : Cut h → Maybe (Sink h ⊤) → Act h ⊤ → Set₁
    Attached c nothing  u = Lift _ (val (Kit.held c) ≡ nothing)
    Attached c (just k) u = val (Kit.held c) ≡ just k × slotIs k (attachCb u)

    Registered : Maybe (Sink h ⊤) → Act h ⊤ → Set₁
    Registered nothing  u = Lift _ ⊤
    Registered (just k) u = slotIs k (attachCb u)

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

    -- A connect is open while its body is, beside the source the meaning
    -- holds, if it holds one.
    connected : ∀ {A B} → Maybe (U.Node A) → Maybe (U.Node B) → Maybe (U.Node B)
    connected s        nothing  = nothing
    connected (just s) (just b) = just (U.connectᶜ b s)
    connected nothing  (just b) = just b

    taking? : ∀ {A} → Bool → (A → Bool) → Taking → Maybe (U.Node A) → Maybe (U.Node A)
    taking? i p taking     s = mapᴹ (U.takeWhileᶜ i p) s
    taking? i p (ending q) s = just (U.endᶜ q)
    taking? i p taken      s = nothing

    -- The lanes still open.
    count : ∀ {Δ B} → List (Lane h Δ B) → ℕ
    count []                = 0
    count (lane c _ _ ∷ ls) = if val (Kit.live c) then suc (count ls) else count ls

    switches : ∀ {Δ B} → List (Lane h Δ B) → List (Cut h)
    switches []                = []
    switches (lane c _ _ ∷ ls) = c ∷ switches ls

    ----------------------------------------------------------------------
    -- What is still open: the configuration, exactly

    mutual
      part : ∀ {Δ A} → Sub h Δ A → Srcs Δ → Maybe (U.Node A)
      part (pendingˢ s q)                         ρ = just (U.subscribe s ρ q)
      part (coldˢ s hd ph)                        ρ = if spentʰ hd then nothing else just (nodeOf ph)
      part (ofˢ p i xs)                           ρ = just (U.ofᶜ p i xs)
      part doneˢ                                  ρ = nothing
      part (mapˢ f s)                             ρ = mapᴹ (U.mapᶜ f) (part s ρ)
      part (scanˢ f r s)                          ρ = mapᴹ (U.scanᶜ f (val r)) (part s ρ)
      part (takeWhileˢ i p c k tk s)              ρ = if val (Kit.live c) then taking? i p tk (part s ρ) else nothing
      part (flatMapˢ op f fl oc k r so ls)        ρ =
        merged op (λ a q → U.subscribe (f a) ρ q) (part so ρ) (partLanes ls ρ) (val (Flat.queue fl))
      part (connectˢ s₁ p S c k fd s₀ m src body) ρ = connected m (part body (s₀ ∷ ρ))
      part (joinˢ j i sk l x cp)                  ρ = if val l then mapᴹ (U.joinᶜ j i) cp else nothing
      part (deferˢ k s)                           ρ = part s ρ

      partLanes : ∀ {Δ B} → List (Lane h Δ B) → Srcs Δ → List (U.Node B)
      partLanes []                ρ = []
      partLanes (lane c k s ∷ ls) ρ = if val (Kit.live c) then consᴹ (part s ρ) (partLanes ls ρ) else partLanes ls ρ

    ----------------------------------------------------------------------
    -- The joiners' copies

    -- Owed the feed's delivery.
    Owed : ∀ {A} → Feed A h → Sink h A → Pos → Set
    Owed idle             sk j = ⊥
    Owed (feeding x q ss) sk j = (sk , j) ∈ ss
    Owed (finishing q ss) sk j = (sk , j) ∈ ss

    -- A joiner's copy behind its source as the run holds it, by what the
    -- feed still owes it: the value, the completion, or nothing but
    -- silent steps.  A source the run holds no more has ended, and the
    -- copy reaches an end the same way.
    Behind : ∀ {A} → Pos → Feed A h → U.Node A → Maybe (U.Node A) → Set₁
    Behind {A} j (feeding x q ss) cp (just n) = Σ (U.Node A) λ cp′ → Lags j cp cp′ × U.step cp′ ≡ U.outˢ q x n
    Behind {A} j (feeding x q ss) cp nothing  = Lift _ ⊥
    Behind {A} j (finishing q ss) cp _        = Σ (U.Node A) λ cp′ → Lags j cp cp′ × U.step cp′ ≡ U.endˢ q
    Behind {A} j idle             cp (just n) = Lags j cp n
    Behind {A} j idle             cp nothing  = Σ (U.Node A) λ cp′ → Lags j cp cp′ × over (U.step cp′) ≡ true

    -- A source's history, from where every joiner's copy starts: values
    -- only at or before the run's position `p`, so a joiner subscribed
    -- now drops them all.
    History : ∀ {A} → Pos → U.Node A → Maybe (U.Node A) → Set₁
    History p s₀ (just n) = Lags p s₀ n
    History p s₀ nothing  = Lift _ ⊤

    -- Every live joiner whose copy has not ended, behind its source; every
    -- connect's source reached from where it started, by its history.
    mutual
      Caught : ∀ {Δ A} → Pos → Sub h Δ A → Srcs Δ → Now h Δ → Set₁
      Caught π (mapˢ f s)                             ρ ν = Caught π s ρ ν
      Caught π (scanˢ f r s)                          ρ ν = Caught π s ρ ν
      Caught π (takeWhileˢ i p c k tk s)              ρ ν = Caught π s ρ ν
      Caught π (flatMapˢ op f fl oc k r so ls)        ρ ν = Caught π so ρ ν × CaughtLanes π ls ρ ν
      Caught π (connectˢ s₁ p S c k fd s₀ m src body) ρ ν =
        History π s₀ (part src ρ) × Caught π src ρ ν × Caught π body (s₀ ∷ ρ) ((part src ρ , fd) ∷ ν)
      Caught π (joinˢ j i sk l x (just cp))           ρ ν = let (n , fd) = lookup ν x in
        val l ≡ true → (Owed fd sk j → Behind j fd cp n) × (¬ Owed fd sk j → Behind j idle cp n)
      Caught π (deferˢ k s)                           ρ ν = Caught π s ρ ν
      Caught π _                                      ρ ν = Lift _ ⊤

      CaughtLanes : ∀ {Δ B} → Pos → List (Lane h Δ B) → Srcs Δ → Now h Δ → Set₁
      CaughtLanes π []                ρ ν = Lift _ ⊤
      CaughtLanes π (lane c k s ∷ ls) ρ ν = Caught π s ρ ν × CaughtLanes π ls ρ ν

    ----------------------------------------------------------------------
    -- The gates

    -- Every cold below spent.
    Dead : ∀ {Δ A} → Sub h Δ A → Set₁
    Dead t = ∀ {Δ′ B} {sk : Sink h B} {hd ph} → Path t (coldˢ {Δ = Δ′} sk hd ph) → spentʰ hd ≡ true

    -- The source the meaning holds behind the run's by steps of the
    -- meaning; past the run's end, at its own.
    Kept : ∀ {A} → Maybe (U.Node A) → Maybe (U.Node A) → Set₁
    Kept {A} (just s) (just s′) = Steps s s′
    Kept {A} (just s) nothing   = Σ (U.Node A) λ s′ → Steps s s′ × over (U.step s′) ≡ true
    Kept {A} nothing  (just s′) = Lift _ (over (U.step s′) ≡ true)
    Kept {A} nothing  nothing   = Lift _ ⊤

    unended : ∀ {A} → Phase A → Bool
    unended (waiting _ _ doneᶠ) = false
    unended _                    = true

    -- Below a cut kill switch, a cut lane or a connect's closed body, every
    -- cold is spent; no live cold waits on its end, which its frame's
    -- last step delivers; and every connect's held source is `Kept`.
    mutual
      Gated : ∀ {Δ A} → Sub h Δ A → Srcs Δ → Set₁
      Gated (coldˢ s hd ph)                        ρ = Lift _ (spentʰ hd ≡ false → unended ph ≡ true)
      Gated (mapˢ f s)                             ρ = Gated s ρ
      Gated (scanˢ f r s)                          ρ = Gated s ρ
      Gated (takeWhileˢ i p c k tk s)              ρ = (val (Kit.live c) ≡ false → Dead s) × Gated s ρ
      Gated (flatMapˢ op f fl oc k r so ls)        ρ = Gated so ρ × GatedLanes ls ρ
      Gated (connectˢ s₁ p S c k fd s₀ m src body) ρ =
        Kept m (part src ρ) × (part body (s₀ ∷ ρ) ≡ nothing → Dead src) × Gated src ρ × Gated body (s₀ ∷ ρ)
      Gated (deferˢ k s)                           ρ = Gated s ρ
      Gated _                                      ρ = Lift _ ⊤

      GatedLanes : ∀ {Δ B} → List (Lane h Δ B) → Srcs Δ → Set₁
      GatedLanes []                ρ = Lift _ ⊤
      GatedLanes (lane c k s ∷ ls) ρ = (val (Kit.live c) ≡ false → Dead s) × Gated s ρ × GatedLanes ls ρ

    ----------------------------------------------------------------------
    -- Every subscription against its kernel

    mutual
      Holds : ∀ {Δ A} → Sub h Δ A → Env Δ h → Observer A h → Set₁
      Holds (coldˢ s hd p)                         E o = slotIs s (cbOf o)
      Holds (mapˢ f s)                             E o = Holds s E (mapO f o)
      Holds (scanˢ f r s)                          E o = Holds s E (scanO f r o)
      Holds (takeWhileˢ i p c k tk s)              E o = Attached c k (unsub s) × Holds s E (takeWhileO i p c o)
      Holds (flatMapˢ op f fl oc k r so ls)        E o =
        val (Flat.refill fl) ≡ just r × slotIs r (Flat′.refillCb op f E o fl)
        × Attached oc k (unsub so) × Holds so E (Flat′.outerO op f E o fl oc)
        × val (Flat.active fl) ≡ count ls
        × Σ (List (Cut h)) (λ gone → val (Flat.lanes fl) ++ gone ≡ switches ls × All (λ c → val (Kit.live c) ≡ false) gone)
        × HoldsLanes op f E o fl ls
      Holds (connectˢ s₁ p S c k fd s₀ m src body) E o =
        Attached c k (unsub src) × Holds src E (feeder S) × Holds body (S ∷ E) (bodyO c o)
      Holds (joinˢ j i sk l x cp)                  E o = slotIs sk (joinerCb l o)
      Holds (deferˢ k s)                           E o = Registered k (unsub s) × Holds s E o
      Holds _                                      E o = Lift _ ⊤

      HoldsLanes : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Env Δ h → Observer B h → Flat A h → List (Lane h Δ B) → Set₁
      HoldsLanes op f E o fl []                = Lift _ ⊤
      HoldsLanes op f E o fl (lane c k s ∷ ls) = Attached c k (unsub s) × Holds s E (Flat′.laneO op f E o fl c) × HoldsLanes op f E o fl ls

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
  -- THE RELATION

  -- Timers in the order their cascades sit, each due no earlier than
  -- now, its cascade past where the run is.
  Ordered : ∀ {h} → State h → Set₁
  Ordered st = Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (State.timers st)
             × All (λ t → State.clock st ≤ Timer.due t × State.pos st <ᵖ cascade t ≡ true) (State.timers st)

  -- THE CONFIGURATION `c` IS WHAT IS RUNNING: a witness holding every
  -- subscription the run reaches, against its kernel, whose open part is
  -- `c`; the machine's control and stack the witness's agenda; every
  -- joiner's copy behind its source by what its feed owes it, every
  -- closed gate's subscriptions spent, every joiner joined no later than
  -- the run's position; the queue its pending frames and dead ones, in
  -- order; the subjects' subscribers its joiners; the names all
  -- distinct; the clock the run position's tick; the root not done.
  record Carried (m : Mach) (c : U.Node R) : Set₁ where
    open Mach m using (world; state; ctl)
    open At (State.heap state)
    field
      tree    : Sub world [] R
      ctlAs   : Against.CtlAs tree ctl
      holds   : Holds tree [] rootObs
      open≡   : part tree [] ≡ just c
      caught  : Caught (State.pos state) tree [] []
      gated   : Gated tree []
      past    : All (λ j → State.pos state <ᵖ Joiner.at′ j ≡ false) (joiners tree [])
      timed   : Timed (State.timers state) (pendings tree)
      joined  : Joined (subjects tree) (joiners tree [])
      ordered : Ordered state
      fresh   : AllPairs _≢_ (names tree)
      clocked : State.clock state ≡ tick (State.pos state)
      running : State.ended state ≡ false
