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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Data.List.Relation.Unary.Any as Any
open import Relation.Nullary using (¬_)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList using (Time; Pos; From; Frame; Timeline; at; last; ix; tick; _<ᵖ_) renaming (sub to subᴾ; done to doneᶠ)
import denotation.Unfold as U
open import operation.AbstractObservable using (base; module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; Kind; cell; slot; play; _∋_; wk∋; Sink; Handle; same; _⨾_; note; fin; module Pure)
open import operation.Machine using (module Machine)

module Carrying (R : Set) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (State; Timer; Callbacks; Val; get; cascade)
  open Machine R using (Mach; ⟨_,_⟩; Ctl; run; ret; burst; turn; Stack; loop; push; rest; sent)

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
      -- feed, where the source ended once it has, the source, the body.
      connectˢ   : ∀ {Δ A B} → Obs Timeline Δ A → Pos → Subject A h → Cut h → Maybe (Sink h ⊤) → Feed A h
                 → Maybe Pos → Sub h Δ A → Sub h (A ∷ Δ) B → Sub h Δ B
      -- Joined at `j`: the registered sink and its flag, and what the
      -- meaning has fed it and not yet shown, with where it ends once
      -- told; gone once its completion is delivered.
      joinˢ      : ∀ {Δ A} → Pos → Sink h A → Ref h (base Bool) → A ∈ Δ → Maybe (List (Pos × A) × Maybe Pos) → Sub h Δ A
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
  unsub (connectˢ s₁ p S c k fd e src body) = unsub src >>ᴬ unsub body
  unsub (joinˢ j sk l x st)                = writeRef l false skipᴬ
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
      in-source : ∀ {Δ A B Δ′ C} {s₁ p S c k fd e} {t : Sub h Δ A} {b : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path t u → Path (connectˢ s₁ p S c k fd e t b) u
      in-body   : ∀ {Δ A B Δ′ C} {s₁ p S c k fd e} {t : Sub h Δ A} {b : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path b u → Path (connectˢ s₁ p S c k fd e t b) u
      in-defer  : ∀ {Δ A Δ′ C} {k} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (deferˢ k t) u

    data PathLanes {h} : ∀ {Δ B Δ′ C} → List (Lane h Δ B) → Sub h Δ′ C → Set₁ where
      this-lane : ∀ {Δ B Δ′ C} {c k} {t : Sub h Δ B} {ls} {u : Sub h Δ′ C} → Path t u → PathLanes (lane c k t ∷ ls) u
      next-lane : ∀ {Δ B Δ′ C} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → PathLanes ls u → PathLanes (l ∷ ls) u

  -- What a kernel at a node was handed: its observer, its continuation,
  -- the subjects in scope.
  record Here (h : World) (Δ : List Set) (A : Set) : Set₁ where
    constructor ctx
    field
      obs  : Observer A h
      kont : Kont h
      env  : Env Δ h
  open Here

  mutual
    walk : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Here h Δ A → Here h Δ′ A′
    walk here                                     H = H
    walk (in-map {f = f} p)                       H = walk p (ctx (mapO f (obs H)) (kont H) (env H))
    walk (in-scan {f = f} {r} p)                  H = walk p (ctx (scanO f r (obs H)) (kont H) (env H))
    walk (in-take {i = i} {q} {c} p)              H = walk p (ctx (takeWhileO i q c (obs H)) (takeK c (kont H)) (env H))
    walk (in-outer {op = op} {f} {fl} {oc} p)     H =
      walk p (ctx (Flat′.outerO op f (env H) (obs H) fl oc) (flatK oc fl (kont H)) (env H))
    walk (in-lanes {op = op} {f} {fl} p)          H = walkLanes op f fl H p
    walk (in-source {S = S} {c} {b = b} p)        H = walk p (ctx (feeder S) (srcK c (unsubscribing (unsub b)) (kont H)) (env H))
    walk (in-body {s₁ = s₁} {q} {S} {c} p)        H =
      walk p (ctx (bodyO c (obs H)) (bodyK s₁ (env H) S c q (kont H)) (S ∷ env H))
    walk (in-defer p)                             H = walk p (ctx (obs H) (deferK (kont H)) (env H))

    walkLanes : ∀ {h Δ A B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h
              → Here h Δ B → PathLanes ls u → Here h Δ′ C
    walkLanes op f fl H (this-lane {c = c} p) = walk p (ctx (Flat′.laneO op f (env H) (obs H) fl c) (laneK c) (env H))
    walkLanes op f fl H (next-lane p)         = walkLanes op f fl H p

  -- A node somewhere below `t`.
  record Spot {h Δ₀ A₀} (t : Sub h Δ₀ A₀) : Set₁ where
    constructor spot
    field
      {Δ}  : List Set
      {A}  : Set
      {u}  : Sub h Δ A
      path : Path t u

  -- The connects' sources a continuation handed to the node at the end
  -- of a path begins: one for each connect body the path enters, from the
  -- node up to the nearest lane, whose continuation only attaches.  The
  -- flag says a lane was met.
  mutual
    chain : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {x : Sub h Δ′ A′} {u : Sub h Δ″ A″}
          → (∀ {Δ₁ A₁} {v : Sub h Δ₁ A₁} → Path x v → Path t v) → Path x u → List (Spot t) × Bool
    chain mk here          = [] , false
    chain mk (in-map p)    = chain (λ q → mk (in-map q)) p
    chain mk (in-scan p)   = chain (λ q → mk (in-scan q)) p
    chain mk (in-take p)   = chain (λ q → mk (in-take q)) p
    chain mk (in-outer p)  = chain (λ q → mk (in-outer q)) p
    chain mk (in-lanes p)  = proj₁ (chainLanes (λ q → mk (in-lanes q)) p) , true
    chain mk (in-source p) = chain (λ q → mk (in-source q)) p
    chain mk (in-defer p)  = chain (λ q → mk (in-defer q)) p
    chain mk (in-body p) with chain (λ q → mk (in-body q)) p
    ... | ss , true  = ss , true
    ... | ss , false = spot (mk (in-source here)) ∷ ss , false

    chainLanes : ∀ {h Δ A Δ′ B Δ″ A″} {t : Sub h Δ A} {ls : List (Lane h Δ′ B)} {u : Sub h Δ″ A″}
               → (∀ {Δ₁ A₁} {v : Sub h Δ₁ A₁} → PathLanes ls v → Path t v) → PathLanes ls u → List (Spot t) × Bool
    chainLanes mk (this-lane p) = chain (λ q → mk (this-lane q)) p
    chainLanes mk (next-lane p) = chainLanes (λ q → mk (next-lane q)) p

  -- The root's observer, in any world: it only records.
  rootObs : ∀ {h} → Observer R h
  rootObs = record { next = λ a → eff (note a) λ _ → done tt ; complete = eff fin λ _ → done tt ; closed = done false }

  top : ∀ {h} → Here h [] R
  top = ctx rootObs (λ _ _ → done tt) []

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
    bodyC  : ∀ {Δ A B} {s₁ q S c k fd e} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B} → Path t (connectˢ s₁ q S c k fd e s b) → Call t
    feedC  : ∀ {Δ A B} {s₁ q S c k x r ss e} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
           → Path t (connectˢ s₁ q S c k (feeding x r ss) e s b) → Call t
    finC   : ∀ {Δ A B} {s₁ q S c k r ss e} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
           → Path t (connectˢ s₁ q S c k (finishing r ss) e s b) → Call t

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
      sentAs : ∀ {u w Δ A v} {s : Sink w A} {hd τ τ′ r i} {b : Frame A v} {ρ : u ⊑ w} {σ : w ⊑ h} {K}
             → Path t (coldˢ {Δ = Δ} (wk∋ σ s) (wk∋ σ hd) (playing τ′ r i b)) → StackAs (ρ ⨾ σ) K
             → StackAs σ (push (sent s hd τ r i b) ρ K)

    -- The states the simulation re-enters at: the loop between turns; a
    -- value just recorded, the agenda left; a subscription about to
    -- begin at its pending node, compiled in some world its subjects were
    -- weakened from; a cold's frame about to step; a timer just popped,
    -- its cold still waiting on the frame now at its first step.
    data CtlAs : Ctl h → Set₁ where
      calmAs  : CtlAs turn
      noteAs  : ∀ {w} {act : Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → act ≗ ⟦ ks ⟧ → StackAs σ K → CtlAs (run act σ K)
      subAs   : ∀ {w Δ A} {s : Obs Timeline Δ A} {q} {act : Act h ⊤} {σ : w ⊑ h} {K} (π : Path t (pendingˢ s q)) (ks : List (Call t))
              → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ env (walk π top)
                   × act ≗ (compile s E′ υ (obs (walk π top)) (kont (walk π top)) >>ᴬ ⟦ ks ⟧))
              → StackAs σ K → CtlAs (run act σ K)
      burstAs : ∀ {w Δ A v} {s : Sink h A} {hd τ τ′ r i} {b : Frame A v} {σ : w ⊑ h} {K}
              → Path t (coldˢ {Δ = Δ} s hd (playing τ′ r i b)) → StackAs σ K → CtlAs (burst s hd τ r i b σ K)
      fireAs  : ∀ {w Δ A u t′} {s : Sink h A} {hd τ′ e r} {x : u ≤ t′} {b : Frame A t′} {σ : w ⊑ h} {K}
              → r ≡ ix (τ′ + t′) ∷ subᴾ e ∷ [] → Path t (coldˢ {Δ = Δ} s hd (waiting τ′ e (at t′ x b))) → StackAs σ K
              → CtlAs (burst s hd t′ r 0 b σ K)

    -- What is owed, gathered from the control and the stack: the calls on
    -- the agenda, the bursts in flight, and the subscriptions reached and
    -- not begun that the one under way, or a continuation the agenda
    -- owes, begins.
    stackCalls : ∀ {w X} {σ : w ⊑ h} {K : Stack w X} → StackAs σ K → List (Call t)
    stackCalls loopAs          = []
    stackCalls (restAs ks _ K) = ks ++ stackCalls K
    stackCalls (sentAs _ K)    = stackCalls K

    stackBursts : ∀ {w X} {σ : w ⊑ h} {K : Stack w X} → StackAs σ K → List (Spot t)
    stackBursts loopAs         = []
    stackBursts (restAs _ _ K) = stackBursts K
    stackBursts (sentAs π K)   = spot π ∷ stackBursts K

    agenda : ∀ {c} → CtlAs c → List (Call t)
    agenda calmAs           = []
    agenda (noteAs ks _ K)  = ks ++ stackCalls K
    agenda (subAs _ ks _ K) = ks ++ stackCalls K
    agenda (burstAs _ K)    = stackCalls K
    agenda (fireAs _ _ K)   = stackCalls K

    bursts : ∀ {c} → CtlAs c → List (Spot t)
    bursts calmAs          = []
    bursts (noteAs _ _ K)  = stackBursts K
    bursts (subAs _ _ _ K) = stackBursts K
    bursts (burstAs π K)   = spot π ∷ stackBursts K
    bursts (fireAs _ π K)  = spot π ∷ stackBursts K

    kontChains : List (Call t) → List (Spot t)
    kontChains []             = []
    kontChains (kontC π ∷ ks) = proj₁ (chain (λ q → q) π) ++ kontChains ks
    kontChains (_ ∷ ks)       = kontChains ks

    begins : ∀ {c} → CtlAs c → List (Spot t)
    begins ca@(subAs π _ _ _) = spot π ∷ proj₁ (chain (λ q → q) π) ++ kontChains (agenda ca)
    begins ca                 = kontChains (agenda ca)

  ------------------------------------------------------------------------
  -- Against a heap

  -- The configuration a cold's phase is.
  nodeOf : ∀ {Δ A} → Phase A → U.Node Δ A
  nodeOf (waiting τ e m)   = U.framesᶜ τ e m
  nodeOf (playing τ r i b) = U.burstᶜ τ r i b

  -- The frame a cold waits for, as the timer that should be queued.
  timerOf : ∀ {h A} → Sink h A → Handle h → Phase A → List (Timer h)
  timerOf s hd (waiting τ e (at t _ b)) = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
  timerOf s hd (waiting τ e _)          = []
  timerOf s hd (playing _ _ _ _)        = []

  -- The frame a popped timer bursts, out of the queue and still pending.
  firing : ∀ {h} {t : Sub h [] R} {ctl : Ctl h} → Against.CtlAs t ctl → List (Timer h)
  firing {ctl = turn}                     _                                                   = []
  firing {ctl = run _ _ _}                _                                                   = []
  firing {ctl = ret _ _ _}                _                                                   = []
  firing {ctl = burst _ _ _ _ _ _ _ _}    (Against.burstAs _ _)                               = []
  firing {ctl = burst _ _ _ _ _ _ _ _}    (Against.fireAs {s = s} {hd} {τ′} {e} {x = x} {b} _ _ _) = timerOf s hd (waiting τ′ e (at _ x b))

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
    pendings (connectˢ s₁ p S c k fd e src body) = pendings src ++ pendings body
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
    subjects (connectˢ s₁ p S c k fd e src body) = (_ , S) ∷ subjects src ++ subjects body
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
    joiners (connectˢ s₁ p S c k fd e src body) E = joiners src E ++ joiners body (S ∷ E)
    joiners (joinˢ j sk l x st)                  E = joiner (lookup E x) sk j ∷ []
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
    names (connectˢ s₁ p S c k fd e src body) = subjectNames S ++ cutNames c ++ maybeName k ++ names src ++ names body
    names (joinˢ j sk l x st)                  = (slot _ , sk) ∷ (cell _ , l) ∷ []
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
    merged : ∀ {Δ A B} → T.FlatOp → (A → Pos → U.Node Δ B) → Maybe (U.Node Δ A) → List (U.Node Δ B) → List A → Maybe (U.Node Δ B)
    merged op g nothing []       []       = nothing
    merged op g o       ls       qs       = just (U.flatMapᶜ op g o ls qs)

    -- A connect is open while its body is, beside its source while that
    -- runs; past the source's end, every joiner the body holds told so.
    connected : ∀ {Δ A B} → Maybe Pos → Maybe (U.Node Δ A) → Maybe (U.Node (A ∷ Δ) B) → Maybe (U.Node Δ B)
    connected e        s        nothing  = nothing
    connected e        (just s) (just b) = just (U.connectᶜ b (U.live s))
    connected (just c) nothing  (just b) = just (U.connectᶜ (U.shut (Any.here refl) c b) (U.ended c))
    connected nothing  nothing  (just b) = nothing

    -- A joiner shows what it holds until it is gone.
    joinedᶜ : ∀ {Δ A} → A ∈ Δ → Pos → Maybe (List (Pos × A) × Maybe Pos) → Maybe (U.Node Δ A)
    joinedᶜ x j nothing          = nothing
    joinedᶜ x j (just (xs , e))  = just (U.joinᶜ x j xs e)

    taking? : ∀ {Δ A} → Bool → (A → Bool) → Taking → Maybe (U.Node Δ A) → Maybe (U.Node Δ A)
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
      part : ∀ {Δ A} → Sub h Δ A → Maybe (U.Node Δ A)
      part (pendingˢ s q)                        = just (U.subscribe s q)
      part (coldˢ s hd ph)                       = if spentʰ hd then nothing else just (nodeOf ph)
      part (ofˢ p i xs)                          = just (U.ofᶜ p i xs)
      part doneˢ                                 = nothing
      part (mapˢ f s)                            = mapᴹ (U.mapᶜ f) (part s)
      part (scanˢ f r s)                         = mapᴹ (U.scanᶜ f (val r)) (part s)
      part (takeWhileˢ i p c k tk s)             = if val (Kit.live c) then taking? i p tk (part s) else nothing
      part (flatMapˢ op f fl oc k r so ls)       =
        merged op (λ a q → U.subscribe (f a) q) (part so) (partLanes ls) (val (Flat.queue fl))
      part (connectˢ s₁ p S c k fd e src body)   = connected e (part src) (part body)
      part (joinˢ j sk l x st)                   = if val l then joinedᶜ x j st else nothing
      part (deferˢ k s)                          = part s

      partLanes : ∀ {Δ B} → List (Lane h Δ B) → List (U.Node Δ B)
      partLanes []                = []
      partLanes (lane c k s ∷ ls) = if val (Kit.live c) then consᴹ (part s) (partLanes ls) else partLanes ls

    ----------------------------------------------------------------------
    -- The joiners' feed

    -- Owed the feed's delivery.
    Owed : ∀ {A} → Feed A h → Sink h A → Pos → Set
    Owed idle             sk j = ⊥
    Owed (feeding x q ss) sk j = (sk , j) ∈ ss
    Owed (finishing q ss) sk j = (sk , j) ∈ ss

    -- What the meaning has fed a joiner at `j` and the run still owes it:
    -- the value, under the joiner's position; the completion, likewise.
    owing : ∀ {A : Set} → Feed A h → Pos → Maybe (List (Pos × A) × Maybe Pos)
    owing idle             j = just ([] , nothing)
    owing (feeding x q ss) j = just ((q ++ [ subᴾ j ] , x) ∷ [] , nothing)
    owing (finishing q ss) j = just ([] , just (q ++ [ subᴾ j ]))

    -- Owed nothing: still waiting while its source runs, gone once the
    -- source has ended.
    owingNone : ∀ {A : Set} → Maybe Pos → Maybe (List (Pos × A) × Maybe Pos)
    owingNone nothing  = just ([] , nothing)
    owingNone (just c) = nothing

    -- Each connect in scope: its feed, and where its source ended.
    Now : List Set → Set₁
    Now = All (λ A → Feed A h × Maybe Pos)

    -- EVERY LIVE JOINER HOLDS WHAT THE RUN OWES IT: the value or the
    -- completion its feed has still to deliver it, and nothing else.
    mutual
      Fed : ∀ {Δ A} → Sub h Δ A → Now Δ → Set₁
      Fed (mapˢ f s)                           ν = Fed s ν
      Fed (scanˢ f r s)                        ν = Fed s ν
      Fed (takeWhileˢ i p c k tk s)            ν = Fed s ν
      Fed (flatMapˢ op f fl oc k r so ls)      ν = Fed so ν × FedLanes ls ν
      Fed (connectˢ s₁ p S c k fd e src body)  ν = Fed src ν × Fed body ((fd , e) ∷ ν)
      Fed (joinˢ j sk l x st)                  ν = let (fd , e) = lookup ν x in
        Lift _ (val l ≡ true → (Owed fd sk j → st ≡ owing fd j) × (¬ Owed fd sk j → st ≡ owingNone e))
      Fed (deferˢ k s)                         ν = Fed s ν
      Fed _                                    ν = Lift _ ⊤

      FedLanes : ∀ {Δ B} → List (Lane h Δ B) → Now Δ → Set₁
      FedLanes []                ν = Lift _ ⊤
      FedLanes (lane c k s ∷ ls) ν = Fed s ν × FedLanes ls ν

    ----------------------------------------------------------------------
    -- The gates

    -- Every cold below spent.
    Dead : ∀ {Δ A} → Sub h Δ A → Set₁
    Dead t = ∀ {Δ′ B} {sk : Sink h B} {hd ph} → Path t (coldˢ {Δ = Δ′} sk hd ph) → spentʰ hd ≡ true

    unended : ∀ {A} → Phase A → Bool
    unended (waiting _ _ doneᶠ) = false
    unended _                    = true

    -- Below a switch cut once its subscription is attached, every cold
    -- spent.  Before then the cut has nothing to unsubscribe: a source cut
    -- inside its own subscribe burst keeps its colds unspent, each reading
    -- its subscriber closed, until the attach unsubscribes them.
    Cut↓ : ∀ {Δ A} → Maybe (Sink h ⊤) → Sub h Δ A → Set₁
    Cut↓ nothing  s = Lift _ ⊤
    Cut↓ (just _) s = Dead s

    -- Below a cut kill switch, a cut lane or a connect's closed body, every
    -- cold is spent once attached; no live cold waits on its end, which
    -- its frame's last step delivers.
    mutual
      Gated : ∀ {Δ A} → Sub h Δ A → Set₁
      Gated (coldˢ s hd ph)                       = Lift _ (spentʰ hd ≡ false → unended ph ≡ true)
      Gated (mapˢ f s)                            = Gated s
      Gated (scanˢ f r s)                         = Gated s
      Gated (takeWhileˢ i p c k tk s)             = (val (Kit.live c) ≡ false → Cut↓ k s) × Gated s
      Gated (flatMapˢ op f fl oc k r so ls)       = Gated so × GatedLanes ls
      Gated (connectˢ s₁ p S c k fd e src body)   =
        (part body ≡ nothing → Cut↓ k src) × Gated src × Gated body
      Gated (deferˢ k s)                          = Gated s
      Gated _                                     = Lift _ ⊤

      GatedLanes : ∀ {Δ B} → List (Lane h Δ B) → Set₁
      GatedLanes []                = Lift _ ⊤
      GatedLanes (lane c k s ∷ ls) = (val (Kit.live c) ≡ false → Cut↓ k s) × Gated s × GatedLanes ls

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
      Holds (connectˢ s₁ p S c k fd e src body) E o =
        Attached c k (unsub src) × Holds src E (feeder S) × Holds body (S ∷ E) (bodyO c o)
      Holds (joinˢ j sk l x st)                  E o = slotIs sk (joinerCb l o)
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

  -- EVERYTHING DUE BEFORE THE NEXT TURN IS OWED: an `of`'s rest to the
  -- agenda; a playing cold's frame to a burst in flight; a subscription
  -- reached and not begun to the one under way, or to a continuation the
  -- agenda owes; a live takeWhile's completion and cut, and a connect's
  -- feed, to the agenda.
  record Owned {h} (H : All (Val h) h) (t : Sub h [] R) {ctl : Ctl h} (ca : Against.CtlAs t ctl) : Set₁ where
    open At H
    open Against t
    field
      ofs   : ∀ {Δ A p i xs} (π : Path t (ofˢ {Δ = Δ} {A} p i xs)) → emitC π ∈ agenda ca
      plays : ∀ {Δ A s hd τ r i u} {b : Frame A u} (π : Path t (coldˢ {Δ = Δ} s hd (playing τ r i b)))
            → spentʰ hd ≡ false → spot π ∈ bursts ca
      begun : ∀ {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) → spot π ∈ begins ca
      ends  : ∀ {Δ A i p c k q} {s : Sub h Δ A} (π : Path t (takeWhileˢ i p c k (ending q) s))
            → val (Kit.live c) ≡ true → take1C π ∈ agenda ca
      cuts  : ∀ {Δ A i p c k} {s : Sub h Δ A} (π : Path t (takeWhileˢ i p c k taken s))
            → val (Kit.live c) ≡ true → take2C π ∈ agenda ca
      feeds : ∀ {Δ A B s₁ q S c k x r ss e} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
            → (π : Path t (connectˢ s₁ q S c k (feeding x r ss) e s b)) → feedC π ∈ agenda ca
      fins  : ∀ {Δ A B s₁ q S c k r ss e} {s : Sub h Δ A} {b : Sub h (A ∷ Δ) B}
            → (π : Path t (connectˢ s₁ q S c k (finishing r ss) e s b)) → finC π ∈ agenda ca

  -- Every subscription against what its kernel registered; below a closed
  -- gate, every cold spent.
  record Kernels {h} (H : All (Val h) h) (t : Sub h [] R) : Set₁ where
    open At H
    field
      holds : Holds t [] rootObs
      gated : Gated t

  -- Every live joiner holding what its feed owes it.
  record Meaning {h} (H : All (Val h) h) (t : Sub h [] R) : Set₁ where
    open At H
    field
      fed : Fed t []

  -- Every joiner joined no later than the run's position; the queue, with
  -- the frame popped and bursting, its pending frames and dead ones, the
  -- queue in order; the subjects' subscribers its joiners.
  record Queue {h} (st : State h) (t : Sub h [] R) (fl : List (Timer h)) : Set₁ where
    open At (State.heap st)
    field
      past    : All (λ j → State.pos st <ᵖ Joiner.at′ j ≡ false) (joiners t [])
      timed   : Timed (fl ++ State.timers st) (pendings t)
      joined  : Joined (subjects t) (joiners t [])
      ordered : Ordered st

  -- The names all distinct; the clock the run position's tick; the root
  -- not done.
  record Books {h} (st : State h) (t : Sub h [] R) : Set₁ where
    field
      fresh   : AllPairs _≢_ (names t)
      clocked : State.clock st ≡ tick (State.pos st)
      running : State.ended st ≡ false

  -- THE CONFIGURATION `c` IS WHAT IS RUNNING: a witness holding every
  -- subscription the run reaches, whose open part is `c`, and the
  -- machine's control and stack its agenda; then the invariants, one
  -- record per concern.
  record Carried (m : Mach) (c : U.Node [] R) : Set₁ where
    open Mach m using (world; state; ctl)
    field
      tree    : Sub world [] R
      ctlAs   : Against.CtlAs tree ctl
      open≡   : At.part (State.heap state) tree ≡ just c
      owned   : Owned (State.heap state) tree ctlAs
      kernels : Kernels (State.heap state) tree
      meaning : Meaning (State.heap state) tree
      queue   : Queue state tree (firing ctlAs)
      books   : Books state tree
