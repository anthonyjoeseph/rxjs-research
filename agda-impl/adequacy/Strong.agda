{-# OPTIONS --guardedness --large-indices #-}

-- THE RUN'S RE-ENTRY CONFIGURATIONS, against the ghost (`adequacy.Content`'s
-- `Mirror`): between turns, a value or the completion about to be
-- recorded, a subscription about to begin, a cold's frame about to step.
-- Every other configuration is reached from one of these by its own
-- silent steps, so is related to the ghost by nothing else.
--
-- The machine keeps no tree, so the relation is carried by a witness,
-- `Sub`: every subscription the run still reaches, one constructor per
-- kernel, with the names it allocated and what the meaning keeps that
-- the run does not.  A subscription the run has reached but not begun
-- is `pendingˢ`; its meaning is the program `subscribe`d where it stands.
-- A `Path` locates a node; `walk` rebuilds, along it, the observer and
-- the continuation its kernel was handed.
module adequacy.Strong where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Lift; lower)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Linked using (Linked) renaming ([] to []ᴸ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList using (Time; Pos; From; Frame; Timeline; at; emit; stall; close; ix; last; tick; root; _<ᵖ_) renaming (done to doneᶠ; quiet to quietᶠ) renaming (sub to subᴾ)
open import operation.AbstractObservable using (base; maybe; quiet; module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; note; fin; module Pure)
open import operation.Machine using (module Machine)
import denotation.Unfold as U
open import adequacy.Sane using (Sane; sane-subscribe)
open import adequacy.Placed using (placed-subscribe) renaming (Placed to Placedᵍ)
open import adequacy.Sorted using (module Sorting; _≤ᵖ_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

module Strongly (R : Set) where
  open Heap using (World; Kind; cell; slot; hush; play; _⊑_; _∋_; Sink; Handle; Quiet; _⨾_; same)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Shared Timeline (Out R) using (Callbacks; Heapᴹ; look; Conf; Ctl; Stack; bottom; push; rest; back; rehold; run; asking; ⟨_,_,_⟩) renaming (held to holding)
  open Pure R using (Timer; cascade)
  open Machine R using (Mach; Playing; begin)
  open Sorting R using (WellMach; begin-well)

  ------------------------------------------------------------------------
  -- The same program, whatever world its names were weakened through

  -- Two programs written alike differ in how their worlds were reached:
  -- a name weakened along `σ ⨾ τ` and one weakened along `σ` then `τ`
  -- are equal only propositionally.  So names and contents are related
  -- by `_≡_`, and continuations pointwise, never by extensionality.
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
    stash≗     : ∀ {w B} {m m′ : Act w ⊤} {k k′ : ∀ {v} → w ⊑ v → Quiet v → Act v B}
               → m ≗ m′ → (∀ {v} (σ : w ⊑ v) q → k σ q ≗ k′ σ q) → stash m k ≗ stash m′ k′
    cancel≗    : ∀ {w B} {q q′ : Quiet w} {k k′ : Act w B} → q ≡ q′ → k ≗ k′ → cancel q k ≗ cancel q′ k′
    eff≗       : ∀ {w B X} {e} {k k′ : X → Act w B} → (∀ a → k a ≗ k′ a) → eff e k ≗ eff e k′
    here≗      : ∀ {w B} {k k′ : Pos → Act w B} → (∀ p → k p ≗ k′ p) → here k ≗ here k′
    under≗     : ∀ {w B} {l} {m m′ : Act w ⊤} {k k′ : Act w B} → m ≗ m′ → k ≗ k′ → under l m k ≗ under l m′ k′
    diverge≗   : ∀ {w B} → diverge {w} {B} ≗ diverge
    unfold≗    : ∀ {w Γ A B} {l : Later _ Γ A} {e e′} {n n′ : A → Act w ⊤} {c c′ x x′}
                   {k k′ : ∀ {v} → w ⊑ v → Quiet v → Act v ⊤} {m m′ : Act w B}
               → e ≡ e′ → (∀ a → n a ≗ n′ a) → c ≗ c′ → x ≗ x′ → (∀ {v} (σ : w ⊑ v) q → k σ q ≗ k′ σ q) → m ≗ m′
               → unfold l e n c x k m ≗ unfold l e′ n′ c′ x′ k′ m′

  ≗-refl : ∀ {w B} (m : Act w B) → m ≗ m
  ≗-refl (done b)                 = done≗ refl
  ≗-refl (newRef t a k)           = newRef≗ refl λ σ r → ≗-refl (k σ r)
  ≗-refl (readRef r k)            = readRef≗ refl λ σ x → ≗-refl (k σ x)
  ≗-refl (writeRef r a k)         = writeRef≗ refl refl (≗-refl k)
  ≗-refl (register n c x k)       = register≗ (λ a → ≗-refl (n a)) (≗-refl c) (≗-refl x) λ σ s → ≗-refl (k σ s)
  ≗-refl (send s a k)             = send≗ refl (≗-refl k)
  ≗-refl (finish s k)             = finish≗ refl (≗-refl k)
  ≗-refl (startCold c s k)        = startCold≗ refl λ σ hd → ≗-refl (k σ hd)
  ≗-refl (stop hd k)              = stop≗ refl (≗-refl k)
  ≗-refl (stash m k)              = stash≗ (≗-refl m) λ σ q → ≗-refl (k σ q)
  ≗-refl (cancel q k)             = cancel≗ refl (≗-refl k)
  ≗-refl (eff e k)                = eff≗ λ a → ≗-refl (k a)
  ≗-refl (here k)                 = here≗ λ p → ≗-refl (k p)
  ≗-refl (under l m k)            = under≗ (≗-refl m) (≗-refl k)
  ≗-refl diverge                  = diverge≗
  ≗-refl (unfold l e n c x k m)   = unfold≗ refl (λ a → ≗-refl (n a)) (≗-refl c) (≗-refl x) (λ σ q → ≗-refl (k σ q)) (≗-refl m)

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
      { next = λ a → if p a then Observer.next o a
                     else (when i (under (ix 0) (Observer.next o a) skipᴬ) >>ᴬ under last (Observer.complete o) (cut c))
      ; complete = Observer.complete o ; closed = Observer.closed o })

    -- A connect's body: its completion cuts the source.
    bodyO : ∀ {B} → Cut h → Observer B h → Observer B h
    bodyO c o = record { next = Observer.next o ; complete = Observer.complete o >>ᴬ cut c ; closed = Observer.closed o }

    -- A connect's source feeds its subject.
    feeder : ∀ {A} → Subject A h → Observer A h
    feeder S = record
      { next = λ a → readRef (Subject.subscribers S) λ _ ss → each ss λ j → under (subᴾ (proj₂ j)) (send (proj₁ j) a skipᴬ) skipᴬ
      ; complete = writeRef (Subject.closed S) true (readRef (Subject.subscribers S) λ _ ss →
                   each ss λ j → under (subᴾ (proj₂ j)) (finish (proj₁ j) skipᴬ) skipᴬ)
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

  -- A connect's body: its subscription stashed in the connect's cell.
  bodyK : ∀ {h} → Ref h (maybe quiet) → Kont h
  bodyK b π body = stash (Subscription.unsubscribe body) λ π′ t → writeRef (wkR (π ⨾ π′) b) (just t) skipᴬ

  -- A connect's source, the body's subscription read from its cell.
  srcK : ∀ {h} → Cut h → Ref h (maybe quiet) → Kont h → Kont h
  srcK c b k ψ src = attach (wkCut ψ c) src >>ᴬ readRef (wkR ψ b) λ ψ′ mb →
    k (ψ ⨾ ψ′) (unsubscribing (Subscription.unsubscribe (wkSubn ψ′ src) >>ᴬ unsubscribeVia mb))

  -- A `defer`'s body: its subscription stashed, then cancelled through.
  deferK : ∀ {h} → Kont h → Kont h
  deferK k σ sub = stash (Subscription.unsubscribe sub) λ τ t → k (σ ⨾ τ) (unsubscribing (cancel t (done tt)))

  ------------------------------------------------------------------------
  -- Every subscription the run still reaches, with its names

  -- A started cold, subscribed at tick `τ`: between frames, its timeline
  -- from the frame it waits for, the frame's timer set at `e`; that
  -- frame's timer popped, its burst held and not yet stepped; or at step
  -- `i` of the frame at `r`.
  data Phase (A : Set) : Set where
    waiting : ∀ {u} → Time → Pos → From A u → Phase A
    fired   : ∀ {u} → Time → Pos → From A u → Phase A
    playing : ∀ {t} → Time → Pos → ℕ → Frame A t → Phase A

  -- A takeWhile running; its failing value passed at the position given,
  -- its completion under it owed, its source's configuration as the value
  -- left it; its completion delivered, its cut owed.
  data Taking (Δ : List Set) (A : Set) : Set₁ where
    taking : Taking Δ A
    ending : Pos → U.Node Δ A → Taking Δ A
    taken  : Taking Δ A

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
      -- Its kill switch, the unsubscribe `attach` stashed once the
      -- source's subscription exists, the source.
      takeWhileˢ : ∀ {Δ A} → Bool → (A → Bool) → Cut h → Maybe (Quiet h) → Taking Δ A → Sub h Δ A → Sub h Δ A
      -- Its cells, the outer's kill switch and stashed unsubscribe, the
      -- refill sink, the meaning's pool of what its ended parts left
      -- running, the outer, and every lane it subscribed.
      flatMapˢ   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Maybe (Quiet h) → Sink h ⊤
                 → U.Node Δ B → Sub h Δ A → List (Lane h Δ B) → Sub h Δ B
      -- The subject, the source's kill switch, the cell for the body's
      -- unsubscribe and what it stashed there, the source's stashed
      -- unsubscribe, the feed, where the source subscribes, where it
      -- ended once it has and what the meaning keeps of it running past
      -- that, the source, the body.
      connectˢ   : ∀ {Δ A B} → Subject A h → Cut h → Ref h (maybe quiet) → Maybe (Quiet h) → Maybe (Quiet h) → Feed A h
                 → Pos → Maybe Pos → U.Node Δ A → Sub h Δ A → Sub h (A ∷ Δ) B → Sub h Δ B
      -- Joined at `j`: the registered sink and its flag, and what the
      -- meaning has fed it and not yet shown, with where it ends once
      -- told; gone once its completion is delivered.
      joinˢ      : ∀ {Δ A} → Pos → Sink h A → Ref h (base Bool) → A ∈ Δ → Maybe (List (Pos × Maybe A) × Maybe Pos) → Sub h Δ A
      -- A `defer` reached: the unsubscribe it stashed once its body's
      -- subscription exists, its body.
      deferˢ     : ∀ {Δ A} → Maybe (Quiet h) → Sub h Δ A → Sub h Δ A

    record Lane (h : World) (Δ : List Set) (B : Set) : Set₁ where
      inductive
      constructor lane
      field
        switch   : Cut h
        detacher : Maybe (Quiet h)
        inner    : Sub h Δ B

  -- WHAT UNSUBSCRIBING DOES, as each kernel's subscription says.  A
  -- subscription not yet made has nothing to undo.
  unsub : ∀ {h Δ A} → Sub h Δ A → Act h ⊤
  unsub (pendingˢ s q)                     = skipᴬ
  unsub (coldˢ s hd _)                     = stop hd (done tt)
  unsub (ofˢ p i xs)                       = skipᴬ
  unsub doneˢ                              = skipᴬ
  unsub (mapˢ f s)                         = unsub s
  unsub (scanˢ f r s)                      = unsub s
  unsub (takeWhileˢ i p c k tk s)          = cut c
  unsub (flatMapˢ op f fl oc k r pl so ls)    = cut oc >>ᴬ killAllᶜ fl
  unsub (connectˢ S c b kb k fd rp e rt src bd)  = unsub src >>ᴬ unsubscribeVia kb
  unsub (joinˢ j sk l x st)                = writeRef l false skipᴬ
  unsub (deferˢ k s)                       = unsubscribeVia k

  ------------------------------------------------------------------------
  -- Where a node sits, and what its kernel was handed

  mutual
    data Path {h} : ∀ {Δ A Δ′ A′} → Sub h Δ A → Sub h Δ′ A′ → Set₁ where
      here      : ∀ {Δ A} {t : Sub h Δ A} → Path t t
      in-map    : ∀ {Δ A B Δ′ C} {f : A → B} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (mapˢ f t) u
      in-scan   : ∀ {Δ A B Δ′ C} {f : B → A → B} {r} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (scanˢ f r t) u
      in-take   : ∀ {Δ A Δ′ C} {i p c k tk} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (takeWhileˢ i p c k tk t) u
      in-outer  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C}
                → Path t u → Path (flatMapˢ op f fl oc k r pl t ls) u
      in-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C}
                → PathLanes ls u → Path (flatMapˢ op f fl oc k r pl t ls) u
      in-source : ∀ {Δ A B Δ′ C} {S c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path t u → Path (connectˢ S c b kb k fd rp e rt t bd) u
      in-body   : ∀ {Δ A B Δ′ C} {S c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C}
                → Path bd u → Path (connectˢ S c b kb k fd rp e rt t bd) u
      in-defer  : ∀ {Δ A Δ′ C} {k} {t : Sub h Δ A} {u : Sub h Δ′ C} → Path t u → Path (deferˢ k t) u

    data PathLanes {h} : ∀ {Δ B Δ′ C} → List (Lane h Δ B) → Sub h Δ′ C → Set₁ where
      this-lane : ∀ {Δ B Δ′ C} {c k} {t : Sub h Δ B} {ls} {u : Sub h Δ′ C} → Path t u → PathLanes (lane c k t ∷ ls) u
      next-lane : ∀ {Δ B Δ′ C} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → PathLanes ls u → PathLanes (l ∷ ls) u

  -- A path, then one from where it ends.
  mutual
    infixr 5 _⊕_ _⊕ᴸ_
    _⊕_ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} → Path t u → Path u v → Path t v
    here        ⊕ q = q
    in-map p    ⊕ q = in-map (p ⊕ q)
    in-scan p   ⊕ q = in-scan (p ⊕ q)
    in-take p   ⊕ q = in-take (p ⊕ q)
    in-outer p  ⊕ q = in-outer (p ⊕ q)
    in-lanes p  ⊕ q = in-lanes (p ⊕ᴸ q)
    in-source p ⊕ q = in-source (p ⊕ q)
    in-body p   ⊕ q = in-body (p ⊕ q)
    in-defer p  ⊕ q = in-defer (p ⊕ q)

    _⊕ᴸ_ : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} → PathLanes ls u → Path u v → PathLanes ls v
    this-lane p ⊕ᴸ q = this-lane (p ⊕ q)
    next-lane p ⊕ᴸ q = next-lane (p ⊕ᴸ q)

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
    walk here                               H = H
    walk (in-map {f = f} p)                 H = walk p (ctx (mapO f (obs H)) (kont H) (env H))
    walk (in-scan {f = f} {r} p)            H = walk p (ctx (scanO f r (obs H)) (kont H) (env H))
    walk (in-take {i = i} {q} {c} p)        H = walk p (ctx (takeWhileO i q c (obs H)) (takeK c (kont H)) (env H))
    walk (in-outer {op = op} {f} {fl} {oc} p) H =
      walk p (ctx (Flat′.outerO op f (env H) (obs H) fl oc) (flatK oc fl (kont H)) (env H))
    walk (in-lanes {op = op} {f} {fl} p)    H = walkLanes op f fl H p
    walk (in-source {S = S} {c} {b} p)      H = walk p (ctx (feeder S) (srcK c b (kont H)) (env H))
    walk (in-body {S = S} {c} {b} p)        H = walk p (ctx (bodyO c (obs H)) (bodyK b) (S ∷ᴬ env H))
    walk (in-defer p)                       H = walk p (ctx (obs H) (deferK (kont H)) (env H))

    walkLanes : ∀ {h Δ A B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h
              → Here h Δ B → PathLanes ls u → Here h Δ′ C
    walkLanes op f fl H (this-lane {c = c} p) = walk p (ctx (Flat′.laneO op f (env H) (obs H) fl c) (laneK c) (env H))
    walkLanes op f fl H (next-lane p)         = walkLanes op f fl H p

  -- The root's observer, in any world: it only records.
  rootObs : ∀ {h} → Observer R h
  rootObs = record { next = λ a → eff (note a) λ _ → done tt ; complete = eff fin λ _ → done tt ; closed = done false }

  top : ∀ {h} → Here h [] R
  top = ctx rootObs (λ _ _ → done tt) []ᴬ

  ------------------------------------------------------------------------
  -- What is owed once the current callback returns

  -- Each, the code a kernel runs at a node: the rest of an `of`'s burst;
  -- a subscription's continuation, handed what unsubscribes it; a
  -- takeWhile's completion and cut, or its cut; a connect's cut once its
  -- body completes; the rest of a connect's feed; a connect's source,
  -- subscribed once its body is.
  data Call {h} (t : Sub h [] R) : Set₁ where
    emitC  : ∀ {Δ A} {p i xs} → Path t (ofˢ {Δ = Δ} {A} p i xs) → Call t
    kontC  : ∀ {Δ A} {u : Sub h Δ A} → Path t u → Call t
    take1C : ∀ {Δ A} {i p c k q n} {s : Sub h Δ A} → Path t (takeWhileˢ i p c k (ending q n) s) → Call t
    take2C : ∀ {Δ A} {i p c k} {s : Sub h Δ A} → Path t (takeWhileˢ i p c k taken s) → Call t
    bodyC  : ∀ {Δ A B} {S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → Path t (connectˢ S c b kb k fd rp e rt s bd) → Call t
    feedC  : ∀ {Δ A B} {S c b kb k x r ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
           → Path t (connectˢ S c b kb k (feeding x r ss) rp e rt s bd) → Call t
    finC   : ∀ {Δ A B} {S c b kb k r ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
           → Path t (connectˢ S c b kb k (finishing r ss) rp e rt s bd) → Call t
    srcC   : ∀ {Δ A B} {S c b kb k fd e s₁ q rp rt} {bd : Sub h (A ∷ Δ) B}
           → Path t (connectˢ S c b kb k fd rp e rt (pendingˢ {Δ = Δ} s₁ q) bd) → Call t

  code : ∀ {h} {t : Sub h [] R} → Call t → Act h ⊤
  code (emitC {i = i} {xs} π)            = emitAll (obs (walk π top)) i xs
  code (kontC {u = u} π)                 = kont (walk π top) same (unsubscribing (unsub u))
  code (take1C {c = c} π)                = under last (Observer.complete (obs (walk π top))) (cut c)
  code (take2C {c = c} π)                = cut c
  code (bodyC {c = c} π)                 = cut c
  code (feedC {x = x} {ss = ss} π)       = each ss λ j → under (subᴾ (proj₂ j)) (send (proj₁ j) x skipᴬ) skipᴬ
  code (finC {ss = ss} π)                = each ss λ j → under (subᴾ (proj₂ j)) (finish (proj₁ j) skipᴬ) skipᴬ
  code (srcC {s₁ = s₁} π)                = let H = walk (π ⊕ in-source here) top in
                                           under (ix 1) (compile s₁ (env H) same (obs H) (kont H)) skipᴬ

  ⟦_⟧ : ∀ {h} {t : Sub h [] R} → List (Call t) → Act h ⊤
  ⟦_⟧ = foldr (λ k m → code k >>ᴬ m) (done tt)

  ------------------------------------------------------------------------
  -- Against a heap

  -- The configuration a cold's phase is.
  nodeOf : ∀ {Δ A} → Phase A → U.Node Δ A
  nodeOf (waiting τ e m)   = U.framesᶜ τ e m
  nodeOf (fired τ e m)     = U.framesᶜ τ e m
  nodeOf (playing τ r i b) = U.burstᶜ τ r i b

  -- The frame a cold waits for, as the timer that should be queued.
  timerOf : ∀ {h A} → Sink h A → Handle h → Phase A → List (Timer h)
  timerOf s hd (waiting τ e (at t _ b)) = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
  timerOf s hd (waiting τ e _)          = []
  timerOf s hd (fired _ _ _)            = []
  timerOf s hd (playing _ _ _ _)        = []

  -- What the joiners of each subject are.
  record Joiner (h : World) : Set₁ where
    constructor joiner
    field
      {A}     : Set
      subject : Subject A h
      sink′   : Sink h A
      at′     : Pos

  mutual
    pendings : ∀ {h Δ A} → Sub h Δ A → List (Timer h)
    pendings (coldˢ s hd ph)                   = timerOf s hd ph
    pendings (mapˢ f s)                        = pendings s
    pendings (scanˢ f r s)                     = pendings s
    pendings (takeWhileˢ i p c k tk s)         = pendings s
    pendings (flatMapˢ op f fl oc k r pl so ls)   = pendings so ++ lanePendings ls
    pendings (connectˢ S c b kb k fd rp e rt src bd) = pendings src ++ pendings bd
    pendings (deferˢ k s)                      = pendings s
    pendings _                                 = []

    lanePendings : ∀ {h Δ B} → List (Lane h Δ B) → List (Timer h)
    lanePendings []                = []
    lanePendings (lane c k s ∷ ls) = pendings s ++ lanePendings ls

  mutual
    subjects : ∀ {h Δ A} → Sub h Δ A → List (Σ Set λ A → Subject A h)
    subjects (mapˢ f s)                        = subjects s
    subjects (scanˢ f r s)                     = subjects s
    subjects (takeWhileˢ i p c k tk s)         = subjects s
    subjects (flatMapˢ op f fl oc k r pl so ls)   = subjects so ++ laneSubjects ls
    subjects (connectˢ S c b kb k fd rp e rt src bd) = (_ , S) ∷ subjects src ++ subjects bd
    subjects (deferˢ k s)                      = subjects s
    subjects _                                 = []

    laneSubjects : ∀ {h Δ B} → List (Lane h Δ B) → List (Σ Set λ A → Subject A h)
    laneSubjects []                = []
    laneSubjects (lane c k s ∷ ls) = subjects s ++ laneSubjects ls

  mutual
    joiners : ∀ {h Δ A} → Sub h Δ A → Env Δ h → List (Joiner h)
    joiners (mapˢ f s)                        E = joiners s E
    joiners (scanˢ f r s)                     E = joiners s E
    joiners (takeWhileˢ i p c k tk s)         E = joiners s E
    joiners (flatMapˢ op f fl oc k r pl so ls)   E = joiners so E ++ laneJoiners ls E
    joiners (connectˢ S c b kb k fd rp e rt src bd) E = joiners src E ++ joiners bd (S ∷ᴬ E)
    joiners (joinˢ j sk l x st)               E = joiner (lookup E x) sk j ∷ []
    joiners (deferˢ k s)                      E = joiners s E
    joiners _                                 E = []

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

  quietName : ∀ {h} → Maybe (Quiet h) → List (Name h)
  quietName nothing  = []
  quietName (just q) = (hush , q) ∷ []

  -- EVERY NAME A SUBSCRIPTION'S KERNEL ALLOCATED.
  mutual
    names : ∀ {h Δ A} → Sub h Δ A → List (Name h)
    names (coldˢ s hd _)                    = (slot _ , s) ∷ (play , hd) ∷ []
    names (mapˢ f s)                        = names s
    names (scanˢ f r s)                     = (cell _ , r) ∷ names s
    names (takeWhileˢ i p c k tk s)         = cutNames c ++ quietName k ++ names s
    names (flatMapˢ op f fl oc k r pl so ls)   = flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls
    names (connectˢ S c b kb k fd rp e rt src bd) =
      subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names src ++ names bd
    names (joinˢ j sk l x st)               = (slot _ , sk) ∷ (cell _ , l) ∷ []
    names (deferˢ k s)                      = quietName k ++ names s
    names _                                 = []

    laneNames : ∀ {h Δ B} → List (Lane h Δ B) → List (Name h)
    laneNames []                = []
    laneNames (lane c k s ∷ ls) = cutNames c ++ quietName k ++ names s ++ laneNames ls

  module At {h : World} (H : Heapᴹ h) where
    val : ∀ {t} → Ref h t → El h t
    val r = lower (look H r)

    spentʰ : Handle h → Bool
    spentʰ hd = lower (look H hd)

    -- A registered observer, up to `_≗_` against `c`.
    slotIs : ∀ {A} → Sink h A → Callbacks A h → Set₁
    slotIs s c = CbRel (look H s) c

    -- A stashed unsubscribe, up to `_≗_` against `u`.
    stashIs : Quiet h → Act h ⊤ → Set₁
    stashIs q u = look H q ≗ u

    -- A kill switch's attachment: none until the subscription exists,
    -- then the stashed unsubscribe.
    Attached : Cut h → Maybe (Quiet h) → Act h ⊤ → Set₁
    Attached c nothing  u = Lift _ (val (Kit.held c) ≡ nothing)
    Attached c (just q) u = val (Kit.held c) ≡ just q × stashIs q u

    Stashed : Maybe (Quiet h) → Act h ⊤ → Set₁
    Stashed nothing  u = Lift _ ⊤
    Stashed (just q) u = stashIs q u

    mapᴹ : ∀ {X Y : Set₁} → (X → Y) → Maybe X → Maybe Y
    mapᴹ f nothing  = nothing
    mapᴹ f (just x) = just (f x)

    consᴹ : ∀ {X : Set₁} → Maybe X → List X → List X
    consᴹ nothing  xs = xs
    consᴹ (just x) xs = x ∷ xs

    -- A flatMap is open while its outer, a lane or the queue is.
    merged : ∀ {Δ A B} → T.FlatOp → (A → Pos → U.Node Δ B) → Maybe (U.Node Δ A) → List (U.Node Δ B) → List A → U.Node Δ B → Maybe (U.Node Δ B)
    merged op g nothing []       []       pl = nothing
    merged op g o       ls       qs       pl = just (U.flatMapᶜ op g o ls qs pl)

    -- A connect is open while its body is, beside its source while that
    -- runs; past the source's end, every joiner the body holds told so.
    connected : ∀ {Δ A B} → Pos → Maybe Pos → U.Node Δ A → Maybe (U.Node Δ A) → Maybe (U.Node (A ∷ Δ) B) → Maybe (U.Node Δ B)
    connected r e        t s        nothing  = nothing
    connected r e        t (just s) (just b) = just (U.connectᶜ r b (U.live s))
    connected r (just c) t nothing  (just b) = just (U.connectᶜ r (U.shut (Any.here refl) c b) (U.ended c t))
    connected r nothing  t nothing  (just b) = nothing

    -- A joiner shows what it holds until it is gone.
    joinedᶜ : ∀ {Δ A} → A ∈ Δ → Pos → Maybe (List (Pos × Maybe A) × Maybe Pos) → Maybe (U.Node Δ A)
    joinedᶜ x j nothing          = nothing
    joinedᶜ x j (just (xs , e))  = just (U.joinᶜ x j xs e)

    taking? : ∀ {Δ A} → Bool → (A → Bool) → Taking Δ A → Maybe (U.Node Δ A) → Maybe (U.Node Δ A)
    taking? i p taking       s = mapᴹ (U.takeWhileᶜ i p) s
    taking? i p (ending k c) s = just (U.endingᶜ (k ++ [ last ]) c)
    taking? i p taken        s = nothing

    -- The lanes still open.
    count : ∀ {Δ B} → List (Lane h Δ B) → ℕ
    count []                = 0
    count (lane c _ _ ∷ ls) = if val (Kit.live c) then suc (count ls) else count ls

    switches : ∀ {Δ B} → List (Lane h Δ B) → List (Cut h)
    switches []                = []
    switches (lane c _ _ ∷ ls) = c ∷ switches ls

    ----------------------------------------------------------------------
    -- What is still open: the ghost, exactly

    mutual
      part : ∀ {Δ A} → Sub h Δ A → Maybe (U.Node Δ A)
      part (pendingˢ s q)                    = just (U.subscribe s q)
      part (coldˢ s hd ph)                   = if spentʰ hd then nothing else just (nodeOf ph)
      part (ofˢ p i xs)                      = just (U.ofᶜ p i xs)
      part doneˢ                             = nothing
      part (mapˢ f s)                        = mapᴹ (U.mapᶜ f) (part s)
      part (scanˢ f r s)                     = mapᴹ (U.scanᶜ f (val r)) (part s)
      part (takeWhileˢ i p c k tk s)         = if val (Kit.live c) then taking? i p tk (part s) else nothing
      part (flatMapˢ op f fl oc k r pl so ls)   =
        merged op (λ a q → U.subscribe (f a) q) (part so) (partLanes ls) (val (Flat.queue fl)) pl
      part (connectˢ S c b kb k fd rp e rt src bd) = connected rp e rt (part src) (part bd)
      part (joinˢ j sk l x st)               = if val l then joinedᶜ x j st else nothing
      part (deferˢ k s)                      = part s

      partLanes : ∀ {Δ B} → List (Lane h Δ B) → List (U.Node Δ B)
      partLanes []                = []
      partLanes (lane c k s ∷ ls) = if val (Kit.live c) then consᴹ (part s) (partLanes ls) else partLanes ls

    ----------------------------------------------------------------------
    -- The joiners' feed

    -- Owed the feed's delivery.
    Owed : ∀ {A} → Feed A h → Sink h A → Pos → Set
    Owed idle             sk j = ⊥
    Owed (feeding x q ss) sk j = (sk , j) ∈ᴸ ss
    Owed (finishing q ss) sk j = (sk , j) ∈ᴸ ss

    -- What the meaning has fed a joiner at `j` and the run still owes it:
    -- the value, under the joiner's position; the completion, likewise.
    owing : ∀ {A : Set} → Feed A h → Pos → Maybe (List (Pos × Maybe A) × Maybe Pos)
    owing idle             j = just ([] , nothing)
    owing (feeding x q ss) j = just ((q ++ [ subᴾ j ] , just x) ∷ [] , nothing)
    owing (finishing q ss) j = just ([] , just (q ++ [ subᴾ j ]))

    -- Owed nothing: still waiting while its source runs, gone once the
    -- source has ended.
    owingNone : ∀ {A : Set} → Maybe Pos → Maybe (List (Pos × Maybe A) × Maybe Pos)
    owingNone nothing  = just ([] , nothing)
    owingNone (just c) = nothing

    -- Each connect in scope: its feed, and where its source ended.
    Now : List Set → Set₁
    Now = All (λ A → Feed A h × Maybe Pos)

    -- EVERY LIVE JOINER HOLDS WHAT THE RUN OWES IT: the value or the
    -- completion its feed has still to deliver it, and nothing else.
    mutual
      Fed : ∀ {Δ A} → Sub h Δ A → Now Δ → Set₁
      Fed (mapˢ f s)                        ν = Fed s ν
      Fed (scanˢ f r s)                     ν = Fed s ν
      Fed (takeWhileˢ i p c k tk s)         ν = Fed s ν
      Fed (flatMapˢ op f fl oc k r pl so ls)   ν = Fed so ν × FedLanes ls ν
      Fed (connectˢ S c b kb k fd rp e rt src bd) ν = Fed src ν × Fed bd ((fd , e) ∷ᴬ ν)
      Fed (joinˢ j sk l x st)               ν = let (fd , e) = lookup ν x in
        Lift _ (val l ≡ true → (Owed fd sk j → st ≡ owing fd j) × (¬ Owed fd sk j → st ≡ owingNone e))
      Fed (deferˢ k s)                      ν = Fed s ν
      Fed _                                 ν = Lift _ ⊤

      FedLanes : ∀ {Δ B} → List (Lane h Δ B) → Now Δ → Set₁
      FedLanes []                ν = Lift _ ⊤
      FedLanes (lane c k s ∷ ls) ν = Fed s ν × FedLanes ls ν

    ----------------------------------------------------------------------
    -- The gates

    -- Every cold below spent that unsubscribing reaches: below a
    -- subscription not yet attached, nothing.  A switch cut before its
    -- subscription is attached has nothing to unsubscribe: a source cut
    -- inside its own subscribe burst, or a lane cut while its cold's
    -- first burst plays, keeps its colds unspent, each reading its
    -- subscriber closed, until the attach unsubscribes them.
    --
    -- REFUTED: 00dd1c06 of every cold below a cut switch, by a lane whose cold plays its first burst into a takeWhile that fails and cuts
    mutual
      Spent : ∀ {Δ A} → Sub h Δ A → Set₁
      Spent (coldˢ s hd ph)                         = Lift _ (spentʰ hd ≡ true)
      Spent (mapˢ f s)                              = Spent s
      Spent (scanˢ f r s)                           = Spent s
      Spent (takeWhileˢ i p c k tk s)               = Cut↓ k s
      Spent (flatMapˢ op f fl oc k r pl so ls)      = Cut↓ k so × SpentLanes ls
      Spent (connectˢ S c b kb k fd rp e rt src bd) = Cut↓ k src × Cut↓ kb bd
      Spent (deferˢ k s)                            = Cut↓ k s
      Spent _                                       = Lift _ ⊤

      SpentLanes : ∀ {Δ B} → List (Lane h Δ B) → Set₁
      SpentLanes []                = Lift _ ⊤
      SpentLanes (lane c k s ∷ ls) = Cut↓ k s × SpentLanes ls

      -- Below a subscription once attached, what unsubscribing reaches
      -- spent.
      Cut↓ : ∀ {Δ A} → Maybe (Quiet h) → Sub h Δ A → Set₁
      Cut↓ nothing  s = Lift _ ⊤
      Cut↓ (just _) s = Spent s

    unended : ∀ {A} → Phase A → Bool
    unended (waiting _ _ doneᶠ) = false
    unended _                    = true

    -- Below a cut kill switch, a cut lane or a connect's thrown switch,
    -- what unsubscribing reaches is spent once attached; no live cold
    -- waits on its end, which its frame's last step delivers. A connect's
    -- body ending does not tear its source: the source stays live until
    -- the switch is thrown, and a note can fall in between.
    --
    -- REFUTED: c0bd1892 of a connect's source torn once its body's part is gone, by a concat whose next lane emits from inside the body's completion
    mutual
      Gated : ∀ {Δ A} → Sub h Δ A → Set₁
      Gated (coldˢ s hd ph)                   = Lift _ (spentʰ hd ≡ false → unended ph ≡ true)
      Gated (mapˢ f s)                        = Gated s
      Gated (scanˢ f r s)                     = Gated s
      Gated (takeWhileˢ i p c k tk s)         = (val (Kit.live c) ≡ false → Cut↓ k s) × Gated s
      Gated (flatMapˢ op f fl oc k r pl so ls)   = Gated so × GatedLanes ls
      Gated (connectˢ S c b kb k fd rp e rt src bd) = (val (Kit.live c) ≡ false → Cut↓ k src) × Gated src × Gated bd
      Gated (deferˢ k s)                      = Gated s
      Gated _                                 = Lift _ ⊤

      GatedLanes : ∀ {Δ B} → List (Lane h Δ B) → Set₁
      GatedLanes []                = Lift _ ⊤
      GatedLanes (lane c k s ∷ ls) = (val (Kit.live c) ≡ false → Cut↓ k s) × Gated s × GatedLanes ls

    ----------------------------------------------------------------------
    -- Every subscription against its kernel

    mutual
      Holds : ∀ {Δ A} → Sub h Δ A → Env Δ h → Observer A h → Set₁
      Holds (coldˢ s hd p)                    E o = slotIs s (cbOf o)
      Holds (mapˢ f s)                        E o = Holds s E (mapO f o)
      Holds (scanˢ f r s)                     E o = Holds s E (scanO f r o)
      Holds (takeWhileˢ i p c k tk s)         E o = Attached c k (unsub s) × Holds s E (takeWhileO i p c o)
      Holds (flatMapˢ op f fl oc k r pl so ls)   E o =
        val (Flat.refill fl) ≡ just r × slotIs r (Flat′.refillCb op f E o fl)
        × Attached oc k (unsub so) × Holds so E (Flat′.outerO op f E o fl oc)
        × val (Flat.active fl) ≡ count ls
        × Σ (List (Cut h)) (λ gone → val (Flat.lanes fl) ++ gone ≡ switches ls × All (λ c → val (Kit.live c) ≡ false) gone)
        × HoldsLanes op f E o fl ls
      Holds (connectˢ S c b kb k fd rp e rt src bd) E o =
        Attached c k (unsub src) × val b ≡ kb × Stashed kb (unsub bd)
        × Holds src E (feeder S) × Holds bd (S ∷ᴬ E) (bodyO c o)
      Holds (joinˢ j sk l x st)               E o = slotIs sk (joinerCb l o)
      Holds (deferˢ k s)                      E o = Stashed k (unsub s) × Holds s E o
      Holds _                                 E o = Lift _ ⊤

      HoldsLanes : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Env Δ h → Observer B h → Flat A h → List (Lane h Δ B) → Set₁
      HoldsLanes op f E o fl []                = Lift _ ⊤
      HoldsLanes op f E o fl (lane c k s ∷ ls) = Attached c k (unsub s) × Holds s E (Flat′.laneO op f E o fl c) × HoldsLanes op f E o fl ls

    ----------------------------------------------------------------------
    -- The queue, the subjects

    -- Every live timer is a pending frame's, and every pending frame of a
    -- cold not spent is queued.
    Timed : List (Timer h) → List (Timer h) → Set₁
    Timed ts ps = All (λ tm → spentʰ (Timer.handle tm) ≡ true ⊎ tm ∈ᴸ ps) ts
                × All (λ tm → spentʰ (Timer.handle tm) ≡ false → tm ∈ᴸ ts) ps

    -- A subscriber no joiner the tree holds: silenced for good.
    Silenced : ∀ {A} → Sink h A × Pos → Set₁
    Silenced {A} (sk , j) = Σ (Ref h (base Bool)) λ l → Σ (Observer A h) λ o → val l ≡ false × slotIs sk (joinerCb l o)

    -- Every subject's subscribers are its joiners, in the order they
    -- joined, and those the tree no longer holds, silenced.
    Joined : List (Σ Set λ A → Subject A h) → List (Joiner h) → Set₁
    Joined ss js = All (λ { (A , S) → let xs = val (Subject.subscribers S) in
                          All (λ { (sk , j) → joiner S sk j ∈ᴸ js ⊎ Silenced (sk , j) }) xs
                        × Linked (λ x y → proj₂ x <ᵖ proj₂ y ≡ true) xs }) ss
                 × All (λ { (joiner S sk j) → (sk , j) ∈ᴸ val (Subject.subscribers S) }) js

  ------------------------------------------------------------------------
  -- The machine's control and stack, against the witness

  -- A node somewhere below `t`.
  record Spot {h Δ₀ A₀} (t : Sub h Δ₀ A₀) : Set₁ where
    constructor spot
    field
      {Δ}  : List Set
      {A}  : Set
      {u}  : Sub h Δ A
      path : Path t u

  -- A call owed, and the position it runs at.
  Job : ∀ {h} → Sub h [] R → Set₁
  Job t = Pos × Call t

  at⟦_⟧ : ∀ {h} {t : Sub h [] R} → Pos → List (Call t) → List (Job t)
  at⟦ p ⟧ []       = []
  at⟦ p ⟧ (k ∷ ks) = (p , k) ∷ at⟦ p ⟧ ks

  -- A played cold's burst, as the driver holds it.
  playingOf : ∀ {h Δ A τ r i u} {t : Sub h [] R} {sk : Sink h A} {hd} {fr : Frame A u}
            → Path t (coldˢ {Δ = Δ} sk hd (playing τ r i fr)) → Bool → Playing h
  playingOf {r = r} {i} {u} {sk = sk} {hd} {fr} _ pl =
    record { sink = sk ; handle = hd ; at′ = u ; under′ = r ; index = i ; frame = fr ; polled = pl }

  -- A fired cold's burst, as the timer's pop made it: its first step, at
  -- the frame's cascade.
  firedOf : ∀ {h Δ A τ e v u x} {t : Sub h [] R} {sk : Sink h A} {hd} {fr : Frame A u}
          → Path t (coldˢ {Δ = Δ} sk hd (fired {u = v} τ e (at u x fr))) → Playing h
  firedOf {τ = τ} {e} {u = u} {sk = sk} {hd} {fr} _ =
    record { sink = sk ; handle = hd ; at′ = u ; under′ = ix (τ + u) ∷ subᴾ e ∷ [] ; index = 0 ; frame = fr ; polled = false }

  module Against {h : World} (t : Sub h [] R) where
    -- A burst the driver holds: a cold the witness has playing, or fired,
    -- not yet polled for this step; or one over, the machine to resume.
    data BurstAs : Maybe (Playing h) → Set₁ where
      playsAs : ∀ {Δ A τ r i u} {sk : Sink h A} {hd} {fr : Frame A u}
                (π : Path t (coldˢ {Δ = Δ} sk hd (playing τ r i fr))) → BurstAs (just (playingOf π false))
      firesAs : ∀ {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
                (π : Path t (coldˢ {Δ = Δ} sk hd (fired {u = v} τ e (at u x fr)))) → BurstAs (just (firedOf π))
      overAs  : BurstAs nothing

    -- A stack the driver holds over: the bottom, or what follows a cold's
    -- start.  The turn is reached nowhere else, and a delivery or a poll
    -- the driver feeds returns to the stack it held.
    data Held {w} : Stack w ⊤ → Set₁ where
      bottomᴴ : Held bottom
      restᴴ   : ∀ {u B} {m : Act w B} {ρ : u ⊑ w} {K : Stack u B} → Held (push (rest m) ρ K)

    -- Each frame, run in the current world, the agenda up to `_≗_`, at
    -- the position the frame resumes at: a scope's, the one it puts back;
    -- any other, the one control returns to it at.  A delivery the driver
    -- fed returns to the burst it came from.  Indexed by the position
    -- control returns at, and the driver's bursts the stack's own.  A
    -- scope's position below the one it returns from.
    data StackAs : ∀ {w} → Pos → w ⊑ h → Stack w ⊤ → List (Maybe (Playing h)) → Set₁ where
      bottomAs : ∀ {w p} {σ : w ⊑ h} → StackAs p σ bottom []
      restAs   : ∀ {u w p bs} {m : Act w ⊤} {ρ : u ⊑ w} {σ : w ⊑ h} {K} (ks : List (Call t))
               → wkAct σ m ≗ ⟦ ks ⟧ → StackAs p (ρ ⨾ σ) K bs → StackAs p σ (push (rest m) ρ K) bs
      backAs   : ∀ {u w p bs} q {m : Act w ⊤} {ρ : u ⊑ w} {σ : w ⊑ h} {K} (ks : List (Call t)) → q <ᵖ p ≡ true
               → wkAct σ m ≗ ⟦ ks ⟧ → StackAs q (ρ ⨾ σ) K bs → StackAs p σ (push (back q m) ρ K) bs
      reholdAs : ∀ {u w p bs b} {ρ : u ⊑ w} {σ : w ⊑ h} {K}
               → BurstAs b → Held K → StackAs p (ρ ⨾ σ) K bs → StackAs p σ (push rehold ρ K) (b ∷ bs)

    -- THE RE-ENTRY STATES: the driver's turn with nothing held; a value
    -- about to be recorded, the agenda its continuation; the agenda about
    -- to run; a subscription about to begin at its pending node, compiled
    -- in some world its subjects were weakened from; a cold's frame about
    -- to step.
    data CtlAs : Pos → Ctl h → List (Maybe (Playing h)) → Set₁ where
      calmAs  : ∀ {w p} {σ : w ⊑ h} → CtlAs p (holding σ bottom) []
      noteAs  : ∀ {w p a bs} {k : ⊤ → Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → k tt ≗ ⟦ ks ⟧ → StackAs p σ K bs → CtlAs p (asking (note a) k σ K) bs
      runAs   : ∀ {w p bs} {act : Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → act ≗ ⟦ ks ⟧ → StackAs p σ K bs → CtlAs p (run act σ K) bs
      subAs   : ∀ {w Δ A bs} {s : Obs Timeline Δ A} {q} {act : Act h ⊤} {σ : w ⊑ h} {K} (π : Path t (pendingˢ s q))
              → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ env (walk π top)
                   × act ≗ compile s E′ υ (obs (walk π top)) (kont (walk π top)))
              → StackAs q σ K bs → CtlAs q (run act σ K) bs
      burstAs : ∀ {w p bs b} {σ : w ⊑ h} {K} → BurstAs (just b) → Held K → StackAs p σ K bs → CtlAs p (holding σ K) (just b ∷ bs)

    -- What is owed, gathered from the control and the stack: the calls on
    -- the agenda, at their positions; the bursts in flight; the
    -- subscriptions reached and not begun, the one under way and every
    -- connect's source its `srcC` owes.
    stackJobs : ∀ {w p σ bs} {K : Stack w ⊤} → StackAs p σ K bs → List (Job t)
    stackJobs bottomAs             = []
    stackJobs (restAs {p = p} ks _ K) = at⟦ p ⟧ ks ++ stackJobs K
    stackJobs (backAs q ks _ _ K)  = at⟦ q ⟧ ks ++ stackJobs K
    stackJobs (reholdAs _ _ K)     = stackJobs K

    burstSpots : ∀ {b} → BurstAs b → List (Spot t)
    burstSpots (playsAs π) = spot π ∷ []
    burstSpots (firesAs π) = spot π ∷ []
    burstSpots overAs      = []

    stackBursts : ∀ {w p σ bs} {K : Stack w ⊤} → StackAs p σ K bs → List (Spot t)
    stackBursts bottomAs        = []
    stackBursts (restAs _ _ K)  = stackBursts K
    stackBursts (backAs _ _ _ _ K) = stackBursts K
    stackBursts (reholdAs b _ K) = burstSpots b ++ stackBursts K

    agenda : ∀ {p c bs} → CtlAs p c bs → List (Job t)
    agenda calmAs                  = []
    agenda (noteAs {p = p} ks _ K) = at⟦ p ⟧ ks ++ stackJobs K
    agenda (runAs {p = p} ks _ K)  = at⟦ p ⟧ ks ++ stackJobs K
    agenda (subAs _ _ K)           = stackJobs K
    agenda (burstAs _ _ K)         = stackJobs K

    bursts : ∀ {p c bs} → CtlAs p c bs → List (Spot t)
    bursts calmAs         = []
    bursts (noteAs _ _ K) = stackBursts K
    bursts (runAs _ _ K)  = stackBursts K
    bursts (subAs _ _ K)  = stackBursts K
    bursts (burstAs b _ K) = burstSpots b ++ stackBursts K

    sources : List (Job t) → List (Spot t)
    sources []                  = []
    sources ((_ , srcC π) ∷ js) = spot (π ⊕ in-source here) ∷ sources js
    sources (_ ∷ js)            = sources js

    begins : ∀ {p c bs} → CtlAs p c bs → List (Spot t)
    begins ca@(subAs π _ _) = spot π ∷ sources (agenda ca)
    begins ca               = sources (agenda ca)

    -- Each call runs where its node says: an `of`'s rest at the `of`, a
    -- takeWhile's completion at its failing value, a feed at the value
    -- or the end it carries, a connect's source one level down from the
    -- position it is subscribed under.
    Placed : Job t → Set
    Placed (p , emitC {p = p′} _)  = p ≡ p′
    Placed (p , take1C {q = k} _)  = p ≡ k
    Placed (p , feedC {r = q} _)   = p ≡ q
    Placed (p , finC {r = q} _)    = p ≡ q
    Placed (p , srcC {q = q} _)    = q ≡ p ++ [ ix 1 ]
    Placed _                       = ⊤

    -- Where the clock stands: a callback's position is at its tick, a
    -- burst's frame at its own; the turn has none.  Every frame the
    -- stack resumes at, and every burst it holds, the same: the clock
    -- does not move while anything is held.
    BurstClocked : ∀ {b} → ℕ → BurstAs b → Set
    BurstClocked n (playsAs {τ = τ} {r} {u = u} _) = n ≡ τ + u × n ≡ tick r
    BurstClocked n (firesAs {τ = τ} {u = u} _)     = n ≡ τ + u
    BurstClocked n overAs                          = ⊤

    Ticked : ∀ {w p σ bs} {K : Stack w ⊤} → ℕ → StackAs p σ K bs → Set
    Ticked n bottomAs                 = ⊤
    Ticked n (restAs {p = p} _ _ K)   = n ≡ tick p × Ticked n K
    Ticked n (backAs q _ _ _ K)       = n ≡ tick q × Ticked n K
    Ticked n (reholdAs b _ K)         = BurstClocked n b × Ticked n K

    Clocked : ∀ {p c bs} → ℕ → CtlAs p c bs → Set
    Clocked n calmAs              = ⊤
    Clocked {p} n (noteAs _ _ K)  = n ≡ tick p × Ticked n K
    Clocked {p} n (runAs _ _ K)   = n ≡ tick p × Ticked n K
    Clocked {p} n (subAs _ _ K)   = n ≡ tick p × Ticked n K
    Clocked n (burstAs b _ K)     = BurstClocked n b × Ticked n K

  ------------------------------------------------------------------------
  -- THE RELATION, one record per concern

  -- EVERYTHING DUE BEFORE THE NEXT TURN IS OWED: an `of`'s rest to the
  -- agenda; a playing or fired cold's frame to a burst in flight; a subscription
  -- reached and not begun to the one under way, or to a connect's source
  -- the agenda owes; a live takeWhile's completion and cut, and a
  -- connect's feed, to the agenda; and every call run where its node
  -- says.
  record Owned {h} (H : Heapᴹ h) (t : Sub h [] R) {p ctl bs} (ca : Against.CtlAs t p ctl bs) : Set₁ where
    open At H
    open Against t
    field
      ofs    : ∀ {Δ A q i xs} (π : Path t (ofˢ {Δ = Δ} {A} q i xs)) → (q , emitC π) ∈ agenda ca
      plays  : ∀ {Δ A s hd τ r i u} {b : Frame A u} (π : Path t (coldˢ {Δ = Δ} s hd (playing τ r i b)))
             → spentʰ hd ≡ false → spot π ∈ bursts ca
      fires  : ∀ {Δ A s hd τ e u} {m : From A u} (π : Path t (coldˢ {Δ = Δ} s hd (fired τ e m)))
             → spentʰ hd ≡ false → spot π ∈ bursts ca
      begun  : ∀ {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) → spot π ∈ begins ca
      ends   : ∀ {Δ A i p c k q n} {s : Sub h Δ A} (π : Path t (takeWhileˢ i p c k (ending q n) s))
             → val (Kit.live c) ≡ true → (q , take1C π) ∈ agenda ca
      cuts   : ∀ {Δ A i p c k} {s : Sub h Δ A} (π : Path t (takeWhileˢ i p c k taken s))
             → val (Kit.live c) ≡ true → Σ Pos λ q → (q , take2C π) ∈ agenda ca
      feeds  : ∀ {Δ A B S c b kb k x q ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → (π : Path t (connectˢ S c b kb k (feeding x q ss) rp e rt s bd)) → (q , feedC π) ∈ agenda ca
      fins   : ∀ {Δ A B S c b kb k q ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → (π : Path t (connectˢ S c b kb k (finishing q ss) rp e rt s bd)) → (q , finC π) ∈ agenda ca
      bodies : ∀ {Δ A B S c b kb k fd e rp rt q} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → (π : Path t (connectˢ S c b kb k fd rp e rt s bd)) → (q , bodyC π) ∈ agenda ca → part bd ≡ nothing
      placed : All Placed (agenda ca)

  -- Every subscription against what its kernel registered; below a closed
  -- gate, every cold unsubscribing reaches spent.
  record Kernels {h} (H : Heapᴹ h) (t : Sub h [] R) : Set₁ where
    open At H
    field
      holds : Holds t []ᴬ rootObs
      gated : Gated t

  -- Every live joiner holding what its feed owes it.
  record Meaning {h} (H : Heapᴹ h) (t : Sub h [] R) : Set₁ where
    open At H
    field
      fed : Fed t []ᴬ

  -- The queue, its pending frames and dead ones, in order, each due no earlier than now
  -- and past where the run is; the subjects' subscribers its joiners.
  record Queue {h} (H : Heapᴹ h) (p : Pos) (clock : ℕ) (timers : List (Timer h)) (t : Sub h [] R) : Set₁ where
    open At H
    field
      timed   : Timed timers (pendings t)
      joined  : Joined (subjects t) (joiners t []ᴬ)
      ordered : Linked (λ x y → cascade x <ᵖ cascade y ≡ true) timers
      ahead   : All (λ tm → clock ≤ Timer.due tm × p <ᵖ cascade tm ≡ true) timers

  -- The names all distinct; the clock where the control says; nothing
  -- owed the driver; the root not done.
  record Books {h} (t : Sub h [] R) {p ctl bs} (ca : Against.CtlAs t p ctl bs) (m : Mach) : Set₁ where
    field
      fresh   : AllPairs _≢_ (names t)
      clocked : Against.Clocked t (Mach.clock m) ca
      paidUp  : Mach.todo m ≡ []
      running : Mach.ended m ≡ false

  -- Whether the ghost holds the path's end: every takeWhile live and
  -- taking, every lane live, every connect open.
  isTaking : ∀ {Δ A} → Taking Δ A → Bool
  isTaking taking = true
  isTaking _      = false

  mutual
    seen : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Bool
    seen H here                              = true
    seen H (in-map p)                        = seen H p
    seen H (in-scan p)                       = seen H p
    seen H (in-take {c = c} {tk = tk} p)     = At.val H (Kit.live c) ∧ isTaking tk ∧ seen H p
    seen H (in-outer p)                      = seen H p
    seen H (in-lanes p)                      = seenL H p
    seen H (in-source {bd = bd} p)           = is-just (At.part H bd) ∧ seen H p
    seen H (in-body {e = e} {t = t} p)       = (is-just (At.part H t) ∨ is-just e) ∧ seen H p
    seen H (in-defer p)                      = seen H p

    seenL : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Bool
    seenL H (this-lane {c = c} p) = At.val H (Kit.live c) ∧ seen H p
    seenL H (next-lane p)         = seenL H p

  ∧-split : ∀ x {y} → x ∧ y ≡ true → x ≡ true × y ≡ true
  ∧-split true  p = refl , p
  ∧-split false ()

  ∧-join : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
  ∧-join refl refl = refl

  false≢ : ∀ {a} {X : Set a} → false ≡ true → X
  false≢ ()

  -- A path held is each of its halves held.
  module _ {h} (H : Heapᴹ h) where
    private
      ∧-assoc₃ : ∀ a b x y → a ∧ b ∧ x ∧ y ≡ (a ∧ b ∧ x) ∧ y
      ∧-assoc₃ a b x y = sym (trans (∧-assoc a (b ∧ x) y) (cong (a ∧_) (∧-assoc b x y)))

    mutual
      seen-⊕ : ∀ {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (ψ : Path u v)
             → seen H (ρ ⊕ ψ) ≡ seen H ρ ∧ seen H ψ
      seen-⊕ here          ψ = refl
      seen-⊕ (in-map ρ)    ψ = seen-⊕ ρ ψ
      seen-⊕ (in-scan ρ)   ψ = seen-⊕ ρ ψ
      seen-⊕ (in-take {c = c} {tk = tk} ρ) ψ =
        trans (cong (λ z → At.val H (Kit.live c) ∧ isTaking tk ∧ z) (seen-⊕ ρ ψ)) (∧-assoc₃ (At.val H (Kit.live c)) (isTaking tk) (seen H ρ) (seen H ψ))
      seen-⊕ (in-outer ρ)  ψ = seen-⊕ ρ ψ
      seen-⊕ (in-lanes πL) ψ = seenL-⊕ πL ψ
      seen-⊕ (in-source {bd = bd} ρ) ψ =
        trans (cong (is-just (At.part H bd) ∧_) (seen-⊕ ρ ψ)) (sym (∧-assoc (is-just (At.part H bd)) (seen H ρ) (seen H ψ)))
      seen-⊕ (in-body {e = e} {t = t} ρ) ψ =
        trans (cong ((is-just (At.part H t) ∨ is-just e) ∧_) (seen-⊕ ρ ψ)) (sym (∧-assoc (is-just (At.part H t) ∨ is-just e) (seen H ρ) (seen H ψ)))
      seen-⊕ (in-defer ρ)  ψ = seen-⊕ ρ ψ

      seenL-⊕ : ∀ {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (ψ : Path u v)
              → seenL H (πL ⊕ᴸ ψ) ≡ seenL H πL ∧ seen H ψ
      seenL-⊕ (this-lane {c = c} ρ) ψ =
        trans (cong (At.val H (Kit.live c) ∧_) (seen-⊕ ρ ψ)) (sym (∧-assoc (At.val H (Kit.live c)) (seen H ρ) (seen H ψ)))
      seenL-⊕ (next-lane πL) ψ = seenL-⊕ πL ψ

    seen-join : ∀ {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (ψ : Path u v)
              → seen H ρ ≡ true → seen H ψ ≡ true → seen H (ρ ⊕ ψ) ≡ true
    seen-join ρ ψ sρ sψ = trans (seen-⊕ ρ ψ) (cong₂ _∧_ sρ sψ)

  -- What the ghost holds at a path's end, held, it holds at every node
  -- above.
  module _ {h} (H : Heapᴹ h) where
    open At H

    private
      Filled : ∀ {X : Set₁} → List X → Set
      Filled []      = ⊥
      Filled (_ ∷ _) = ⊤

      map-just : ∀ {X Y : Set₁} (f : X → Y) (m : Maybe X) → is-just m ≡ true → is-just (mapᴹ f m) ≡ true
      map-just f (just _) _ = refl
      map-just f nothing  ()

      outer-just : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) ls qs pl
                 → is-just o ≡ true → is-just (merged op g o ls qs pl) ≡ true
      outer-just op g (just _) ls qs pl _ = refl
      outer-just op g nothing  ls qs pl ()

      lanes-just : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) ls qs pl
                 → Filled ls → is-just (merged op g o ls qs pl) ≡ true
      lanes-just op g (just _) ls      qs pl _ = refl
      lanes-just op g nothing  (_ ∷ _) qs pl _ = refl
      lanes-just op g nothing  []      qs pl ()

      cons-holds : ∀ {X : Set₁} (m : Maybe X) xs → is-just m ≡ true → Filled (consᴹ m xs)
      cons-holds (just _) xs _ = tt
      cons-holds nothing  xs ()

      cons-keeps : ∀ {X : Set₁} (m : Maybe X) xs → Filled xs → Filled (consᴹ m xs)
      cons-keeps (just _) xs _  = tt
      cons-keeps nothing  xs hs = hs

      source-just : ∀ {Δ A B} r e t (s : Maybe (U.Node Δ A)) (b : Maybe (U.Node (A ∷ Δ) B))
                  → is-just s ≡ true → is-just b ≡ true → is-just (connected r e t s b) ≡ true
      source-just r e t (just _) (just _) _  _ = refl
      source-just r e t nothing  _        () _
      source-just r e t (just _) nothing  _  ()

      body-just : ∀ {Δ A B} r e t (s : Maybe (U.Node Δ A)) (b : Maybe (U.Node (A ∷ Δ) B))
                → (is-just s ∨ is-just e) ≡ true → is-just b ≡ true → is-just (connected r e t s b) ≡ true
      body-just r e        t (just _) (just _) _  _ = refl
      body-just r (just _) t nothing  (just _) _  _ = refl
      body-just r nothing  t nothing  (just _) () _
      body-just r e        t s        nothing  _  ()

    mutual
      seen-up : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H ψ ≡ true → is-just (part u) ≡ true → is-just (part t) ≡ true
      seen-up here                         _  j = j
      seen-up (in-map {f = f} {t = s} ψ)   sn j = map-just (U.mapᶜ f) (part s) (seen-up ψ sn j)
      seen-up (in-scan {f = f} {r} {t = s} ψ) sn j = map-just (U.scanᶜ f (val r)) (part s) (seen-up ψ sn j)
      seen-up (in-take {i = i} {p} {c} {tk = taking} {t = s} ψ) sn j with val (Kit.live c)
      ... | true  = map-just (U.takeWhileᶜ i p) (part s) (seen-up ψ sn j)
      ... | false = false≢ sn
      seen-up (in-take {c = c} {tk = ending _ _} ψ) sn j = false≢ (proj₂ (∧-split (val (Kit.live c)) sn))
      seen-up (in-take {c = c} {tk = taken} ψ)      sn j = false≢ (proj₂ (∧-split (val (Kit.live c)) sn))
      seen-up (in-outer {op = op} {f} {fl} {pl = pl} {t = so} {ls} ψ) sn j =
        outer-just op (λ a q → U.subscribe (f a) q) (part so) (partLanes ls) (val (Flat.queue fl)) pl (seen-up ψ sn j)
      seen-up (in-lanes {op = op} {f} {fl} {pl = pl} {t = so} {ls} πL) sn j =
        lanes-just op (λ a q → U.subscribe (f a) q) (part so) (partLanes ls) (val (Flat.queue fl)) pl (seenL-up πL sn j)
      seen-up (in-source {e = e} {rp} {rt} {t = src} {bd} ψ) sn j with ∧-split (is-just (part bd)) sn
      ... | jb , sψ = source-just rp e rt (part src) (part bd) (seen-up ψ sψ j) jb
      seen-up (in-body {e = e} {rp} {rt} {t = src} {bd} ψ) sn j with ∧-split (is-just (part src) ∨ is-just e) sn
      ... | js , sψ = body-just rp e rt (part src) (part bd) js (seen-up ψ sψ j)
      seen-up (in-defer ψ) sn j = seen-up ψ sn j

      seenL-up : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) → seenL H πL ≡ true → is-just (part u) ≡ true
               → Filled (partLanes ls)
      seenL-up (this-lane {c = c} {t = s} {ls} ψ) sn j with val (Kit.live c)
      ... | true  = cons-holds (part s) (partLanes ls) (seen-up ψ sn j)
      ... | false = false≢ sn
      seenL-up (next-lane {l = lane c k s} {ls} πL) sn j with val (Kit.live c)
      ... | true  = cons-keeps (part s) (partLanes ls) (seenL-up πL sn j)
      ... | false = seenL-up πL sn j

  -- What the ghost is, at each state: what the witness has open; at a
  -- value about to be recorded, what steps to it by that value.
  -- Every node the ghost holds below `t` passes `P`, and so does what a
  -- held flatMap's ended parts left running, and what a held connect's
  -- ended source did.  Held: `seen`, so a teardown, which leaves what it
  -- reached unseen, answers for nothing below its switch.
  record Each {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ A} (t : Sub h Δ A) : Set₁ where
    field
      parts : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H ψ ≡ true → ∀ {c} → At.part H u ≡ just c → P c
      pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
            → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
            → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
      rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
            → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
            → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

  -- Its next event no earlier than `q`.
  Heads : ∀ {Γ A} → Pos → U.Node Γ A → Set
  Heads q c = ∀ {k} → U.headˢ (U.step c) ≡ just k → q ≤ᵖ k

  Meets : ∀ {h} {t : Sub h [] R} {p ctl bs} → Against.CtlAs t p ctl bs → Maybe (U.Node [] R) → U.Node [] R → Set₁
  Meets (Against.noteAs {p = p} {a} _ _ _) n g = Σ (U.Node [] R) λ g′ → n ≡ just g′ × U.step g ≡ U.outˢ p a g′
  Meets _                                  n g = n ≡ just g

  -- THE CONFIGURATION RUNS THE GHOST FROM A RE-ENTRY STATE: a witness
  -- holding every subscription the run reaches, whose open part is the
  -- ghost, and the machine's control and stack its agenda; the machine
  -- sorted, every frame it keeps under where it runs; every node the
  -- ghost holds heading no earlier than where the run is.
  record Carried (g : U.Node [] R) (m : Mach) : Set₁ where
    H = Conf.heap (Mach.conf m)
    field
      sane    : Sane []ᴬ g
      placed  : Placedᵍ g []ᴬ
      tree    : Sub (Conf.world (Mach.conf m)) [] R
      ctlAs   : Against.CtlAs tree (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m)) (Mach.bursts m)
      meets   : Meets ctlAs (At.part H tree) g
      owned   : Owned H tree ctlAs
      kernels : Kernels H tree
      meaning : Meaning H tree
      queue   : Queue H (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) tree
      books   : Books tree ctlAs m
      sorted  : Σ Pos λ lo → WellMach lo m
      behind  : Each H (Heads (Conf.pos (Mach.conf m))) tree

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST: carried, or the root's
  -- completion about to be shown where the ghost ends.
  --
  -- DEAD ROUTE: a contract per kernel over the histories its observer is
  --   delivered, composed by `compile`.  The contract must hold under
  --   every context the subscription runs in, and a `Ref` is a
  --   membership proof into the world, forgeable by any computation at a
  --   larger world, so some context writes `scan`'s accumulator; only
  --   the compiled program's own configuration is honest.
  -- DEAD ROUTE: a relation over `Act` blind to the heap.  `scanᴷ`'s
  --   `next` reads its accumulator from a cell and delivers `f b a`; a
  --   relation whose `readRef` case quantifies over every content must
  --   accept every `b`.
  -- DEAD ROUTE: the owed bound at the run's position.  A scope returning
  --   puts the position back above what it just delivered, so a cut
  --   record owes the events up to its last mark, which lie past it.
  -- DEAD ROUTE: a spec per observer, its triples quantifying over the
  --   frame around it.  A cut flows ownership upstream: `takeWhile`'s
  --   completion cancels its source from inside the source's own
  --   callback, so the source's cells are written within its call and
  --   cannot be framed out of it.  And a frame naming other observers'
  --   specs sits a universe above them, so no heap can store it.
  data Strong (g : U.Node [] R) (m : Mach) : Set₁ where
    carried : Carried g m → Strong g m
    closing : ∀ {h hp p w B k σ K} → Mach.conf m ≡ ⟨_,_,_⟩ {h} hp p (asking {w = w} {B = B} fin k σ K)
            → Mach.ended m ≡ false → U.step g ≡ U.endˢ p → Sane []ᴬ g → Placedᵍ g []ᴬ → Strong g m

  -- THE LAUNCH IS A SUBSCRIPTION ABOUT TO BEGIN: the program, pending at
  -- the root, nothing yet allocated or owed.
  -- A program subscribed heads at a position, never the empty one: each
  -- head is something appended to, or a timer's cascade.
  Opens : Maybe Pos → Set
  Opens nothing        = ⊤
  Opens (just [])      = ⊥
  Opens (just (_ ∷ _)) = ⊤

  opens-++ : ∀ k x → Opens (just (k ++ [ x ]))
  opens-++ []      x = tt
  opens-++ (_ ∷ _) x = tt

  opens-map : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.mapˢ f s))
  opens-map f (U.outˢ k a c) o = o
  opens-map f (U.skipˢ k c)  o = o
  opens-map f (U.endˢ k)     o = o
  opens-map f U.hushˢ        o = tt

  opens-scan : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.scanˢ f z s))
  opens-scan f z (U.outˢ k a c) o = o
  opens-scan f z (U.skipˢ k c)  o = o
  opens-scan f z (U.endˢ k)     o = o
  opens-scan f z U.hushˢ        o = tt

  opens-taking : ∀ {Γ A} i (p : A → Bool) k a (c : U.Node Γ A) b → Opens (just k) → Opens (U.headˢ (U.taking i p k a c b))
  opens-taking i     p k a c true  o = o
  opens-taking true  p k a c false o = opens-++ k (ix 0)
  opens-taking false p k a c false o = opens-++ k last

  opens-take : ∀ {Γ A} i (p : A → Bool) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.takeWhileˢ i p s))
  opens-take i p (U.outˢ k a c) o = opens-taking i p k a c (p a) o
  opens-take i p (U.skipˢ k c)  o = o
  opens-take i p (U.endˢ k)     o = o
  opens-take i p U.hushˢ        o = tt

  opens-outer : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A) → Opens (U.headˢ so)
              → Opens (U.headˢ (U.outerˢ op g o so [] [] U.idleᶜ))
  opens-outer op g o (U.outˢ q a o′) h = opens-++ q (ix 0)
  opens-outer op g o (U.skipˢ q o′)  h = h
  opens-outer op g o (U.endˢ c)      h = h
  opens-outer op g o U.hushˢ         h = tt

  opens-body : ∀ {Γ A B} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → Opens (U.headˢ sb) → Opens (U.headˢ (U.bodyˢ r s sb))
  opens-body r s (U.outˢ k a b) h = h
  opens-body r s (U.skipˢ k b)  h = h
  opens-body r s (U.endˢ c)     h = h
  opens-body r s U.hushˢ        h = tt

  opens-source : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) ss → Opens (U.headˢ sb)
               → Opens (U.headˢ (U.sourceˢ r b sb s ss))
  opens-source r b sb s (U.outˢ q a s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
  ... | true  = opens-++ q (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s (U.skipˢ q s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
  ... | true  = opens-++ q (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s (U.endˢ c) h with U.beforeˢ (c ++ [ ix 0 ]) sb
  ... | true  = opens-++ c (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s U.hushˢ h = opens-body r (U.live s) sb h

  opens-burst : ∀ {Γ A t} τ r i (f : Frame A t) → Opens (U.headˢ (U.burstˢ {Γ} τ r i f))
  opens-burst τ r i (emit a k) = opens-++ r (ix i)
  opens-burst τ r i (stall k)  = opens-++ r (ix i)
  opens-burst τ r i (close k)  = opens-++ r (ix i)

  opens-start : ∀ {Γ A} p (m : From A 0) → Opens (U.headˢ (U.step (U.startᶜ {Γ} p m)))
  opens-start p (at zero _ b)    = opens-burst (tick p) p 0 b
  opens-start p (at (suc t) _ b) = opens-burst (tick p) _ 0 b
  opens-start p doneᶠ            = opens-++ p last
  opens-start p quietᶠ           = tt

  opens-of : ∀ {Γ A} p i (xs : List A) → Opens (U.headˢ (U.ofˢ {Γ} p i xs))
  opens-of p i []       = opens-++ p last
  opens-of p i (x ∷ xs) = opens-++ p (ix i)

  opens-subscribe : ∀ {Γ A} (o : Obs Timeline Γ A) p → Opens (U.headˢ (U.step (U.subscribe o p)))
  opens-subscribe (T.cold c)          p = opens-start p (lower c)
  opens-subscribe T.empty             p = opens-++ p last
  opens-subscribe (T.of xs)           p = opens-of p 0 xs
  opens-subscribe (T.map f s)         p = opens-map f _ (opens-subscribe s p)
  opens-subscribe (T.scan f z s)      p = opens-scan f z _ (opens-subscribe s p)
  opens-subscribe (T.takeWhile i q s) p = opens-take i q _ (opens-subscribe s p)
  opens-subscribe (T.flatMap op f s)  p = opens-outer op (λ a q → U.subscribe (f a) q) (U.subscribe s p) _ (opens-subscribe s p)
  opens-subscribe (T.connect s b)     p =
    opens-source (p ++ [ ix 1 ]) (U.subscribe b (p ++ [ ix 0 ])) _ (U.subscribe s (p ++ [ ix 1 ])) (U.step (U.subscribe s (p ++ [ ix 1 ]))) (opens-subscribe b (p ++ [ ix 0 ]))
  opens-subscribe (T.connected i)     p = tt
  opens-subscribe (T.defer l)         p = opens-++ p (ix 0)

  -- The root comes before every position but the empty one.
  root-least : ∀ a q → root ≤ᵖ (a ∷ q)
  root-least (ix zero)    []      = inj₁ refl
  root-least (ix zero)    (_ ∷ _) = inj₂ refl
  root-least (ix (suc n)) q       = inj₂ refl
  root-least (subᴾ x)     q       = inj₂ refl
  root-least last         q       = inj₂ refl

  heads-open : ∀ {k} (h : Maybe Pos) → Opens h → h ≡ just k → root ≤ᵖ k
  heads-open (just (a ∷ q)) _ refl = root-least a q

  -- A program subscribed at the root heads no earlier than it: its
  -- first event under the root, or a timer's tick past it.
  heads-begin : (o : Obs Timeline [] R) → Heads root (U.subscribe o root)
  heads-begin o e = heads-open _ (opens-subscribe o root) e

  strong-begin : (o : Obs Timeline [] R) → Strong (U.subscribe o root) (begin o)
  strong-begin o = carried record
    { sane    = sane-subscribe o root (λ ())
    ; placed  = placed-subscribe o
    ; tree    = pendingˢ o root
    ; ctlAs   = Against.subAs here ([] , []ᴬ , same , refl , ≗-refl _) Against.bottomAs
    ; meets   = refl
    ; owned   = record { ofs = λ () ; plays = λ () ; fires = λ () ; begun = λ { here → Any.here refl } ; ends = λ () ; cuts = λ () ; feeds = λ () ; fins = λ () ; bodies = λ _ ()
                       ; placed = []ᴬ }
    ; kernels = record { holds = _ ; gated = _ }
    ; meaning = record { fed = _ }
    ; queue   = record { timed = []ᴬ , []ᴬ ; joined = []ᴬ , []ᴬ ; ordered = []ᴸ ; ahead = []ᴬ }
    ; books   = record { fresh = []ᴾ ; clocked = refl , tt ; paidUp = refl ; running = refl }
    ; sorted  = root , begin-well o
    ; behind  = record { parts = λ { here _ refl → heads-begin o } ; pools = λ () ; rests = λ () } }
