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
open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Linked using (Linked) renaming ([] to []ᴸ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList using (inside; Time; Pos; From; Frame; Timeline; at; emit; stall; close; ix; last; tick; root; _<ᵖ_) renaming (done to doneᶠ; quiet to quietᶠ) renaming (sub to subᴾ)
open import operation.AbstractObservable using (base; maybe; quiet; gate; module Run; module Heap) renaming (module Machine to Shared)
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
    joinerCb : ∀ {A} → Ref h gate → Observer A h → Callbacks A h
    joinerCb l o = record { onNext = λ a → readG l λ b → when b (Observer.next o a)
                          ; onComplete = readG l λ b → when b (Observer.complete o)
                          ; isClosed = readG l λ b → if b then Observer.closed o else done true }

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
      joinˢ      : ∀ {Δ A} → Pos → Sink h A → Ref h gate → A ∈ Δ → Maybe (List (Pos × Maybe A) × Maybe Pos) → Sub h Δ A
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

  ------------------------------------------------------------------------
  -- A PART OF THE RELATION: one clause per node over its children's
  -- parts, each handed what its parent inherits it.

  record Alg {ℓ : Level} (h : World) : Set (lsuc ℓ) where
    no-eta-equality
    field
      Inh    : ∀ {Δ A} → Sub h Δ A → Set ℓ
      InhL   : ∀ {Δ B} → List (Lane h Δ B) → Set ℓ
      pendᶜ  : ∀ {Δ A} (s : Obs Timeline Δ A) q → Inh (pendingˢ s q) → Set ℓ
      coldᶜ  : ∀ {Δ A} (s : Sink h A) hd ph → Inh (coldˢ {Δ = Δ} s hd ph) → Set ℓ
      ofᶜ    : ∀ {Δ} {A : Set} p i (xs : List A) → Inh (ofˢ {Δ = Δ} p i xs) → Set ℓ
      doneᶜ  : ∀ {Δ A} → Inh (doneˢ {h} {Δ} {A}) → Set ℓ
      mapᶜ   : ∀ {Δ A} {B : Set} (f : A → B) (s : Sub h Δ A) → (Inh s → Set ℓ) → Inh (mapˢ f s) → Set ℓ
      scanᶜ  : ∀ {Δ A B} (f : B → A → B) r (s : Sub h Δ A) → (Inh s → Set ℓ) → Inh (scanˢ f r s) → Set ℓ
      takeᶜ  : ∀ {Δ A} i p c k tk (s : Sub h Δ A) → (Inh s → Set ℓ) → Inh (takeWhileˢ i p c k tk s) → Set ℓ
      flatᶜ  : ∀ {Δ A B} op f fl oc k r pl (so : Sub h Δ A) (ls : List (Lane h Δ B))
             → (Inh so → Set ℓ) → (InhL ls → Set ℓ) → Inh (flatMapˢ op f fl oc k r pl so ls) → Set ℓ
      connᶜ  : ∀ {Δ A B} S c b kb k fd rp e rt (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
             → (Inh src → Set ℓ) → (Inh bd → Set ℓ) → Inh (connectˢ S c b kb k fd rp e rt src bd) → Set ℓ
      joinᶜ  : ∀ {Δ A} j sk l (x : A ∈ Δ) st → Inh (joinˢ j sk l x st) → Set ℓ
      deferᶜ : ∀ {Δ A} k (s : Sub h Δ A) → (Inh s → Set ℓ) → Inh (deferˢ k s) → Set ℓ
      nilᶜ   : ∀ {Δ B} → InhL {Δ} {B} [] → Set ℓ
      consᶜ  : ∀ {Δ B} c k (s : Sub h Δ B) (ls : List (Lane h Δ B)) → (Inh s → Set ℓ) → (InhL ls → Set ℓ) → InhL (lane c k s ∷ ls) → Set ℓ

  module Fold {ℓ} {h} (a : Alg {ℓ} h) where
    open Alg a
    mutual
      fold : ∀ {Δ A} (u : Sub h Δ A) → Inh u → Set ℓ
      fold (pendingˢ s q)                          = pendᶜ s q
      fold (coldˢ s hd ph)                         = coldᶜ s hd ph
      fold (ofˢ p i xs)                            = ofᶜ p i xs
      fold doneˢ                                   = doneᶜ
      fold (mapˢ f s)                              = mapᶜ f s (fold s)
      fold (scanˢ f r s)                           = scanᶜ f r s (fold s)
      fold (takeWhileˢ i p c k tk s)               = takeᶜ i p c k tk s (fold s)
      fold (flatMapˢ op f fl oc k r pl so ls)      = flatᶜ op f fl oc k r pl so ls (fold so) (foldL ls)
      fold (connectˢ S c b kb k fd rp e rt src bd) = connᶜ S c b kb k fd rp e rt src bd (fold src) (fold bd)
      fold (joinˢ j sk l x st)                     = joinᶜ j sk l x st
      fold (deferˢ k s)                            = deferᶜ k s (fold s)

      foldL : ∀ {Δ B} (ls : List (Lane h Δ B)) → InhL ls → Set ℓ
      foldL []                = nilᶜ
      foldL (lane c k s ∷ ls) = consᶜ c k s ls (fold s) (foldL ls)

  -- Once a subscription is attached.
  Once : ∀ {ℓ h} → Maybe (Quiet h) → Set ℓ → Set ℓ
  Once nothing  X = Lift _ ⊤
  Once (just _) X = X

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

  -- A subscription whose unsubscribe still reaches one not yet begun.
  Owes : ∀ {h Δ A} → Sub h Δ A → Set
  Owes (pendingˢ s q)                       = ⊤
  Owes (mapˢ f s)                           = Owes s
  Owes (scanˢ f r s)                        = Owes s
  Owes (connectˢ S c b kb k fd rp e rt s bd) = Owes s
  Owes _                                    = ⊥

  -- NOTHING IS STASHED BEFORE IT IS BEGUN: a kernel's continuation runs
  -- once its subscription is made, so no detacher is held over one its
  -- unsubscribe still owes.
  Begun : ∀ {h Δ A} → Maybe (Quiet h) → Sub h Δ A → Set
  Begun nothing  s = ⊤
  Begun (just _) s = ¬ Owes s

  SettledAlg : ∀ {h} → Alg h
  SettledAlg = record
    { Inh    = λ _ → ⊤
    ; InhL   = λ _ → ⊤
    ; pendᶜ  = λ _ _ _ → ⊤
    ; coldᶜ  = λ _ _ _ _ → ⊤
    ; ofᶜ    = λ _ _ _ _ → ⊤
    ; doneᶜ  = λ _ → ⊤
    ; mapᶜ   = λ _ _ X → X
    ; scanᶜ  = λ _ _ _ X → X
    ; takeᶜ  = λ _ _ _ k _ s X i → Begun k s × X i
    ; flatᶜ  = λ _ _ _ _ k _ _ so _ X L i → Begun k so × X i × L tt
    ; connᶜ  = λ _ _ _ kb k _ _ _ _ s bd X Y i → Begun k s × Begun kb bd × X i × Y tt
    ; joinᶜ  = λ _ _ _ _ _ _ → ⊤
    ; deferᶜ = λ k s X i → Begun k s × X i
    ; nilᶜ   = λ _ → ⊤
    ; consᶜ  = λ _ k s _ X L i → Begun k s × X tt × L i }

  Settled : ∀ {h Δ A} → Sub h Δ A → Set
  Settled u = Fold.fold SettledAlg u tt

  SettledLanes : ∀ {h Δ B} → List (Lane h Δ B) → Set
  SettledLanes ls = Fold.foldL SettledAlg ls tt

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

  -- A path, then nothing.
  mutual
    ⊕-here : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → π ⊕ here ≡ π
    ⊕-here here          = refl
    ⊕-here (in-map π)    = cong in-map (⊕-here π)
    ⊕-here (in-scan π)   = cong in-scan (⊕-here π)
    ⊕-here (in-take π)   = cong in-take (⊕-here π)
    ⊕-here (in-outer π)  = cong in-outer (⊕-here π)
    ⊕-here (in-lanes π)  = cong in-lanes (⊕-hereᴸ π)
    ⊕-here (in-source π) = cong in-source (⊕-here π)
    ⊕-here (in-body π)   = cong in-body (⊕-here π)
    ⊕-here (in-defer π)  = cong in-defer (⊕-here π)

    ⊕-hereᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → π ⊕ᴸ here ≡ π
    ⊕-hereᴸ (this-lane π) = cong this-lane (⊕-here π)
    ⊕-hereᴸ (next-lane π) = cong next-lane (⊕-hereᴸ π)

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
  -- A node whose kernel calls the continuation it was handed: one
  -- beneath which nothing runs.  Every other kernel hands its
  -- continuation on to a child, so a continuation owed is a leaf's.
  data Leaf {h} : ∀ {Δ A} → Sub h Δ A → Set₁ where
    of-leaf   : ∀ {Δ A p i xs} → Leaf (ofˢ {Δ = Δ} {A} p i xs)
    cold-leaf : ∀ {Δ A s hd ph} → Leaf (coldˢ {Δ = Δ} {A} s hd ph)
    done-leaf : ∀ {Δ A} → Leaf (doneˢ {Δ = Δ} {A})
    join-leaf : ∀ {Δ A j s l i ns} → Leaf (joinˢ {Δ = Δ} {A} j s l i ns)

  data Call {h} (t : Sub h [] R) : Set₁ where
    emitC  : ∀ {Δ A} {p i xs} → Path t (ofˢ {Δ = Δ} {A} p i xs) → Call t
    kontC  : ∀ {Δ A} {u : Sub h Δ A} → Leaf u → Path t u → Call t
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
  code (kontC {u = u} _ π)               = kont (walk π top) same (unsubscribing (unsub u))
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
    -- What a subscription leaves running past its end

    -- A source's node: what it shows while it runs, else what it left.
    sourced : ∀ {Δ A} → Maybe (U.Node Δ A) → U.Node Δ A → U.Node Δ A
    sourced (just s) _ = s
    sourced nothing  t = t

    -- Read off the witness past every flag and pool: each connect's
    -- source run under where it subscribed, beside its body's leftover;
    -- a pending node's, once begun.
    mutual
      leftover : ∀ {Δ A B} → Sub h Δ A → U.Node Δ B
      leftover (pendingˢ s q)                     = U.restᶜ (U.subscribe s q)
      leftover (coldˢ s hd ph)                    = U.idleᶜ
      leftover (ofˢ p i xs)                       = U.idleᶜ
      leftover doneˢ                              = U.idleᶜ
      leftover (mapˢ f s)                         = leftover s
      leftover (scanˢ f r s)                      = leftover s
      leftover (takeWhileˢ i p c k tk s)          = leftover s
      leftover (flatMapˢ op f fl oc k r pl so ls) = U.unionᶜ (leftover so) (leftoverL ls)
      leftover (connectˢ S c b kb k fd rp e rt src bd) =
        U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) (leftover {B = ⊤} bd))
        where n = sourced (part src) (leftover src)
      leftover (joinˢ j sk l x st)                = U.idleᶜ
      leftover (deferˢ k s)                       = leftover s

      leftoverL : ∀ {Δ A B} → List (Lane h Δ A) → U.Node Δ B
      leftoverL []                = U.idleᶜ
      leftoverL (lane c k s ∷ ls) = U.unionᶜ (leftover s) (leftoverL ls)

    -- What a flatMap's pool runs, by its own flags, which turn as its
    -- pool takes a rest: its outer's leftover once it heard the outer
    -- end, each lane's once it cut the lane.
    pooledL : ∀ {Δ A B} → List (Lane h Δ A) → U.Node Δ B
    pooledL []                = U.idleᶜ
    pooledL (lane c k s ∷ ls) = if val (Kit.live c) then pooledL ls else U.unionᶜ (leftover s) (pooledL ls)

    pooled : ∀ {Δ A B} → Flat A h → Sub h Δ A → List (Lane h Δ B) → U.Node Δ B
    pooled fl so ls = U.unionᶜ (if val (Flat.outerDone fl) then leftover so else U.idleᶜ) (pooledL ls)

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
    FedAlg : Alg {lsuc lzero} h
    Alg.Inh FedAlg {Δ} _ = Now Δ
    Alg.InhL FedAlg {Δ} _ = Now Δ
    Alg.pendᶜ FedAlg = λ _ _ _ → Lift _ ⊤
    Alg.coldᶜ FedAlg = λ _ _ _ _ → Lift _ ⊤
    Alg.ofᶜ FedAlg = λ _ _ _ _ → Lift _ ⊤
    Alg.doneᶜ FedAlg = λ _ → Lift _ ⊤
    Alg.mapᶜ FedAlg = λ _ _ X → X
    Alg.scanᶜ FedAlg = λ _ _ _ X → X
    Alg.takeᶜ FedAlg = λ _ _ _ _ _ _ X → X
    Alg.flatᶜ FedAlg = λ _ _ _ _ _ _ _ _ _ X L ν → X ν × L ν
    Alg.connᶜ FedAlg = λ _ _ _ _ _ fd _ e _ _ _ X Y ν → X ν × Y ((fd , e) ∷ᴬ ν)
    Alg.joinᶜ FedAlg = λ j sk l x st ν → let (fd , e) = lookup ν x in
                   Lift _ (val l ≡ true → (Owed fd sk j → st ≡ owing fd j) × (¬ Owed fd sk j → st ≡ owingNone e))
    Alg.deferᶜ FedAlg = λ _ _ X → X
    Alg.nilᶜ FedAlg = λ _ → Lift _ ⊤
    Alg.consᶜ FedAlg = λ _ _ _ _ X L ν → X ν × L ν

    Fed : ∀ {Δ A} → Sub h Δ A → Now Δ → Set₁
    Fed = Fold.fold FedAlg

    FedLanes : ∀ {Δ B} → List (Lane h Δ B) → Now Δ → Set₁
    FedLanes = Fold.foldL FedAlg

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
    SpentAlg : Alg {lsuc lzero} h
    Alg.Inh SpentAlg = λ _ → Lift _ ⊤
    Alg.InhL SpentAlg = λ _ → Lift _ ⊤
    Alg.pendᶜ SpentAlg = λ _ _ _ → Lift _ ⊤
    Alg.coldᶜ SpentAlg = λ _ hd _ _ → Lift _ (spentʰ hd ≡ true)
    Alg.ofᶜ SpentAlg = λ _ _ _ _ → Lift _ ⊤
    Alg.doneᶜ SpentAlg = λ _ → Lift _ ⊤
    Alg.mapᶜ SpentAlg = λ _ _ X → X
    Alg.scanᶜ SpentAlg = λ _ _ _ X → X
    Alg.takeᶜ SpentAlg = λ _ _ _ k _ _ X i → Once k (X i)
    Alg.flatᶜ SpentAlg = λ _ _ _ _ k _ _ _ _ X L i → Once k (X i) × L (lift tt)
    Alg.connᶜ SpentAlg = λ _ _ _ kb k _ _ _ _ _ _ X Y i → Once k (X i) × Once kb (Y (lift tt))
    Alg.joinᶜ SpentAlg = λ _ _ _ _ _ _ → Lift _ ⊤
    Alg.deferᶜ SpentAlg = λ k _ X i → Once k (X i)
    Alg.nilᶜ SpentAlg = λ _ → Lift _ ⊤
    Alg.consᶜ SpentAlg = λ _ k _ _ X L i → Once k (X (lift tt)) × L i

    Spent : ∀ {Δ A} → Sub h Δ A → Set₁
    Spent u = Fold.fold SpentAlg u (lift tt)

    SpentLanes : ∀ {Δ B} → List (Lane h Δ B) → Set₁
    SpentLanes ls = Fold.foldL SpentAlg ls (lift tt)

    -- Below a subscription once attached, what unsubscribing reaches
    -- spent.
    Cut↓ : ∀ {Δ A} → Maybe (Quiet h) → Sub h Δ A → Set₁
    Cut↓ k s = Once k (Spent s)

    unended : ∀ {A} → Phase A → Bool
    unended (waiting _ _ doneᶠ) = false
    unended _                    = true

    -- Below a cut kill switch, a cut lane or a connect's thrown switch,
    -- what unsubscribing reaches is spent once attached; no live cold
    -- waits on its end, which its frame's last step delivers. A connect's
    -- body ending does not tear its source: the source stays live until
    -- the switch is thrown, and a note can fall in between.
    --
    -- A dead lane its flatMap still lists is excused: the teardown cuts
    -- it again.  A lane's completion runs before the cut it owes, as an
    -- inner takeWhile's or a connect body's does, so its slot frees with
    -- what it subscribed to still live.
    --
    -- REFUTED: c0bd1892 of a connect's source torn once its body's part is gone, by a concat whose next lane emits from inside the body's completion
    GatedAlg : Alg {lsuc lzero} h
    Alg.Inh GatedAlg = λ _ → Lift _ ⊤
    Alg.InhL GatedAlg = λ _ → Lift _ (List (Cut h))
    Alg.pendᶜ GatedAlg = λ _ _ _ → Lift _ ⊤
    Alg.coldᶜ GatedAlg = λ _ hd ph _ → Lift _ (spentʰ hd ≡ false → unended ph ≡ true)
    Alg.ofᶜ GatedAlg = λ _ _ _ _ → Lift _ ⊤
    Alg.doneᶜ GatedAlg = λ _ → Lift _ ⊤
    Alg.mapᶜ GatedAlg = λ _ _ X → X
    Alg.scanᶜ GatedAlg = λ _ _ _ X → X
    Alg.takeᶜ GatedAlg = λ _ _ c k _ s X i → (val (Kit.live c) ≡ false → Cut↓ k s) × X i
    Alg.flatᶜ GatedAlg = λ _ _ fl _ _ _ _ _ _ X L i → X i × L (lift (val (Flat.lanes fl)))
    Alg.connᶜ GatedAlg = λ _ c _ _ k _ _ _ _ src _ X Y i → (val (Kit.live c) ≡ false → Cut↓ k src) × X i × Y (lift tt)
    Alg.joinᶜ GatedAlg = λ _ _ _ _ _ _ → Lift _ ⊤
    Alg.deferᶜ GatedAlg = λ _ _ X → X
    Alg.nilᶜ GatedAlg = λ _ → Lift _ ⊤
    Alg.consᶜ GatedAlg = λ c k s _ X L xs → (val (Kit.live c) ≡ false → c ∈ᴸ lower xs ⊎ Cut↓ k s) × X (lift tt) × L xs

    Gated : ∀ {Δ A} → Sub h Δ A → Set₁
    Gated u = Fold.fold GatedAlg u (lift tt)

    GatedLanes : ∀ {Δ B} → List (Cut h) → List (Lane h Δ B) → Set₁
    GatedLanes xs ls = Fold.foldL GatedAlg ls (lift xs)

    ----------------------------------------------------------------------
    -- Every subscription against its kernel

    -- What a flatMap hands its lanes.
    record Lanes (Δ : List Set) (B : Set) : Set₁ where
      constructor lanesAt
      field
        {A} : Set
        op  : T.FlatOp
        f   : A → Obs Timeline Δ B
        E   : Env Δ h
        o   : Observer B h
        fl  : Flat A h

    HoldsAlg : Alg {lsuc lzero} h
    Alg.Inh HoldsAlg {Δ} {A} _ = Env Δ h × Observer A h
    Alg.InhL HoldsAlg {Δ} {B} _ = Lanes Δ B
    Alg.pendᶜ HoldsAlg = λ _ _ _ → Lift _ ⊤
    Alg.coldᶜ HoldsAlg = λ s _ _ i → slotIs s (cbOf (proj₂ i))
    Alg.ofᶜ HoldsAlg = λ _ _ _ _ → Lift _ ⊤
    Alg.doneᶜ HoldsAlg = λ _ → Lift _ ⊤
    Alg.mapᶜ HoldsAlg = λ f _ X i → X (proj₁ i , mapO f (proj₂ i))
    Alg.scanᶜ HoldsAlg = λ f r _ X i → X (proj₁ i , scanO f r (proj₂ i))
    Alg.takeᶜ HoldsAlg = λ i p c k _ s X e → Attached c k (unsub s) × X (proj₁ e , takeWhileO i p c (proj₂ e))
    Alg.flatᶜ HoldsAlg = λ op f fl oc k r _ so ls X L i →
          val (Flat.refill fl) ≡ just r × slotIs r (Flat′.refillCb op f (proj₁ i) (proj₂ i) fl)
          × Attached oc k (unsub so) × X (proj₁ i , Flat′.outerO op f (proj₁ i) (proj₂ i) fl oc)
          × val (Flat.active fl) ≡ count ls
          × Σ (List (Cut h)) (λ gone → val (Flat.lanes fl) ++ gone ≡ switches ls × All (λ c → val (Kit.live c) ≡ false) gone)
          × L (lanesAt op f (proj₁ i) (proj₂ i) fl)
    Alg.connᶜ HoldsAlg = λ S c b kb k _ _ _ _ src bd X Y i →
          Attached c k (unsub src) × val b ≡ kb × Stashed kb (unsub bd)
          × X (proj₁ i , feeder S) × Y (S ∷ᴬ proj₁ i , bodyO c (proj₂ i))
    Alg.joinᶜ HoldsAlg = λ _ sk l _ _ i → slotIs sk (joinerCb l (proj₂ i))
    Alg.deferᶜ HoldsAlg = λ k s X i → Stashed k (unsub s) × X i
    Alg.nilᶜ HoldsAlg = λ _ → Lift _ ⊤
    Alg.consᶜ HoldsAlg = λ c k s _ X L la → Attached c k (unsub s)
          × X (Lanes.E la , Flat′.laneO (Lanes.op la) (Lanes.f la) (Lanes.E la) (Lanes.o la) (Lanes.fl la) c) × L la

    Holds : ∀ {Δ A} → Sub h Δ A → Env Δ h → Observer A h → Set₁
    Holds u E o = Fold.fold HoldsAlg u (E , o)

    HoldsLanes : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Env Δ h → Observer B h → Flat A h → List (Lane h Δ B) → Set₁
    HoldsLanes op f E o fl ls = Fold.foldL HoldsAlg ls (lanesAt op f E o fl)

    ----------------------------------------------------------------------
    -- The queue, the subjects

    -- Every live timer is a pending frame's, and every pending frame of a
    -- cold not spent is queued.
    Timed : List (Timer h) → List (Timer h) → Set₁
    Timed ts ps = All (λ tm → spentʰ (Timer.handle tm) ≡ true ⊎ tm ∈ᴸ ps) ts
                × All (λ tm → spentʰ (Timer.handle tm) ≡ false → tm ∈ᴸ ts) ps

    -- A subscriber no joiner the tree holds: silenced for good.
    Silenced : ∀ {A} → Sink h A × Pos → Set₁
    Silenced {A} (sk , j) = Σ (Ref h gate) λ l → Σ (Observer A h) λ o → val l ≡ false × slotIs sk (joinerCb l o)

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

    -- What is owed, gathered from the control and the stack: the calls on
    -- the agenda, at their positions; the bursts in flight; the
    -- subscriptions reached and not begun, the one under way and every
    -- connect's source its `srcC` owes.
    stackJobs : ∀ {w p σ bs} {K : Stack w ⊤} → StackAs p σ K bs → List (Job t)
    stackJobs bottomAs             = []
    stackJobs (restAs {p = p} ks _ K) = at⟦ p ⟧ ks ++ stackJobs K
    stackJobs (backAs q ks _ _ K)  = at⟦ q ⟧ ks ++ stackJobs K
    stackJobs (reholdAs _ _ K)     = stackJobs K

    -- A call owing a pending node's subscription: a connect's `srcC`, the
    -- node its source.
    data SrcOf {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) : Call t → Set₁ where
      src-of : ∀ {B S c b kb k fd e rp rt} {bd : Sub h (A ∷ Δ) B} (ρ : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
             → π ≡ ρ ⊕ in-source here → SrcOf π (srcC ρ)

    -- THE RE-ENTRY STATES: the driver's turn with nothing held; a value
    -- about to be recorded, the agenda its continuation; the agenda about
    -- to run; a subscription about to begin at its pending node, compiled
    -- in some world its subjects were weakened from, and owed by no call
    -- on the stack; a cold's frame about to step.
    data CtlAs : Pos → Ctl h → List (Maybe (Playing h)) → Set₁ where
      calmAs  : ∀ {w p} {σ : w ⊑ h} → CtlAs p (holding σ bottom) []
      noteAs  : ∀ {w p a bs} {k : ⊤ → Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → k tt ≗ ⟦ ks ⟧ → StackAs p σ K bs → CtlAs p (asking (note a) k σ K) bs
      runAs   : ∀ {w p bs} {act : Act h ⊤} {σ : w ⊑ h} {K} (ks : List (Call t))
              → act ≗ ⟦ ks ⟧ → StackAs p σ K bs → CtlAs p (run act σ K) bs
      subAs   : ∀ {w Δ A bs} {s : Obs Timeline Δ A} {q} {act : Act h ⊤} {σ : w ⊑ h} {K} (π : Path t (pendingˢ s q))
              → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ env (walk π top)
                   × act ≗ compile s E′ υ (obs (walk π top)) (kont (walk π top)))
              → (sk : StackAs q σ K bs) → All (λ j → ¬ SrcOf π (proj₂ j)) (stackJobs sk) → CtlAs q (run act σ K) bs
      burstAs : ∀ {w p bs b} {σ : w ⊑ h} {K} → BurstAs (just b) → Held K → StackAs p σ K bs → CtlAs p (holding σ K) (just b ∷ bs)

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
    agenda (subAs _ _ K _)         = stackJobs K
    agenda (burstAs _ _ K)         = stackJobs K

    bursts : ∀ {p c bs} → CtlAs p c bs → List (Spot t)
    bursts calmAs         = []
    bursts (noteAs _ _ K) = stackBursts K
    bursts (runAs _ _ K)  = stackBursts K
    bursts (subAs _ _ K _) = stackBursts K
    bursts (burstAs b _ K) = burstSpots b ++ stackBursts K

    sources : List (Job t) → List (Spot t)
    sources []                  = []
    sources ((_ , srcC π) ∷ js) = spot (π ⊕ in-source here) ∷ sources js
    sources (_ ∷ js)            = sources js

    begins : ∀ {p c bs} → CtlAs p c bs → List (Spot t)
    begins ca@(subAs π _ _ _) = spot π ∷ sources (agenda ca)
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
    Clocked {p} n (subAs _ _ K _) = n ≡ tick p × Ticked n K
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

  -- `Owned`, node by node: each node handed the path to it from the
  -- root, as a context closing any path below it.
  module Owning {h} (H : Heapᴹ h) (t : Sub h [] R) (Ag : Job t → Set₁) (Bu Be : Spot t → Set₁) where
    open At H

    Ctx : ∀ {Δ A} → Sub h Δ A → Set₁
    Ctx u = ∀ {Δ′ A′} {w : Sub h Δ′ A′} → Path u w → Path t w

    CtxL : ∀ {Δ B} → List (Lane h Δ B) → Set₁
    CtxL ls = ∀ {Δ′ A′} {w : Sub h Δ′ A′} → PathLanes ls w → Path t w

    coldOwed : ∀ {Δ A} {s : Sink h A} {hd} (ph : Phase A) → Path t (coldˢ {Δ = Δ} s hd ph) → Set₁
    coldOwed         (waiting _ _ _)   π = Lift _ ⊤
    coldOwed {hd = hd} (fired _ _ _)   π = spentʰ hd ≡ false → Bu (spot π)
    coldOwed {hd = hd} (playing _ _ _ _) π = spentʰ hd ≡ false → Bu (spot π)

    takeOwed : ∀ {Δ A i p c k} (tk : Taking Δ A) {s : Sub h Δ A} → Path t (takeWhileˢ i p c k tk s) → Set₁
    takeOwed         taking       π = Lift _ ⊤
    takeOwed {c = c} (ending q n) π = val (Kit.live c) ≡ true → Ag (q , take1C π)
    takeOwed {c = c} taken        π = val (Kit.live c) ≡ true → Σ Pos λ q → Ag (q , take2C π)

    feedOwed : ∀ {Δ A B S c b kb k rp e rt} (fd : Feed A h) {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Path t (connectˢ S c b kb k fd rp e rt src bd) → Set₁
    feedOwed idle             π = Lift _ ⊤
    feedOwed (feeding x q ss) π = Ag (q , feedC π)
    feedOwed (finishing q ss) π = Ag (q , finC π)

    OwnedAlg : Alg {lsuc lzero} h
    Alg.Inh    OwnedAlg u = Ctx u
    Alg.InhL   OwnedAlg ls = CtxL ls
    Alg.pendᶜ  OwnedAlg s q κ = Be (spot (κ here))
    Alg.coldᶜ  OwnedAlg s hd ph κ = coldOwed ph (κ here)
    Alg.ofᶜ    OwnedAlg p i xs κ = Ag (p , emitC (κ here))
    Alg.doneᶜ  OwnedAlg κ = Lift _ ⊤
    Alg.mapᶜ   OwnedAlg f s X κ = X (λ ψ → κ (in-map ψ))
    Alg.scanᶜ  OwnedAlg f r s X κ = X (λ ψ → κ (in-scan ψ))
    Alg.takeᶜ  OwnedAlg i p c k tk s X κ = takeOwed tk (κ here) × X (λ ψ → κ (in-take ψ))
    Alg.flatᶜ  OwnedAlg op f fl oc k r pl so ls X L κ = X (λ ψ → κ (in-outer ψ)) × L (λ ψ → κ (in-lanes ψ))
    Alg.connᶜ  OwnedAlg S c b kb k fd rp e rt src bd X Y κ =
      feedOwed fd (κ here) × (∀ {q} → Ag (q , bodyC (κ here)) → part bd ≡ nothing) × X (λ ψ → κ (in-source ψ)) × Y (λ ψ → κ (in-body ψ))
    Alg.joinᶜ  OwnedAlg j sk l x st κ = Lift _ ⊤
    Alg.deferᶜ OwnedAlg k s X κ = X (λ ψ → κ (in-defer ψ))
    Alg.nilᶜ   OwnedAlg κ = Lift _ ⊤
    Alg.consᶜ  OwnedAlg c k s ls X L κ = X (λ ψ → κ (this-lane ψ)) × L (λ ψ → κ (next-lane ψ))

    -- The fold, followed down a path.
    mutual
      reach : ∀ {Δ A Δ′ A′} {u : Sub h Δ A} {w : Sub h Δ′ A′} (κ : Ctx u) → Fold.fold OwnedAlg u κ
            → (ψ : Path u w) → Fold.fold OwnedAlg w (λ ρ → κ (ψ ⊕ ρ))
      reach κ f here          = f
      reach κ f (in-map ψ)    = reach (λ ρ → κ (in-map ρ)) f ψ
      reach κ f (in-scan ψ)   = reach (λ ρ → κ (in-scan ρ)) f ψ
      reach κ f (in-take ψ)   = reach (λ ρ → κ (in-take ρ)) (proj₂ f) ψ
      reach κ f (in-outer ψ)  = reach (λ ρ → κ (in-outer ρ)) (proj₁ f) ψ
      reach κ f (in-lanes ψ)  = reachL (λ ρ → κ (in-lanes ρ)) (proj₂ f) ψ
      reach κ f (in-source ψ) = reach (λ ρ → κ (in-source ρ)) (proj₁ (proj₂ (proj₂ f))) ψ
      reach κ f (in-body ψ)   = reach (λ ρ → κ (in-body ρ)) (proj₂ (proj₂ (proj₂ f))) ψ
      reach κ f (in-defer ψ)  = reach (λ ρ → κ (in-defer ρ)) f ψ

      reachL : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {w : Sub h Δ′ A′} (κ : CtxL ls) → Fold.foldL OwnedAlg ls κ
             → (ψ : PathLanes ls w) → Fold.fold OwnedAlg w (λ ρ → κ (ψ ⊕ᴸ ρ))
      reachL κ f (this-lane ψ) = reach (λ ρ → κ (this-lane ρ)) (proj₁ f) ψ
      reachL κ f (next-lane ψ) = reachL (λ ρ → κ (next-lane ρ)) (proj₂ f) ψ

  record OwnedF {h} (H : Heapᴹ h) (t : Sub h [] R) {p ctl bs} (ca : Against.CtlAs t p ctl bs) : Set₁ where
    constructor _,ᴼ_
    field
      ownedᶠ  : Fold.fold (Owning.OwnedAlg H t (_∈ Against.agenda t ca) (_∈ Against.bursts t ca) (_∈ Against.begins t ca)) t (λ π → π)
      placedᶠ : All (Against.Placed t) (Against.agenda t ca)

  module _ {h} {H : Heapᴹ h} {t : Sub h [] R} {p ctl bs} {ca : Against.CtlAs t p ctl bs} where
    open At H
    open Against t
    private module O = Owning H t (_∈ agenda ca) (_∈ bursts ca) (_∈ begins ca)

    owned-from : OwnedF H t ca → Owned H t ca
    owned-from (f ,ᴼ pl) = record
      { ofs    = λ {q = q} π → subst (λ π′ → (q , emitC π′) ∈ agenda ca) (⊕-here π) (down π)
      ; plays  = λ π sp → subst (λ π′ → spot π′ ∈ bursts ca) (⊕-here π) (down π sp)
      ; fires  = λ π sp → subst (λ π′ → spot π′ ∈ bursts ca) (⊕-here π) (down π sp)
      ; begun  = λ π → subst (λ π′ → spot π′ ∈ begins ca) (⊕-here π) (down π)
      ; ends   = λ {q = q} π lv → subst (λ π′ → (q , take1C π′) ∈ agenda ca) (⊕-here π) (proj₁ (down π) lv)
      ; cuts   = λ π lv → let (q , m) = proj₁ (down π) lv in q , subst (λ π′ → (q , take2C π′) ∈ agenda ca) (⊕-here π) m
      ; feeds  = λ {q = q} π → subst (λ π′ → (q , feedC π′) ∈ agenda ca) (⊕-here π) (proj₁ (down π))
      ; fins   = λ {q = q} π → subst (λ π′ → (q , finC π′) ∈ agenda ca) (⊕-here π) (proj₁ (down π))
      ; bodies = λ {q = q} π m → proj₁ (proj₂ (down π)) (subst (λ π′ → (q , bodyC π′) ∈ agenda ca) (sym (⊕-here π)) m)
      ; placed = pl }
      where
        down : ∀ {Δ A} {u : Sub h Δ A} (π : Path t u) → Fold.fold O.OwnedAlg u (λ ρ → π ⊕ ρ)
        down π = O.reach (λ ρ → ρ) f π

    mutual
      owned-at : Owned H t ca → ∀ {Δ A} (u : Sub h Δ A) (κ : O.Ctx u) → Fold.fold O.OwnedAlg u κ
      owned-at ow (pendingˢ s q)                     κ = Owned.begun ow (κ here)
      owned-at ow (coldˢ s hd (waiting _ _ _))       κ = lift tt
      owned-at ow (coldˢ s hd (fired _ _ _))         κ = Owned.fires ow (κ here)
      owned-at ow (coldˢ s hd (playing _ _ _ _))     κ = Owned.plays ow (κ here)
      owned-at ow (ofˢ p i xs)                       κ = Owned.ofs ow (κ here)
      owned-at ow doneˢ                              κ = lift tt
      owned-at ow (mapˢ f s)                         κ = owned-at ow s (λ ψ → κ (in-map ψ))
      owned-at ow (scanˢ f r s)                      κ = owned-at ow s (λ ψ → κ (in-scan ψ))
      owned-at ow (takeWhileˢ i p c k taking s)      κ = lift tt , owned-at ow s (λ ψ → κ (in-take ψ))
      owned-at ow (takeWhileˢ i p c k (ending q n) s) κ = Owned.ends ow (κ here) , owned-at ow s (λ ψ → κ (in-take ψ))
      owned-at ow (takeWhileˢ i p c k taken s)       κ = Owned.cuts ow (κ here) , owned-at ow s (λ ψ → κ (in-take ψ))
      owned-at ow (flatMapˢ op f fl oc k r pl so ls) κ = owned-at ow so (λ ψ → κ (in-outer ψ)) , owned-atL ow ls (λ ψ → κ (in-lanes ψ))
      owned-at ow (connectˢ S c b kb k fd rp e rt src bd) κ =
        feed fd (κ here) , (λ {q} → Owned.bodies ow {q = q} (κ here)) , owned-at ow src (λ ψ → κ (in-source ψ)) , owned-at ow bd (λ ψ → κ (in-body ψ))
        where
          feed : ∀ (fd′ : Feed _ h) (π : Path t (connectˢ S c b kb k fd′ rp e rt src bd)) → O.feedOwed fd′ π
          feed idle             π = lift tt
          feed (feeding x q ss) π = Owned.feeds ow π
          feed (finishing q ss) π = Owned.fins ow π
      owned-at ow (joinˢ j sk l x st)                κ = lift tt
      owned-at ow (deferˢ k s)                       κ = owned-at ow s (λ ψ → κ (in-defer ψ))

      owned-atL : Owned H t ca → ∀ {Δ B} (ls : List (Lane h Δ B)) (κ : O.CtxL ls) → Fold.foldL O.OwnedAlg ls κ
      owned-atL ow []                κ = lift tt
      owned-atL ow (lane c k s ∷ ls) κ = owned-at ow s (λ ψ → κ (this-lane ψ)) , owned-atL ow ls (λ ψ → κ (next-lane ψ))

    owned-to : Owned H t ca → OwnedF H t ca
    owned-to ow = owned-at ow t (λ π → π) ,ᴼ Owned.placed ow

  -- Every subscription against what its kernel registered; below a closed
  -- gate, every cold unsubscribing reaches spent.
  record Kernels {h} (H : Heapᴹ h) (t : Sub h [] R) : Set₁ where
    open At H
    field
      holds   : Holds t []ᴬ rootObs
      gated   : Gated t
      settled : Settled t

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

  -- Two steps alike as rests: the same pin, or none.
  data Pinned {Γ} {B C : Set} : U.Step Γ B → U.Step Γ C → Set₁ where
    pinned   : ∀ {k x y} → Pinned (U.skipˢ k x) (U.skipˢ k y)
    unpinned : Pinned U.hushˢ U.hushˢ

  pinned-trans : ∀ {Γ B C D} {a : U.Step Γ B} {b : U.Step Γ C} {c : U.Step Γ D} → Pinned a b → Pinned b c → Pinned a c
  pinned-trans pinned   pinned   = pinned
  pinned-trans unpinned unpinned = unpinned

  pinned-skip : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} {q y′} → Pinned a b → b ≡ U.skipˢ q y′ → Σ (U.Node Γ B) λ x′ → a ≡ U.skipˢ q x′
  pinned-skip pinned refl = _ , refl

  union-pinned : ∀ {Γ B C} {x y : U.Node Γ B} {sx sy} {x′ y′ : U.Node Γ C} {sx′ sy′}
               → Pinned sx sx′ → Pinned sy sy′ → Pinned (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)
  union-pinned (pinned {k}) (pinned {k′}) with k <ᵖ k′
  ... | true  = pinned
  ... | false = pinned
  union-pinned pinned   unpinned = pinned
  union-pinned unpinned q        = q

  under-pinned : ∀ {Γ A D B C} (s : U.Source Γ A) (st : U.Step (A ∷ Γ) D) → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s st)
  under-pinned s (U.skipˢ _ _)  = pinned
  under-pinned s (U.outˢ _ _ _) = unpinned
  under-pinned s (U.endˢ _)     = unpinned
  under-pinned s U.hushˢ        = unpinned

  -- A node's rest pins alike whatever it is read as.
  mutual
    rest-pinned : ∀ {Γ A B C} (c : U.Node Γ A) → Pinned (U.restˢ {B = B} c) (U.restˢ {B = C} c)
    rest-pinned (U.framesᶜ _ _ _)               = unpinned
    rest-pinned (U.burstᶜ _ _ _ _)              = unpinned
    rest-pinned (U.ofᶜ _ _ _)                   = unpinned
    rest-pinned (U.mapᶜ _ c)                    = rest-pinned c
    rest-pinned (U.scanᶜ _ _ c)                 = rest-pinned c
    rest-pinned (U.takeWhileᶜ _ _ c)            = rest-pinned c
    rest-pinned (U.flatMapᶜ _ _ o ls _ p)       = union-pinned (restᴹ-pinned o) (union-pinned (rests-pinned ls) (rest-pinned p))
    rest-pinned (U.joinᶜ _ _ _ _)               = unpinned
    rest-pinned {A = A} (U.connectᶜ r b (U.live s))    = union-pinned (bursts-pinned r s (U.step s)) (under-pinned (U.live s) (U.restˢ {B = A} b))
    rest-pinned {A = A} (U.connectᶜ r b (U.ended c t)) = union-pinned (bursts-pinned r t (U.step t)) (under-pinned (U.ended c t) (U.restˢ {B = A} b))
    rest-pinned (U.deferᶜ _ _ _)                = unpinned
    rest-pinned (U.endingᶜ _ n)                 = rest-pinned n
    rest-pinned (U.restᶜ n)                     = rest-pinned n
    rest-pinned U.idleᶜ                         = unpinned
    rest-pinned (U.unionᶜ x y)                  = union-pinned (rest-pinned x) (rest-pinned y)
    rest-pinned (U.burstingᶜ r t)               = bursts-pinned r t (U.step t)
    rest-pinned (U.underᶜ {C = D} s b)          = under-pinned s (U.restˢ {B = D} b)

    bursts-pinned : ∀ {Γ A B C} (r : Pos) (t : U.Node Γ A) (st : U.Step Γ A) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t st)
    bursts-pinned r t (U.outˢ k _ _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.skipˢ k _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.endˢ _) = rest-pinned t
    bursts-pinned r t U.hushˢ    = rest-pinned t

    restᴹ-pinned : ∀ {Γ A B C} (o : Maybe (U.Node Γ A)) → Pinned (U.restᴹ {B = B} o) (U.restᴹ {B = C} o)
    restᴹ-pinned nothing  = unpinned
    restᴹ-pinned (just o) = rest-pinned o

    rests-pinned : ∀ {Γ A B C} (ls : List (U.Node Γ A)) → Pinned (U.restsˢ {B = B} ls) (U.restsˢ {B = C} ls)
    rests-pinned []       = unpinned
    rests-pinned (l ∷ ls) = union-pinned (rest-pinned l) (rests-pinned ls)

  -- A rest's shape: it steps as it rests.
  data Restful {Γ B} : U.Node Γ B → Set₁ where
    rf-idle  : Restful U.idleᶜ
    rf-rest  : ∀ {A} {n : U.Node Γ A} → Restful (U.restᶜ n)
    rf-union : ∀ {x y} → Restful (U.unionᶜ x y)
    rf-burst : ∀ {A r} {t : U.Node Γ A} → Restful (U.burstingᶜ r t)
    rf-under : ∀ {A C} {s : U.Source Γ A} {b : U.Node (A ∷ Γ) C} → Restful (U.underᶜ s b)

  restful-pinned : ∀ {Γ B} {c : U.Node Γ B} → Restful c → Pinned (U.step c) (U.restˢ {B = B} c)
  restful-pinned rf-idle                    = unpinned
  restful-pinned (rf-rest {n = n})          = rest-pinned n
  restful-pinned (rf-union {x = x} {y})     = union-pinned (rest-pinned x) (rest-pinned y)
  restful-pinned (rf-burst {r = r} {t = t}) = bursts-pinned r t (U.step t)
  restful-pinned (rf-under {C = C} {s = s} {b = b}) = under-pinned s (U.restˢ {B = C} b)

  pinned-sym : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} → Pinned a b → Pinned b a
  pinned-sym pinned   = pinned
  pinned-sym unpinned = unpinned

  -- A body's rest pins as its own, whatever source it carries.
  under-moved : ∀ {Γ A D E B C} (s s′ : U.Source Γ A) {st : U.Step (A ∷ Γ) D} {st′ : U.Step (A ∷ Γ) E}
              → Pinned st st′ → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s′ st′)
  under-moved s s′ pinned   = pinned
  under-moved s s′ unpinned = unpinned

  -- A burst pins as its node's step, and past it as the node's rest.
  bursts-moved : ∀ {Γ A A′ B C} r {t : U.Node Γ A} {t′ : U.Node Γ A′} {st : U.Step Γ A} {st′ : U.Step Γ A′}
               → Pinned st st′ → Pinned (U.restˢ {B = B} t) (U.restˢ {B = C} t′) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t′ st′)
  bursts-moved r (pinned {k}) rp with inside r k
  ... | true  = pinned
  ... | false = rp
  bursts-moved r unpinned rp = rp

  -- A node's next pin a rest's: what a held node keeps of its ended
  -- parts steps as they would rest.
  Tied : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
  Tied x y = Pinned (U.step x) (U.restˢ {B = ⊤} y)

  -- WHAT A HELD NODE KEEPS OF ITS ENDED PARTS IS WHAT THEY STILL RUN.
  -- Below `t`: a held flatMap's pool runs as its ended parts' leftovers,
  -- a held connect's ended source's rest as the source's.
  record Lingers {h} (H : Heapᴹ h) {Δ A} (t : Sub h Δ A) : Set₁ where
    field
      pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
            → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
            → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Tied pl (At.pooled H fl so ls)
      rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
            → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
            → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Tied rt (At.leftover H {B = ⊤} src)

  -- WHAT HOLDS BELOW A HELD NODE, NODE BY NODE: each node's obligation
  -- once it is held, each child held as its parent is and its step
  -- holds; a held flatMap's pool and a held connect's rest besides.
  module Held {h} (H : Heapᴹ h) (Nd Pl Rs : ∀ {Δ A} → Sub h Δ A → Set₁) where
    open At H

    If : Bool → Set₁ → Set₁
    If b X = b ≡ true → X

    HeldAlg : Alg {lsuc lzero} h
    Alg.Inh    HeldAlg _ = Lift _ Bool
    Alg.InhL   HeldAlg _ = Lift _ Bool
    Alg.pendᶜ  HeldAlg s q hb = If (lower hb) (Nd (pendingˢ s q))
    Alg.coldᶜ  HeldAlg {Δ} s hd ph hb = If (lower hb) (Nd (coldˢ {Δ = Δ} s hd ph))
    Alg.ofᶜ    HeldAlg {Δ} p i xs hb = If (lower hb) (Nd (ofˢ {Δ = Δ} p i xs))
    Alg.doneᶜ  HeldAlg {Δ} {A} hb = If (lower hb) (Nd (doneˢ {h} {Δ} {A}))
    Alg.mapᶜ   HeldAlg f s X hb = If (lower hb) (Nd (mapˢ f s)) × X hb
    Alg.scanᶜ  HeldAlg f r s X hb = If (lower hb) (Nd (scanˢ f r s)) × X hb
    Alg.takeᶜ  HeldAlg i p c k tk s X hb =
      If (lower hb) (Nd (takeWhileˢ i p c k tk s)) × X (lift (lower hb ∧ val (Kit.live c) ∧ isTaking tk))
    Alg.flatᶜ  HeldAlg op f fl oc k r pl so ls X L hb =
      If (lower hb) (Nd (flatMapˢ op f fl oc k r pl so ls)) × If (lower hb) (Pl (flatMapˢ op f fl oc k r pl so ls)) × X hb × L hb
    Alg.connᶜ  HeldAlg S c b kb k fd rp e rt src bd X Y hb =
      If (lower hb) (Nd (connectˢ S c b kb k fd rp e rt src bd)) × If (lower hb) (Rs (connectˢ S c b kb k fd rp e rt src bd))
      × X (lift (lower hb ∧ is-just (part bd))) × Y (lift (lower hb ∧ (is-just (part src) ∨ is-just e)))
    Alg.joinᶜ  HeldAlg j sk l x st hb = If (lower hb) (Nd (joinˢ j sk l x st))
    Alg.deferᶜ HeldAlg k s X hb = If (lower hb) (Nd (deferˢ k s)) × X hb
    Alg.nilᶜ   HeldAlg _ = Lift _ ⊤
    Alg.consᶜ  HeldAlg c k s ls X L hb = X (lift (lower hb ∧ val (Kit.live c))) × L hb

    Below : ∀ {Δ A} → Sub h Δ A → Set₁
    Below t = Fold.fold HeldAlg t (lift true)

    -- The same, read along every held path.
    record Over {Δ A} (t : Sub h Δ A) : Set₁ where
      field
        nodes : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H ψ ≡ true → Nd u
        pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
              → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true → Pl (flatMapˢ op f fl oc k r pl so ls)
        rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true → Rs (connectˢ S c b kb k fd rp e rt src bd)

    record OverL {Δ B} (ls : List (Lane h Δ B)) : Set₁ where
      field
        nodes : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : PathLanes ls u) → seenL H ψ ≡ true → Nd u
        pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
              → (ψ : PathLanes ls (flatMapˢ op f fl oc k r pl so ls′)) → seenL H ψ ≡ true → Pl (flatMapˢ op f fl oc k r pl so ls′)
        rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL H ψ ≡ true → Rs (connectˢ S c b kb k fd rp e rt src bd)

    restrict : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Over t → (ρ : Path t u) → seen H ρ ≡ true → Over u
    restrict O ρ sρ = record
      { nodes = λ ψ s → Over.nodes O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s)
      ; pools = λ ψ s → Over.pools O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s)
      ; rests = λ ψ s → Over.rests O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s) }

    private
      lanesOf : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Over (flatMapˢ op f fl oc k r pl so ls) → OverL ls
      lanesOf O = record
        { nodes = λ ψ s → Over.nodes O (in-lanes ψ) s
        ; pools = λ ψ s → Over.pools O (in-lanes ψ) s
        ; rests = λ ψ s → Over.rests O (in-lanes ψ) s }

      thisOf : ∀ {Δ B c k} {s : Sub h Δ B} {ls} → OverL (lane c k s ∷ ls) → val (Kit.live c) ≡ true → Over s
      thisOf O v = record
        { nodes = λ ψ s → OverL.nodes O (this-lane ψ) (∧-join v s)
        ; pools = λ ψ s → OverL.pools O (this-lane ψ) (∧-join v s)
        ; rests = λ ψ s → OverL.rests O (this-lane ψ) (∧-join v s) }

      nextOf : ∀ {Δ B} {l : Lane h Δ B} {ls} → OverL (l ∷ ls) → OverL ls
      nextOf O = record
        { nodes = λ ψ s → OverL.nodes O (next-lane ψ) s
        ; pools = λ ψ s → OverL.pools O (next-lane ψ) s
        ; rests = λ ψ s → OverL.rests O (next-lane ψ) s }

      nd : ∀ {Δ A} {t : Sub h Δ A} {hb} → (hb ≡ true → Over t) → If hb (Nd t)
      nd O e = Over.nodes (O e) here refl

    mutual
      below : ∀ {Δ A} (t : Sub h Δ A) hb → (hb ≡ true → Over t) → Fold.fold HeldAlg t (lift hb)
      below (pendingˢ s q)                          hb O = nd O
      below (coldˢ s hd ph)                         hb O = nd O
      below (ofˢ p i xs)                            hb O = nd O
      below doneˢ                                   hb O = nd O
      below (mapˢ f s)                              hb O = nd O , below s hb (λ e → restrict (O e) (in-map here) refl)
      below (scanˢ f r s)                           hb O = nd O , below s hb (λ e → restrict (O e) (in-scan here) refl)
      below (takeWhileˢ i p c k tk s)               hb O =
        nd O , below s _ (λ e → let (e₁ , e₂) = ∧-split hb e ; (e₃ , e₄) = ∧-split (val (Kit.live c)) e₂
                                 in restrict (O e₁) (in-take here) (∧-join e₃ (∧-join e₄ refl)))
      below (flatMapˢ op f fl oc k r pl so ls)      hb O =
        nd O , (λ e → Over.pools (O e) here refl) , below so hb (λ e → restrict (O e) (in-outer here) refl) , belowL ls hb (λ e → lanesOf (O e))
      below (connectˢ S c b kb k fd rp e rt src bd) hb O =
        nd O , (λ x → Over.rests (O x) here refl)
        , below src _ (λ x → let (x₁ , x₂) = ∧-split hb x in restrict (O x₁) (in-source here) (∧-join x₂ refl))
        , below bd _ (λ x → let (x₁ , x₂) = ∧-split hb x in restrict (O x₁) (in-body here) (∧-join x₂ refl))
      below (joinˢ j sk l x st)                     hb O = nd O
      below (deferˢ k s)                            hb O = nd O , below s hb (λ e → restrict (O e) (in-defer here) refl)

      belowL : ∀ {Δ B} (ls : List (Lane h Δ B)) hb → (hb ≡ true → OverL ls) → Fold.foldL HeldAlg ls (lift hb)
      belowL []                hb O = lift tt
      belowL (lane c k s ∷ ls) hb O =
        below s _ (λ e → let (e₁ , e₂) = ∧-split hb e in thisOf (O e₁) e₂) , belowL ls hb (λ e → nextOf (O e))

    mutual
      reach : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {hb} → Fold.fold HeldAlg t (lift hb) → hb ≡ true
            → (ψ : Path t u) → seen H ψ ≡ true → Fold.fold HeldAlg u (lift true)
      reach f refl here           _ = f
      reach f refl (in-map ψ)     s = reach (proj₂ f) refl ψ s
      reach f refl (in-scan ψ)    s = reach (proj₂ f) refl ψ s
      reach f refl (in-take {c = c} {tk = tk} ψ) s =
        let (e₁ , e₂) = ∧-split (val (Kit.live c)) s ; (e₃ , e₄) = ∧-split (isTaking tk) e₂ in reach (proj₂ f) (∧-join e₁ e₃) ψ e₄
      reach f refl (in-outer ψ)   s = reach (proj₁ (proj₂ (proj₂ f))) refl ψ s
      reach f refl (in-lanes ψ)   s = reachL (proj₂ (proj₂ (proj₂ f))) refl ψ s
      reach f refl (in-source {bd = bd} ψ) s =
        let (e₁ , e₂) = ∧-split (is-just (part bd)) s in reach (proj₁ (proj₂ (proj₂ f))) e₁ ψ e₂
      reach f refl (in-body {e = e} {t = src} ψ) s =
        let (e₁ , e₂) = ∧-split (is-just (part src) ∨ is-just e) s in reach (proj₂ (proj₂ (proj₂ f))) e₁ ψ e₂
      reach f refl (in-defer ψ)   s = reach (proj₂ f) refl ψ s

      reachL : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {hb} → Fold.foldL HeldAlg ls (lift hb) → hb ≡ true
             → (ψ : PathLanes ls u) → seenL H ψ ≡ true → Fold.fold HeldAlg u (lift true)
      reachL f refl (this-lane {c = c} ψ) s = let (e₁ , e₂) = ∧-split (val (Kit.live c)) s in reach (proj₁ f) e₁ ψ e₂
      reachL f refl (next-lane ψ)         s = reachL (proj₂ f) refl ψ s

    private
      node : ∀ {Δ A} (u : Sub h Δ A) → Below u → Nd u
      node (pendingˢ s q)                          f = f refl
      node (coldˢ s hd ph)                         f = f refl
      node (ofˢ p i xs)                            f = f refl
      node doneˢ                                   f = f refl
      node (mapˢ g s)                              f = proj₁ f refl
      node (scanˢ g r s)                           f = proj₁ f refl
      node (takeWhileˢ i p c k tk s)               f = proj₁ f refl
      node (flatMapˢ op g fl oc k r pl so ls)      f = proj₁ f refl
      node (connectˢ S c b kb k fd rp e rt src bd) f = proj₁ f refl
      node (joinˢ j sk l x st)                     f = f refl
      node (deferˢ k s)                            f = proj₁ f refl

    held-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Over t
    held-from f = record
      { nodes = λ ψ s → node _ (reach f refl ψ s)
      ; pools = λ ψ s → proj₁ (proj₂ (reach f refl ψ s)) refl
      ; rests = λ ψ s → proj₁ (proj₂ (reach f refl ψ s)) refl }

    held-to : ∀ {Δ A} {t : Sub h Δ A} → Over t → Below t
    held-to {t = t} O = below t true (λ _ → O)

  -- `Each`, node by node.
  module Eaching {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) where
    open At H

    Part : ∀ {Δ A} → Sub h Δ A → Set₁
    Part u = ∀ {c} → part u ≡ just c → P c

    Pool : ∀ {Δ A} → Sub h Δ A → Set₁
    Pool (flatMapˢ op f fl oc k r pl so ls) = ∀ {c} → part (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
    Pool _                                   = Lift _ ⊤

    Rest : ∀ {Δ A} → Sub h Δ A → Set₁
    Rest (connectˢ S c b kb k fd rp e rt src bd) =
      ∀ {n} → part (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → part src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
    Rest _ = Lift _ ⊤

    open Held H Part Pool Rest using (Over; held-from; held-to) renaming (Below to Folded)

    record Below {Δ A} (t : Sub h Δ A) : Set₁ where
      constructor eaching
      field folded : Folded t

    each-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Each H P t
    each-from (eaching f) = record { parts = Over.nodes O ; pools = Over.pools O ; rests = Over.rests O }
      where O = held-from f

    each-to : ∀ {Δ A} {t : Sub h Δ A} → Each H P t → Below t
    each-to E = eaching (held-to (record { nodes = Each.parts E ; pools = Each.pools E ; rests = Each.rests E }))

  -- `Lingers`, node by node.
  module Lingering {h} (H : Heapᴹ h) where
    open At H

    Pool : ∀ {Δ A} → Sub h Δ A → Set₁
    Pool (flatMapˢ op f fl oc k r pl so ls) = ∀ {c} → part (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Tied pl (pooled fl so ls)
    Pool _                                   = Lift _ ⊤

    Rest : ∀ {Δ A} → Sub h Δ A → Set₁
    Rest (connectˢ S c b kb k fd rp e rt src bd) =
      ∀ {n} → part (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → part src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Tied rt (leftover {B = ⊤} src)
    Rest _ = Lift _ ⊤

    open Held H (λ _ → Lift _ ⊤) Pool Rest using (Over; held-from; held-to) renaming (Below to Folded)

    record Below {Δ A} (t : Sub h Δ A) : Set₁ where
      constructor lingering
      field folded : Folded t

    lingers-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Lingers H t
    lingers-from (lingering f) = record { pools = Over.pools O ; rests = Over.rests O }
      where O = held-from f

    lingers-to : ∀ {Δ A} {t : Sub h Δ A} → Lingers H t → Below t
    lingers-to L = lingering (held-to (record { nodes = λ _ _ → lift tt ; pools = Lingers.pools L ; rests = Lingers.rests L }))

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
  -- ghost holds heading no earlier than where the run is; what it keeps
  -- of ended parts, what they still run.
  record Carried (g : U.Node [] R) (m : Mach) : Set₁ where
    H = Conf.heap (Mach.conf m)
    field
      sane    : Sane []ᴬ g
      placed  : Placedᵍ g []ᴬ
      tree    : Sub (Conf.world (Mach.conf m)) [] R
      ctlAs   : Against.CtlAs tree (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m)) (Mach.bursts m)
      meets   : Meets ctlAs (At.part H tree) g
      owned′  : OwnedF H tree ctlAs
      kernels : Kernels H tree
      meaning : Meaning H tree
      queue   : Queue H (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) tree
      books   : Books tree ctlAs m
      sorted  : Σ Pos λ lo → WellMach lo m
      behind′ : Eaching.Below H (Heads (Conf.pos (Mach.conf m))) tree
      lingers′ : Lingering.Below H tree

    owned : Owned H tree ctlAs
    owned = owned-from {H = H} {t = tree} {ca = ctlAs} owned′

    behind : Each H (Heads (Conf.pos (Mach.conf m))) tree
    behind = Eaching.each-from H (Heads (Conf.pos (Mach.conf m))) behind′

    lingers : Lingers H tree
    lingers = Lingering.lingers-from H lingers′

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
    ; ctlAs   = Against.subAs here ([] , []ᴬ , same , refl , ≗-refl _) Against.bottomAs []ᴬ
    ; meets   = refl
    ; owned′   = Any.here refl ,ᴼ []ᴬ
    ; kernels = record { holds = _ ; gated = _ ; settled = _ }
    ; meaning = record { fed = _ }
    ; queue   = record { timed = []ᴬ , []ᴬ ; joined = []ᴬ , []ᴬ ; ordered = []ᴸ ; ahead = []ᴬ }
    ; books   = record { fresh = []ᴾ ; clocked = refl , tt ; paidUp = refl ; running = refl }
    ; sorted  = root , begin-well o
    ; behind′  = Eaching.eaching (λ { _ refl → heads-begin o })
    ; lingers′ = Lingering.lingering (λ _ → lift tt) }
