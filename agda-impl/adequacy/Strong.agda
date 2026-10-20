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

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Linked using (Linked) renaming ([] to []ᴸ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ)

import Tree as T
open import Tree using (Obs; Later)
open import denotation.MonotonicList.Events using (inside; Time; Pos; From; Frame; Timeline; at; emit; stall; close; ix; last; tick; root; _<ᵖ_) renaming (done to doneᶠ; quiet to quietᶠ; sub to subᴾ)
open import operation.AbstractObservable using (base; maybe; quiet; gate; module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; note; fin; module Pure)
open import operation.Machine using (module Machine)
import denotation.Unfold as U
open import adequacy.Placed.Order using () renaming (Placed to Placedᵍ)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)


module Strongly (R : Set) where
  open Heap using (World; Kind; cell; slot; hush; play; _⊑_; _∋_; Sink; Handle; Quiet; _⨾_; same)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Shared Timeline (Out R) using (Callbacks; Heapᴹ; look; Conf; Ctl; Stack; bottom; push; rest; back; rehold; run; asking; ⟨_,_,_⟩) renaming (held to holding)
  open Pure R using (Timer; cascade)
  open Machine R using (Mach; Playing; begin)
  open SortingWalk R using (WellMach; begin-well)

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

  -- The done flag of every flatMap a path enters through its outer.
  mutual
    outers : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → List (Name h)
    outers here                   = []
    outers (in-map p)             = outers p
    outers (in-scan p)            = outers p
    outers (in-take p)            = outers p
    outers (in-outer {fl = fl} p) = (cell _ , Flat.outerDone fl) ∷ outers p
    outers (in-lanes p)           = outersL p
    outers (in-source p)          = outers p
    outers (in-body p)            = outers p
    outers (in-defer p)           = outers p

    outersL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → List (Name h)
    outersL (this-lane p) = outers p
    outersL (next-lane p) = outersL p

  mutual
    outers-⊕ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (π : Path t u) (τ : Path u v)
             → outers (π ⊕ τ) ≡ outers π ++ outers τ
    outers-⊕ here          τ = refl
    outers-⊕ (in-map π)    τ = outers-⊕ π τ
    outers-⊕ (in-scan π)   τ = outers-⊕ π τ
    outers-⊕ (in-take π)   τ = outers-⊕ π τ
    outers-⊕ (in-outer π)  τ = cong (_ ∷_) (outers-⊕ π τ)
    outers-⊕ (in-lanes π)  τ = outersL-⊕ π τ
    outers-⊕ (in-source π) τ = outers-⊕ π τ
    outers-⊕ (in-body π)   τ = outers-⊕ π τ
    outers-⊕ (in-defer π)  τ = outers-⊕ π τ

    outersL-⊕ : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (π : PathLanes ls u) (τ : Path u v)
              → outersL (π ⊕ᴸ τ) ≡ outersL π ++ outers τ
    outersL-⊕ (this-lane π) τ = outers-⊕ π τ
    outersL-⊕ (next-lane π) τ = outersL-⊕ π τ

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

    -- What an open part leaves running: its leftover, less an ended
    -- outer's or lane's that its flatMap's pool has yet to take, which
    -- the climb carries free until the pool takes it.
    mutual
      kept : ∀ {Δ A B} → Sub h Δ A → U.Node Δ B
      kept (pendingˢ s q)                     = U.restᶜ (U.subscribe s q)
      kept (coldˢ s hd ph)                    = U.idleᶜ
      kept (ofˢ p i xs)                       = U.idleᶜ
      kept doneˢ                              = U.idleᶜ
      kept (mapˢ f s)                         = kept s
      kept (scanˢ f r s)                      = kept s
      kept (takeWhileˢ i p c k tk s)          = kept s
      kept (flatMapˢ op f fl oc k r pl so ls) =
        U.unionᶜ (if val (Flat.outerDone fl) then leftover so else if is-just (part so) then kept so else U.idleᶜ) (keptL ls)
      kept (connectˢ S c b kb k fd rp e rt src bd) =
        U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) (kept {B = ⊤} bd))
        where n = sourced (part src) (leftover src)
      kept (joinˢ j sk l x st)                = U.idleᶜ
      kept (deferˢ k s)                       = kept s

      keptL : ∀ {Δ A B} → List (Lane h Δ A) → U.Node Δ B
      keptL []                = U.idleᶜ
      keptL (lane c k s ∷ ls) = U.unionᶜ (if val (Kit.live c) then (if is-just (part s) then kept s else U.idleᶜ) else leftover s) (keptL ls)

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

    -- Where a connect's source ended, read only once its subject is
    -- closed: the end climbs to the connect before any joiner is told.
    told : ∀ {A} → Subject A h → Maybe Pos → Maybe Pos
    told S e = if val (Subject.closed S) then e else nothing

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
    Alg.connᶜ FedAlg = λ S _ _ _ _ fd _ e _ _ _ X Y ν → X ν × Y ((fd , told S e) ∷ᴬ ν)
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
