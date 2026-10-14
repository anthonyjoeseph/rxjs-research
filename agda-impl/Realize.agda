{-# OPTIONS --guardedness --large-indices #-}

-- REALIZING A CONFIGURATION: what the engine's state must hold for a
-- configuration tree (`Config`) to be what is running.
--
-- The engine keeps no tree.  Its heap holds cells, registered observers
-- and started colds; its queue holds timers.  So the relation is carried
-- by a witness, `Sub`: every subscription the run has made, open or not,
-- with the names its kernel allocated.  Which of them are still open is
-- read off the heap — a spent handle, a cut flag, a subject's `closed` —
-- and the open part is the configuration (`part`).
--
-- A registered observer is a callback, so it is related by what it does:
-- up to `_≼_` (`operation.Budget`) against the observer its kernel would
-- build now, from its parent's and its own cells (`Canon`).  A stored
-- callback that diverges where the canonical one does not only cuts the
-- run, which the bound half allows.
--
-- What is no longer reachable is dropped from the witness: a lane killed
-- by a switch is unsubscribed whole, so its timers are spent and its
-- joiners silenced, and only those two leave a trace the run still reads.
module Realize where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_) renaming (tail to tailᴸ)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (here; there)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Time; Pos; Burst; Timeline; last; _<ᵖ_; <ᵖ-trans; <ᵖ-ix; hush) renaming (sub to subᴾ)
open import operation.AbstractObservable using (base; sink; module Run)
open import operation.PureObservable using (Pureᴾ; World; Kind; cell; slot; play; _∋_; Sink; Handle; same; note; fin; module Pure)
open import operation.Budget using (module Approx)
open import Config using (Hots; module Nodes)

module Realizing (R : Set) (n : ℕ) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (State; Val; Timer; Callbacks; get; cascade; compileᴺ; mapList)
  open Approx R using (CbRel)
  open Nodes n renaming (live to running)

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

    -- What `attach` registers: the subscription's unsubscribe.
    attachCb : Act h ⊤ → Callbacks ⊤ h
    attachCb u = record { onNext = λ _ → u ; onComplete = skipᴬ ; isClosed = done false }

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
      open FlatMap op (λ a → compileᴺ n (f a) E) o fl public

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
  -- Every subscription made, with its names

  -- A lane: its kill switch, the unsubscribe `attach` registered, and
  -- the subscription.
  mutual
    data Sub (h : World) : List Set → Set → Set₁ where
      -- A started cold, with its next frame if one is pending: subscribed
      -- at tick τ, set at `e`, due at tick `t` of its timeline.
      coldˢ      : ∀ {Δ A} → Sink h A → Handle h → Maybe (Time × Pos × Time × Burst A) → Sub h Δ A
      -- A subscription with nothing left: `empty`, `of`, a join after the
      -- subject completed.
      doneˢ      : ∀ {Δ A} → Sub h Δ A
      mapˢ       : ∀ {Δ A B} → (A → B) → Sub h Δ A → Sub h Δ B
      scanˢ      : ∀ {Δ A B} → (B → A → B) → Ref h (base B) → Sub h Δ A → Sub h Δ B
      takeWhileˢ : ∀ {Δ A} → Bool → (A → Bool) → Cut h → Sink h ⊤ → Sub h Δ A → Sub h Δ A
      -- Its cells, the outer's kill switch and attached unsubscribe, the
      -- refill sink, the outer, and the lanes its `lanes` cell lists.
      flatMapˢ   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Sink h ⊤ → Sink h ⊤
                 → Sub h Δ A → List (Lane h Δ B) → Sub h Δ B
      -- The subject, where the source completed if it has, the source, the
      -- body.
      connectˢ   : ∀ {Δ A B} → Subject A h → Maybe Pos → Sub h Δ A → Sub h (A ∷ Δ) B → Sub h Δ B
      -- Joined at `j`: the registered sink and its flag.
      joinˢ      : ∀ {Δ A} → Pos → Sink h A → Ref h (base Bool) → A ∈ Δ → Sub h Δ A

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
  unsub (connectˢ S e src body)          = unsub src >>ᴬ unsub body
  unsub (joinˢ j sk l i)                 = writeRef l false skipᴬ

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
    names (connectˢ S e src body)         = subjectNames S ++ names src ++ names body
    names (joinˢ j sk l i)                = (slot _ , sk) ∷ (cell _ , l) ∷ []

    laneNames : ∀ {h Δ B} → List (Lane h Δ B) → List (Name h)
    laneNames []                  = []
    laneNames (lane c k s ∷ ls)   = cutNames c ++ (slot _ , k) ∷ names s ++ laneNames ls

  -- The frames pending, as the timers that should be queued for them.
  mutual
    pendings : ∀ {h Δ A} → Sub h Δ A → List (Timer h)
    pendings (coldˢ s hd nothing)                = []
    pendings (coldˢ s hd (just (τ , e , t , b))) = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
    pendings doneˢ                               = []
    pendings (mapˢ f s)                          = pendings s
    pendings (scanˢ f r s)                       = pendings s
    pendings (takeWhileˢ i p c k s)              = pendings s
    pendings (flatMapˢ op f fl oc k r so ls)     = pendings so ++ lanePendings ls
    pendings (connectˢ S e src body)             = pendings src ++ pendings body
    pendings (joinˢ j sk l i)                    = []

    lanePendings : ∀ {h Δ B} → List (Lane h Δ B) → List (Timer h)
    lanePendings []                = []
    lanePendings (lane c k s ∷ ls) = pendings s ++ lanePendings ls

  -- A subject the tree holds, and a joiner of one.
  record Joiner (h : World) : Set₁ where
    constructor joiner
    field
      {A}     : Set
      subject : Subject A h
      sink′   : Sink h A
      at      : Pos

  mutual
    subjects : ∀ {h Δ A} → Sub h Δ A → List (Σ Set λ A → Subject A h)
    subjects (coldˢ s hd _)                  = []
    subjects doneˢ                           = []
    subjects (mapˢ f s)                      = subjects s
    subjects (scanˢ f r s)                   = subjects s
    subjects (takeWhileˢ i p c k s)          = subjects s
    subjects (flatMapˢ op f fl oc k r so ls) = subjects so ++ laneSubjects ls
    subjects (connectˢ S e src body)         = (_ , S) ∷ subjects src ++ subjects body
    subjects (joinˢ j sk l i)                = []

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
    joiners (connectˢ S e src body)         E = joiners src E ++ joiners body (S ∷ E)
    joiners (joinˢ j sk l i)                E = joiner (lookup E i) sk j ∷ []

    laneJoiners : ∀ {h Δ B} → List (Lane h Δ B) → Env Δ h → List (Joiner h)
    laneJoiners []                E = []
    laneJoiners (lane c k s ∷ ls) E = joiners s E ++ laneJoiners ls E

  ------------------------------------------------------------------------
  -- Against a state

  module At {h : World} (H : All (Val h) h) where
    val : ∀ {t} → Ref h t → El h t
    val r = lower (get H r)

    spentʰ : Handle h → Bool
    spentʰ hd = lower (get H hd)

    -- A registered observer, up to `_≼_` against `c`.
    slotIs : ∀ {A} → Sink h A → Callbacks A h → Set₁
    slotIs s c = CbRel (get H s) c

    -- An unsubscribe attached to a kill switch.
    heldIs : Cut h → Sink h ⊤ → Act h ⊤ → Set₁
    heldIs c k u = val (Kit.held c) ≡ just k × slotIs k (attachCb u)

    pending : ∀ {Δ A} → Maybe (Time × Pos × Time × Burst A) → Node Δ A
    pending nothing                = quietᶜ
    pending (just (τ , e , t , b)) = coldᶜ τ e t b

    mapᴹ : ∀ {X Y : Set₁} → (X → Y) → Maybe X → Maybe Y
    mapᴹ f nothing  = nothing
    mapᴹ f (just x) = just (f x)

    consᴹ : ∀ {X : Set₁} → Maybe X → List X → List X
    consᴹ nothing  xs = xs
    consᴹ (just x) xs = x ∷ xs

    -- A flatMap is open while its outer, a lane or the queue is.
    merged : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Maybe (Node Δ A) → List (Node Δ B) → List A → Maybe (Node Δ B)
    merged op f nothing []       []       = nothing
    merged op f o       ls       qs       = just (flatMapᶜ op f o ls qs)

    -- A connect is open while its body is; its source, once complete, is
    -- complete where it completed.
    connected : ∀ {Δ A B} → Maybe (Node Δ A) → Maybe Pos → Maybe (Node (A ∷ Δ) B) → Maybe (Node Δ B)
    connected s        e        nothing  = nothing
    connected (just s) e        (just b) = just (connectᶜ (running s) b)
    connected nothing  (just p) (just b) = just (connectᶜ (finished p) b)
    connected nothing  nothing  (just b) = nothing

    isNothing : ∀ {X : Set₁} → Maybe X → Bool
    isNothing nothing  = true
    isNothing (just _) = false

    -- The lanes still open.
    count : ∀ {Δ B} → List (Lane h Δ B) → ℕ
    count []                = 0
    count (lane c _ _ ∷ ls) = if val (Kit.live c) then suc (count ls) else count ls

    switches : ∀ {Δ B} → List (Lane h Δ B) → List (Cut h)
    switches []                = []
    switches (lane c _ _ ∷ ls) = c ∷ switches ls

    ----------------------------------------------------------------------
    -- What is still open: the configuration

    mutual
      part : ∀ {Δ A} → Sub h Δ A → Env Δ h → Maybe (Node Δ A)
      part (coldˢ s hd p)                  E = if spentʰ hd then nothing else just (pending p)
      part doneˢ                           E = nothing
      part (mapˢ f s)                      E = mapᴹ (mapᶜ f) (part s E)
      part (scanˢ f r s)                   E = mapᴹ (scanᶜ f (val r)) (part s E)
      part (takeWhileˢ i p c k s)          E = if val (Kit.live c) then mapᴹ (takeWhileᶜ i p) (part s E) else nothing
      part (flatMapˢ op f fl oc k r so ls) E = merged op f (part so E) (partLanes ls E) (val (Flat.queue fl))
      part (connectˢ S e src body)         E = connected (part src E) e (part body (S ∷ E))
      part (joinˢ j sk l i)                E = if val l ∧ not (val (Subject.closed (lookup E i))) then just (joinᶜ j 0 i) else nothing

      partLanes : ∀ {Δ B} → List (Lane h Δ B) → Env Δ h → List (Node Δ B)
      partLanes []                E = []
      partLanes (lane c k s ∷ ls) E = if val (Kit.live c) then consᴹ (part s E) (partLanes ls E) else partLanes ls E

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
        × val (Flat.outerDone fl) ≡ isNothing (part so E)
        × val (Flat.active fl) ≡ count ls
        × val (Flat.lanes fl) ≡ switches ls
        × HoldsLanes op f E o fl ls
      Holds (connectˢ S e src body)         E o =
        Holds src E (feeder S) × Holds body (S ∷ E) o × val (Subject.closed S) ≡ isNothing (part src E)
        × (isNothing (part src E) ≡ true → Σ Pos λ p → e ≡ just p)
      Holds (joinˢ j sk l i)                E o = slotIs sk (joinerCb l o)

      HoldsLanes : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Env Δ h → Observer B h → Flat A h → List (Lane h Δ B) → Set₁
      HoldsLanes op f E o fl []                = Lift _ ⊤
      HoldsLanes op f E o fl (lane c k s ∷ ls) = heldIs c k (unsub s) × Holds s E (Flat′.laneO op f E o fl c)
                                               × (val (Kit.live c) ≡ true → isNothing (part s E) ≡ false) × HoldsLanes op f E o fl ls

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
  -- subscription made, against its kernel, whose open part is `c`; the
  -- queue its pending frames, the subjects' subscribers its joiners, the
  -- names all distinct.
  --
  -- DEAD ROUTE: a relation per operator (a `Below s d`, against any
  --   observer that keeps an abstract interface) cannot be carried.
  --   Siblings that share one observer — a merge's lanes, a subject's
  --   joiners — each hold a remainder only the shared state records, and
  --   an abstract step returns its sibling's as an existential witness,
  --   forgotten; and a merge's order needs every sibling's pending
  --   positions, which an abstract subscription does not expose.
  record Realizes {h} (c : Node [] R) (st : State h) : Set₁ where
    open At (State.heap st)
    field
      tree    : Sub h [] R
      holds   : Holds tree [] rootObs
      open≡   : part tree [] ≡ just c
      timed   : Timed (State.timers st) (pendings tree)
      joined  : Joined (subjects tree) (joiners tree [])
      ordered : Ordered st
      fresh   : AllPairs _≢_ (names tree)

  ------------------------------------------------------------------------
  -- With no timer left, nothing is pending

  absurd : ∀ {a} {X : Set a} → true ≡ false → X
  absurd ()

  module Dryness {h : World} (st : State h) where
    open At (State.heap st)

    Spent : List (Timer h) → Set₁
    Spent = All (λ tm → spentʰ (Timer.handle tm) ≡ true)

    -- A subject not yet complete is silent in the meaning's environment.
    Hushed : ∀ {Δ} → Env Δ h → Hots Δ → Set₁
    Hushed {Δ} E ρ = ∀ {A} (i : A ∈ Δ) → val (Subject.closed (lookup E i)) ≡ false → lookup ρ i ≡ hush

    hushed-∷ : ∀ {Δ A} {S : Subject A h} {E : Env Δ h} {e ρ} → (val (Subject.closed S) ≡ false → e ≡ hush) → Hushed E ρ
             → Hushed (S ∷ E) (e ∷ ρ)
    hushed-∷ p q (here refl) c = p c
    hushed-∷ p q (there i)   c = q i c

    merged-just : ∀ {Δ A B} op (f : A → Obs Timeline Δ B) mo ls qs {c} → merged op f mo ls qs ≡ just c → flatMapᶜ op f mo ls qs ≡ c
    merged-just op f nothing  []       []       ()
    merged-just op f nothing  []       (_ ∷ _)  refl = refl
    merged-just op f nothing  (_ ∷ _)  qs       refl = refl
    merged-just op f (just _) ls       qs       refl = refl

    mutual
      dry-part : ∀ {Δ A} (t : Sub h Δ A) {E : Env Δ h} {o ρ c} → Holds t E o → Hushed E ρ → Spent (pendings t)
               → part t E ≡ just c → Dry c ρ
      dry-part (coldˢ s hd p) _ _ sp eq with spentʰ hd in w
      dry-part (coldˢ s hd p)        _ _ sp        () | true
      dry-part (coldˢ s hd nothing)  _ _ sp        refl | false = tt
      dry-part (coldˢ s hd (just x)) _ _ (x′ ∷ []) refl | false = absurd (trans (sym x′) w)
      dry-part doneˢ _ _ _ ()
      dry-part (mapˢ f s) {E} q u sp eq with part s E in e
      dry-part (mapˢ f s) {E} q u sp refl | just c′ = dry-part s q u sp e
      dry-part (scanˢ f r s) {E} q u sp eq with part s E in e
      dry-part (scanˢ f r s) {E} q u sp refl | just c′ = dry-part s q u sp e
      dry-part (takeWhileˢ i p c k s) {E} (_ , q) u sp eq with val (Kit.live c) | part s E in e
      dry-part (takeWhileˢ i p c k s) {E} (_ , q) u sp refl | true | just c′ = dry-part s q u sp e
      dry-part (flatMapˢ op f fl oc k r so ls) {E} {o} {ρ = ρ} (_ , _ , _ , q , _ , _ , _ , ql) u sp eq
        rewrite sym (merged-just op f (part so E) (partLanes ls E) (val (Flat.queue fl)) eq) =
        dry-outer so q u (++⁻ˡ (pendings so) sp) , dry-lanes ls {op} {f} {E} {o} {fl} ql u (++⁻ʳ (pendings so) sp)
      dry-part (connectˢ S e src body) {E} (q , qb , cl , _) u sp eq with part src E in es | part body (S ∷ E) in eb
      dry-part (connectˢ S e src body) {E} {ρ = ρ} (q , qb , cl , _) u sp refl | just s′ | just b′ =
        dry-part src q u (++⁻ˡ (pendings src) sp) es
        , dry-part body qb (hushed-∷ (λ _ → dry-hush s′ ρ (dry-part src q u (++⁻ˡ (pendings src) sp) es)) u) (++⁻ʳ (pendings src) sp) eb
      dry-part (connectˢ S (just p) src body) {E} (q , qb , cl , _) u sp refl | nothing | just b′ =
        tt , dry-part body qb (hushed-∷ (λ c → absurd (trans (sym cl) c)) u) (++⁻ʳ (pendings src) sp) eb
      dry-part (joinˢ j sk l i) {E} q u sp eq with val l | val (Subject.closed (lookup E i)) in ec
      dry-part (joinˢ j sk l i) {E} q u sp refl | true | false = u i ec

      dry-outer : ∀ {Δ A} (t : Sub h Δ A) {E : Env Δ h} {o ρ} → Holds t E o → Hushed E ρ → Spent (pendings t) → Dryᵒ (part t E) ρ
      dry-outer t {E} q u sp with part t E in e
      ... | nothing = tt
      ... | just c  = dry-part t q u sp e

      dry-lanes : ∀ {Δ A B} (ls : List (Lane h Δ B)) {op} {f : A → Obs Timeline Δ B} {E : Env Δ h} {o fl ρ}
                → HoldsLanes op f E o fl ls → Hushed E ρ → Spent (lanePendings ls) → Dryˡ (partLanes ls E) ρ
      dry-lanes [] _ _ _ = tt
      dry-lanes (lane c k s ∷ ls) {op} {f} {E} {o} {fl} (_ , q , _ , ql) u sp with val (Kit.live c) | part s E in e
      ... | true  | just c′ = dry-part s q u (++⁻ˡ (pendings s) sp) e , dry-lanes ls {op} {f} {E} {o} {fl} ql u (++⁻ʳ (pendings s) sp)
      ... | true  | nothing = dry-lanes ls {op} {f} {E} {o} {fl} ql u (++⁻ʳ (pendings s) sp)
      ... | false | _       = dry-lanes ls {op} {f} {E} {o} {fl} ql u (++⁻ʳ (pendings s) sp)

    ∉[] : ∀ {X : Set₁} {x : X} {Y : Set₁} → x ∈ [] → Y
    ∉[] ()

    -- A spent cold's frame, or none.
    spent-all : ∀ (ps : List (Timer h)) → All (λ tm → spentʰ (Timer.handle tm) ≡ false → tm ∈ State.timers st) ps
              → State.timers st ≡ [] → Spent ps
    spent-all []       []       e = []
    spent-all (p ∷ ps) (q ∷ qs) e with spentʰ (Timer.handle p) in s
    ... | true  = s ∷ spent-all ps qs e
    ... | false = ∉[] (subst (p ∈_) e (q refl))

  -- WITH NO TIMER LEFT, the configuration has nothing pending.
  realizes-dry : ∀ {h} {c : Node [] R} {st : State h} → Realizes c st → State.timers st ≡ [] → Dry c []
  realizes-dry {st = st} z e = dry-part (Realizes.tree z) (Realizes.holds z) (λ ()) (spent-all (pendings (Realizes.tree z)) (proj₂ (Realizes.timed z)) e) (Realizes.open≡ z)
    where open Dryness st

  ------------------------------------------------------------------------
  -- A spent timer's turn

  -- Every timer queued behind the first sits past it.
  linked-after : ∀ {h} {x : Timer h} {xs} → Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (x ∷ xs)
               → All (λ u → cascade x <ᵖ cascade u ≡ true) xs
  linked-after [-]     = []
  linked-after {x = x} (r ∷ l) =
    Linked⇒All {R = λ t u → cascade t <ᵖ cascade u ≡ true} (λ {i} {j} {k} → <ᵖ-trans (cascade i) (cascade j) (cascade k)) {v = x} r l

  -- A SPENT TIMER'S TURN moves nothing the configuration holds: the clock
  -- reaches its due tick, and the queue behind it is still in order.
  realizes-spent : ∀ {h} {c : Node [] R} {st : State h} {tm ts} → Realizes c st → State.timers st ≡ tm ∷ ts
                 → lower (get (State.heap st) (Timer.handle tm)) ≡ true
                 → Realizes c (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  realizes-spent {h} {st = st} {tm} {ts} z eq s = record
    { tree    = tree
    ; holds   = holds
    ; open≡   = open≡
    ; timed   = drop (subst (All Live) eq (proj₁ timed)) , mapᴬ keep (proj₂ timed)
    ; joined  = joined
    ; ordered = tailᴸ L , mapᴬ (λ {u} r → <ᵖ-ix (Timer.due tm) (Timer.due u) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from u) ∷ []) r , r) (linked-after L)
    ; fresh   = fresh
    }
    where
      open Realizes z
      open At (State.heap st)
      Live : Timer h → Set₁
      Live tm′ = spentʰ (Timer.handle tm′) ≡ true ⊎ tm′ ∈ pendings tree
      drop : All Live (tm ∷ ts) → All Live ts
      drop (_ ∷ a) = a
      keep : ∀ {p} → (spentʰ (Timer.handle p) ≡ false → p ∈ State.timers st) → spentʰ (Timer.handle p) ≡ false → p ∈ ts
      keep {p} f sp with subst (p ∈_) eq (f sp)
      ... | here refl = absurd (trans (sym s) sp)
      ... | there i   = i
      L : Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (tm ∷ ts)
      L = subst (Linked _) eq (proj₁ ordered)
