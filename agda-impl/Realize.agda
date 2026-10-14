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
open import Data.List using (List; []; _∷_; _++_; [_]) renaming (map to mapˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; tabulate) renaming (map to mapᴬ; tail to tailᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_) renaming (tail to tailᴸ)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.AllPairs.Properties using (map⁻)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Time; Pos; Burst; Timeline; last; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-ix; <ᵖ-irrefl; hush) renaming (sub to subᴾ)
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

  -- Where a started cold stands: nothing pending; its next frame, set at
  -- `e`, due at tick `t` of a timeline subscribed at tick `τ`; or inside
  -- that frame, at step `i` of the frame at `r` — only while a turn plays
  -- it.
  data Phase (A : Set) : Set where
    idle   : Phase A
    frame  : Time → Pos → Time → Burst A → Phase A
    firing : Time → Pos → ℕ → Burst A → Phase A

  -- A lane: its kill switch, the unsubscribe `attach` registered, and
  -- the subscription.
  mutual
    data Sub (h : World) : List Set → Set → Set₁ where
      -- A started cold, where it stands.
      coldˢ      : ∀ {Δ A} → Sink h A → Handle h → Phase A → Sub h Δ A
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
    pendings (coldˢ s hd idle)                   = []
    pendings (coldˢ s hd (frame τ e t b))        = record { due = τ + t ; sink = s ; handle = hd ; at′ = t ; from = e ; frame = b } ∷ []
    pendings (coldˢ s hd (firing τ r i b))       = []
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

  -- No cold inside a frame: the tree between turns.
  mutual
    Calm : ∀ {h Δ A} → Sub h Δ A → Set
    Calm (coldˢ s hd idle)                = ⊤
    Calm (coldˢ s hd (frame _ _ _ _))     = ⊤
    Calm (coldˢ s hd (firing _ _ _ _))    = ⊥
    Calm doneˢ                            = ⊤
    Calm (mapˢ f s)                       = Calm s
    Calm (scanˢ f r s)                    = Calm s
    Calm (takeWhileˢ i p c k s)           = Calm s
    Calm (flatMapˢ op f fl oc k r so ls)  = Calm so × CalmLanes ls
    Calm (connectˢ S e src body)          = Calm src × Calm body
    Calm (joinˢ j sk l i)                 = ⊤

    CalmLanes : ∀ {h Δ B} → List (Lane h Δ B) → Set
    CalmLanes []                = ⊤
    CalmLanes (lane c k s ∷ ls) = Calm s × CalmLanes ls

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

    pending : ∀ {Δ A} → Phase A → Node Δ A
    pending idle             = quietᶜ
    pending (frame τ e t b)  = coldᶜ τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 b
    pending (firing τ r i b) = coldᶜ τ r i b

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
  record Holding {h} (c : Node [] R) (st : State h) : Set₁ where
    open At (State.heap st)
    field
      tree    : Sub h [] R
      holds   : Holds tree [] rootObs
      open≡   : part tree [] ≡ just c
      timed   : Timed (State.timers st) (pendings tree)
      joined  : Joined (subjects tree) (joiners tree [])
      ordered : Ordered st
      fresh   : AllPairs _≢_ (names tree)

  -- Between turns, with no cold inside a frame.
  record Realizes {h} (c : Node [] R) (st : State h) : Set₁ where
    field
      holding : Holding c st
      calm    : Calm (Holding.tree holding)

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
      dry-part : ∀ {Δ A} (t : Sub h Δ A) {E : Env Δ h} {o ρ c} → Holds t E o → Calm t → Hushed E ρ → Spent (pendings t)
               → part t E ≡ just c → Dry c ρ
      dry-part (coldˢ s hd p) _ _ _ sp eq with spentʰ hd in w
      dry-part (coldˢ s hd p)               _ _  _ sp        () | true
      dry-part (coldˢ s hd idle)            _ _  _ sp        refl | false = tt
      dry-part (coldˢ s hd (frame _ _ _ _)) _ _  _ (x′ ∷ []) refl | false = absurd (trans (sym x′) w)
      dry-part (coldˢ s hd (firing _ _ _ _)) _ () _ sp       refl | false
      dry-part doneˢ _ _ _ _ ()
      dry-part (mapˢ f s) {E} q m u sp eq with part s E in e
      dry-part (mapˢ f s) {E} q m u sp refl | just c′ = dry-part s q m u sp e
      dry-part (scanˢ f r s) {E} q m u sp eq with part s E in e
      dry-part (scanˢ f r s) {E} q m u sp refl | just c′ = dry-part s q m u sp e
      dry-part (takeWhileˢ i p c k s) {E} (_ , q) m u sp eq with val (Kit.live c) | part s E in e
      dry-part (takeWhileˢ i p c k s) {E} (_ , q) m u sp refl | true | just c′ = dry-part s q m u sp e
      dry-part (flatMapˢ op f fl oc k r so ls) {E} {o} {ρ = ρ} (_ , _ , _ , q , _ , _ , _ , ql) (m , ml) u sp eq
        rewrite sym (merged-just op f (part so E) (partLanes ls E) (val (Flat.queue fl)) eq) =
        dry-outer so q m u (++⁻ˡ (pendings so) sp) , dry-lanes ls {op} {f} {E} {o} {fl} ql ml u (++⁻ʳ (pendings so) sp)
      dry-part (connectˢ S e src body) {E} (q , qb , cl , _) m u sp eq with part src E in es | part body (S ∷ E) in eb
      dry-part (connectˢ S e src body) {E} {ρ = ρ} (q , qb , cl , _) (m , mb) u sp refl | just s′ | just b′ =
        dry-part src q m u (++⁻ˡ (pendings src) sp) es
        , dry-part body qb mb (hushed-∷ (λ _ → dry-hush s′ ρ (dry-part src q m u (++⁻ˡ (pendings src) sp) es)) u) (++⁻ʳ (pendings src) sp) eb
      dry-part (connectˢ S (just p) src body) {E} (q , qb , cl , _) (m , mb) u sp refl | nothing | just b′ =
        tt , dry-part body qb mb (hushed-∷ (λ c → absurd (trans (sym cl) c)) u) (++⁻ʳ (pendings src) sp) eb
      dry-part (joinˢ j sk l i) {E} q m u sp eq with val l | val (Subject.closed (lookup E i)) in ec
      dry-part (joinˢ j sk l i) {E} q m u sp refl | true | false = u i ec

      dry-outer : ∀ {Δ A} (t : Sub h Δ A) {E : Env Δ h} {o ρ} → Holds t E o → Calm t → Hushed E ρ → Spent (pendings t) → Dryᵒ (part t E) ρ
      dry-outer t {E} q m u sp with part t E in e
      ... | nothing = tt
      ... | just c  = dry-part t q m u sp e

      dry-lanes : ∀ {Δ A B} (ls : List (Lane h Δ B)) {op} {f : A → Obs Timeline Δ B} {E : Env Δ h} {o fl ρ}
                → HoldsLanes op f E o fl ls → CalmLanes ls → Hushed E ρ → Spent (lanePendings ls) → Dryˡ (partLanes ls E) ρ
      dry-lanes [] _ _ _ _ = tt
      dry-lanes (lane c k s ∷ ls) {op} {f} {E} {o} {fl} (_ , q , _ , ql) (m , ml) u sp with val (Kit.live c) | part s E in e
      ... | true  | just c′ = dry-part s q m u (++⁻ˡ (pendings s) sp) e , dry-lanes ls {op} {f} {E} {o} {fl} ql ml u (++⁻ʳ (pendings s) sp)
      ... | true  | nothing = dry-lanes ls {op} {f} {E} {o} {fl} ql ml u (++⁻ʳ (pendings s) sp)
      ... | false | _       = dry-lanes ls {op} {f} {E} {o} {fl} ql ml u (++⁻ʳ (pendings s) sp)

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
  realizes-dry {st = st} z e = dry-part tree holds calm (λ ()) (spent-all (pendings tree) (proj₂ timed) e) open≡
    where open Dryness st
          open Realizes z
          open Holding holding

  ------------------------------------------------------------------------
  -- A spent timer's turn

  -- Every timer queued behind the first sits past it.
  linked-after : ∀ {h} {x : Timer h} {xs} → Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (x ∷ xs)
               → All (λ u → cascade x <ᵖ cascade u ≡ true) xs
  linked-after [-]     = []
  linked-after {x = x} (r ∷ l) =
    Linked⇒All {R = λ t u → cascade t <ᵖ cascade u ≡ true} (λ {i} {j} {k} → <ᵖ-trans (cascade i) (cascade j) (cascade k)) {v = x} r l

  -- Popping the queue's first timer, the clock at its due tick.
  ordered-pop : ∀ {h} {st : State h} {tm ts} → Ordered st → State.timers st ≡ tm ∷ ts
              → Ordered (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  ordered-pop {tm = tm} {ts} (l , _) eq =
    tailᴸ L , mapᴬ (λ {u} r → <ᵖ-ix (Timer.due tm) (Timer.due u) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from u) ∷ []) r , r) (linked-after L)
    where
      L : Linked (λ t u → cascade t <ᵖ cascade u ≡ true) (tm ∷ ts)
      L = subst (Linked _) eq l

  -- A SPENT TIMER'S TURN moves nothing the configuration holds: the clock
  -- reaches its due tick, and the queue behind it is still in order.
  realizes-spent : ∀ {h} {c : Node [] R} {st : State h} {tm ts} → Realizes c st → State.timers st ≡ tm ∷ ts
                 → lower (get (State.heap st) (Timer.handle tm)) ≡ true
                 → Realizes c (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  realizes-spent {h} {st = st} {tm} {ts} z eq s = record { holding = record
    { tree    = tree
    ; holds   = holds
    ; open≡   = open≡
    ; timed   = drop (subst (All Live) eq (proj₁ timed)) , mapᴬ keep (proj₂ timed)
    ; joined  = joined
    ; ordered = ordered-pop {st = st} ordered eq
    ; fresh   = fresh
    } ; calm = calm }
    where
      open Realizes z
      open Holding holding
      open At (State.heap st)
      Live : Timer h → Set₁
      Live tm′ = spentʰ (Timer.handle tm′) ≡ true ⊎ tm′ ∈ pendings tree
      drop : All Live (tm ∷ ts) → All Live ts
      drop (_ ∷ a) = a
      keep : ∀ {p} → (spentʰ (Timer.handle p) ≡ false → p ∈ State.timers st) → spentʰ (Timer.handle p) ≡ false → p ∈ ts
      keep {p} f sp with subst (p ∈_) eq (f sp)
      ... | here refl = absurd (trans (sym s) sp)
      ... | there i   = i

  ------------------------------------------------------------------------
  -- A frame starting

  -- One list inside another, in order.
  data _≲_ {X : Set₁} : List X → List X → Set₁ where
    nil  : [] ≲ []
    keep : ∀ {x xs ys} → xs ≲ ys → (x ∷ xs) ≲ (x ∷ ys)
    drop : ∀ {y xs ys} → xs ≲ ys → xs ≲ (y ∷ ys)

  ≲-[] : ∀ {X : Set₁} (ys : List X) → [] ≲ ys
  ≲-[] []       = nil
  ≲-[] (y ∷ ys) = drop (≲-[] ys)

  ≲-++ : ∀ {X : Set₁} {a b c d : List X} → a ≲ b → c ≲ d → (a ++ c) ≲ (b ++ d)
  ≲-++ nil      q = q
  ≲-++ (keep p) q = keep (≲-++ p q)
  ≲-++ (drop p) q = drop (≲-++ p q)

  ≲-ˡ : ∀ {X : Set₁} {a b : List X} (zs : List X) → a ≲ b → a ≲ (zs ++ b)
  ≲-ˡ []       p = p
  ≲-ˡ (z ∷ zs) p = drop (≲-ˡ zs p)

  all-≲ : ∀ {X : Set₁} {P : X → Set₁} {a b : List X} → a ≲ b → All P b → All P a
  all-≲ nil      []       = []
  all-≲ (keep p) (x ∷ xs) = x ∷ all-≲ p xs
  all-≲ (drop p) (x ∷ xs) = all-≲ p xs

  pairs-≲ : ∀ {X : Set₁} {Q : X → X → Set₁} {a b : List X} → a ≲ b → AllPairs Q b → AllPairs Q a
  pairs-≲ nil      []       = []
  pairs-≲ (keep p) (x ∷ xs) = all-≲ p x ∷ pairs-≲ p xs
  pairs-≲ (drop p) (x ∷ xs) = pairs-≲ p xs

  -- The name a timer's cold allocated for its handle.
  hname : ∀ {h} → Timer h → Name h
  hname tm = play , Timer.handle tm

  -- Every pending frame's handle is among the names.
  mutual
    pend-names : ∀ {h Δ A} (t : Sub h Δ A) → mapˡ hname (pendings t) ≲ names t
    pend-names (coldˢ s hd idle)               = ≲-[] _
    pend-names (coldˢ s hd (frame _ _ _ _))    = drop (keep nil)
    pend-names (coldˢ s hd (firing _ _ _ _))   = ≲-[] _
    pend-names doneˢ                           = nil
    pend-names (mapˢ f s)                      = pend-names s
    pend-names (scanˢ f r s)                   = drop (pend-names s)
    pend-names (takeWhileˢ i p c k s)          = ≲-ˡ (cutNames c) (drop (pend-names s))
    pend-names (flatMapˢ op f fl oc k r so ls) rewrite map-++ hname (pendings so) (lanePendings ls) =
      ≲-ˡ (flatNames fl) (≲-ˡ (cutNames oc) (drop (drop (≲-++ (pend-names so) (pend-lanes ls)))))
    pend-names (connectˢ S e src body) rewrite map-++ hname (pendings src) (pendings body) =
      ≲-ˡ (subjectNames S) (≲-++ (pend-names src) (pend-names body))
    pend-names (joinˢ j sk l i)                = ≲-[] _

    pend-lanes : ∀ {h Δ B} (ls : List (Lane h Δ B)) → mapˡ hname (lanePendings ls) ≲ laneNames ls
    pend-lanes []                = nil
    pend-lanes (lane c k s ∷ ls) rewrite map-++ hname (pendings s) (lanePendings ls) =
      ≲-ˡ (cutNames c) (drop (≲-++ (pend-names s) (pend-lanes ls)))

  -- Pending frames are of distinct colds.
  pend-distinct : ∀ {h Δ A} (t : Sub h Δ A) → AllPairs _≢_ (names t) → AllPairs (λ x y → hname x ≢ hname y) (pendings t)
  pend-distinct t f = map⁻ (pairs-≲ (pend-names t) f)

  -- A frame pending twice is not.
  once : ∀ {h} {tm : Timer h} xs {ys} → AllPairs (λ x y → hname x ≢ hname y) (xs ++ tm ∷ ys) → tm ∈ xs ++ ys → ⊥
  once []       (a ∷ _)  m         = lookup a m refl
  once (x ∷ xs) (a ∷ ap) (here eq) = lookup a (∈-++⁺ʳ xs (here (sym eq))) refl
  once (x ∷ xs) (a ∷ ap) (there m) = once xs ap m

  -- THE FRAME OF THE TIMER AT `p` STARTS: its cold is inside it, at step
  -- zero of the frame at the timer's cascade.
  mutual
    fire : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) → tm ∈ pendings t → Sub h Δ A
    fire (coldˢ s hd (frame τ e t b))     (here _)  = coldˢ s hd (firing τ (ix (τ + t) ∷ subᴾ e ∷ []) 0 b)
    fire (mapˢ f s)                       p = mapˢ f (fire s p)
    fire (scanˢ f r s)                    p = scanˢ f r (fire s p)
    fire (takeWhileˢ i q c k s)           p = takeWhileˢ i q c k (fire s p)
    fire (flatMapˢ op f fl oc k r so ls)  p with ∈-++⁻ (pendings so) p
    ... | inj₁ q = flatMapˢ op f fl oc k r (fire so q) ls
    ... | inj₂ q = flatMapˢ op f fl oc k r so (fireLanes ls q)
    fire (connectˢ S e src body)          p with ∈-++⁻ (pendings src) p
    ... | inj₁ q = connectˢ S e (fire src q) body
    ... | inj₂ q = connectˢ S e src (fire body q)

    fireLanes : ∀ {h Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) → tm ∈ lanePendings ls → List (Lane h Δ B)
    fireLanes (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
    ... | inj₁ q = lane c k (fire s q) ∷ ls
    ... | inj₂ q = lane c k s ∷ fireLanes ls q

  -- Starting it takes its frame, and only its, off the pending.
  record Split {h} (tm : Timer h) (ps qs : List (Timer h)) : Set₁ where
    constructor split
    field
      pre post : List (Timer h)
      was      : ps ≡ pre ++ tm ∷ post
      now      : qs ≡ pre ++ post

  split-ˡ : ∀ {h} {tm : Timer h} {ps qs} zs → Split tm ps qs → Split tm (ps ++ zs) (qs ++ zs)
  split-ˡ {tm = tm} zs (split a b w n) = split a (b ++ zs) (trans (cong (_++ zs) w) (++-assoc a (tm ∷ b) zs)) (trans (cong (_++ zs) n) (++-assoc a b zs))

  split-ʳ : ∀ {h} {tm : Timer h} {ps qs} zs → Split tm ps qs → Split tm (zs ++ ps) (zs ++ qs)
  split-ʳ {tm = tm} zs (split a b w n) = split (zs ++ a) b (trans (cong (zs ++_) w) (sym (++-assoc zs a (tm ∷ b)))) (trans (cong (zs ++_) n) (sym (++-assoc zs a b)))

  mutual
    fire-split : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) → Split tm (pendings t) (pendings (fire t p))
    fire-split (coldˢ s hd (frame τ e t b))     (here eq) = split [] [] (cong (_∷ []) (sym eq)) refl
    fire-split (mapˢ f s)                       p = fire-split s p
    fire-split (scanˢ f r s)                    p = fire-split s p
    fire-split (takeWhileˢ i q c k s)           p = fire-split s p
    fire-split (flatMapˢ op f fl oc k r so ls)  p with ∈-++⁻ (pendings so) p
    ... | inj₁ q = split-ˡ (lanePendings ls) (fire-split so q)
    ... | inj₂ q = split-ʳ (pendings so) (fire-lanes-split ls q)
    fire-split (connectˢ S e src body)          p with ∈-++⁻ (pendings src) p
    ... | inj₁ q = split-ˡ (pendings body) (fire-split src q)
    ... | inj₂ q = split-ʳ (pendings src) (fire-split body q)

    fire-lanes-split : ∀ {h Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls)
                     → Split tm (lanePendings ls) (lanePendings (fireLanes ls p))
    fire-lanes-split (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
    ... | inj₁ q = split-ˡ (lanePendings ls) (fire-split s q)
    ... | inj₂ q = split-ʳ (pendings s) (fire-lanes-split ls q)

  -- Starting it moves no name, no subject and no joiner, and nothing an
  -- unsubscribe does.
  mutual
    fire-names : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) → names (fire t p) ≡ names t
    fire-names (coldˢ s hd (frame τ e t b))     (here _) = refl
    fire-names (mapˢ f s)                       p = fire-names s p
    fire-names (scanˢ f r s)                    p = cong (_ ∷_) (fire-names s p)
    fire-names (takeWhileˢ i q c k s)           p = cong (λ x → cutNames c ++ (slot _ , k) ∷ x) (fire-names s p)
    fire-names (flatMapˢ op f fl oc k r so ls)  p with ∈-++⁻ (pendings so) p
    ... | inj₁ q = cong (λ x → flatNames fl ++ cutNames oc ++ (slot _ , k) ∷ (slot _ , r) ∷ x ++ laneNames ls) (fire-names so q)
    ... | inj₂ q = cong (λ x → flatNames fl ++ cutNames oc ++ (slot _ , k) ∷ (slot _ , r) ∷ names so ++ x) (fire-lane-names ls q)
    fire-names (connectˢ S e src body)          p with ∈-++⁻ (pendings src) p
    ... | inj₁ q = cong (λ x → subjectNames S ++ x ++ names body) (fire-names src q)
    ... | inj₂ q = cong (λ x → subjectNames S ++ names src ++ x) (fire-names body q)

    fire-lane-names : ∀ {h Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) → laneNames (fireLanes ls p) ≡ laneNames ls
    fire-lane-names (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
    ... | inj₁ q = cong (λ x → cutNames c ++ (slot _ , k) ∷ x ++ laneNames ls) (fire-names s q)
    ... | inj₂ q = cong (λ x → cutNames c ++ (slot _ , k) ∷ names s ++ x) (fire-lane-names ls q)

  mutual
    fire-subjects : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) → subjects (fire t p) ≡ subjects t
    fire-subjects (coldˢ s hd (frame τ e t b))     (here _) = refl
    fire-subjects (mapˢ f s)                       p = fire-subjects s p
    fire-subjects (scanˢ f r s)                    p = fire-subjects s p
    fire-subjects (takeWhileˢ i q c k s)           p = fire-subjects s p
    fire-subjects (flatMapˢ op f fl oc k r so ls)  p with ∈-++⁻ (pendings so) p
    ... | inj₁ q = cong (_++ laneSubjects ls) (fire-subjects so q)
    ... | inj₂ q = cong (subjects so ++_) (fire-lane-subjects ls q)
    fire-subjects (connectˢ S e src body)          p with ∈-++⁻ (pendings src) p
    ... | inj₁ q = cong (λ x → (_ , S) ∷ x ++ subjects body) (fire-subjects src q)
    ... | inj₂ q = cong (λ x → (_ , S) ∷ subjects src ++ x) (fire-subjects body q)

    fire-lane-subjects : ∀ {h Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) → laneSubjects (fireLanes ls p) ≡ laneSubjects ls
    fire-lane-subjects (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
    ... | inj₁ q = cong (_++ laneSubjects ls) (fire-subjects s q)
    ... | inj₂ q = cong (subjects s ++_) (fire-lane-subjects ls q)

  mutual
    fire-joiners : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) E → joiners (fire t p) E ≡ joiners t E
    fire-joiners (coldˢ s hd (frame τ e t b))     (here _) E = refl
    fire-joiners (mapˢ f s)                       p E = fire-joiners s p E
    fire-joiners (scanˢ f r s)                    p E = fire-joiners s p E
    fire-joiners (takeWhileˢ i q c k s)           p E = fire-joiners s p E
    fire-joiners (flatMapˢ op f fl oc k r so ls)  p E with ∈-++⁻ (pendings so) p
    ... | inj₁ q = cong (_++ laneJoiners ls E) (fire-joiners so q E)
    ... | inj₂ q = cong (joiners so E ++_) (fire-lane-joiners ls q E)
    fire-joiners (connectˢ S e src body)          p E with ∈-++⁻ (pendings src) p
    ... | inj₁ q = cong (_++ joiners body (S ∷ E)) (fire-joiners src q E)
    ... | inj₂ q = cong (joiners src E ++_) (fire-joiners body q (S ∷ E))

    fire-lane-joiners : ∀ {h Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) E → laneJoiners (fireLanes ls p) E ≡ laneJoiners ls E
    fire-lane-joiners (lane c k s ∷ ls) p E with ∈-++⁻ (pendings s) p
    ... | inj₁ q = cong (_++ laneJoiners ls E) (fire-joiners s q E)
    ... | inj₂ q = cong (joiners s E ++_) (fire-lane-joiners ls q E)

  fire-unsub : ∀ {h Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) → unsub (fire t p) ≡ unsub t
  fire-unsub (coldˢ s hd (frame τ e t b))     (here _) = refl
  fire-unsub (mapˢ f s)                       p = fire-unsub s p
  fire-unsub (scanˢ f r s)                    p = fire-unsub s p
  fire-unsub (takeWhileˢ i q c k s)           p = refl
  fire-unsub (flatMapˢ op f fl oc k r so ls)  p with ∈-++⁻ (pendings so) p
  ... | inj₁ q = refl
  ... | inj₂ q = refl
  fire-unsub (connectˢ S e src body)          p with ∈-++⁻ (pendings src) p
  ... | inj₁ q = cong (_>>ᴬ unsub body) (fire-unsub src q)
  ... | inj₂ q = cong (unsub src >>ᴬ_) (fire-unsub body q)

  module Fired {h : World} (H : All (Val h) h) where
    open At H

    -- Starting it moves no node: a frame due and a frame at its first step
    -- mean the same.
    mutual
      fire-part : ∀ {Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) E → part (fire t p) E ≡ part t E
      fire-part (coldˢ s hd (frame τ e t b))     (here _) E = refl
      fire-part (mapˢ f s)                       p E = cong (mapᴹ (mapᶜ f)) (fire-part s p E)
      fire-part (scanˢ f r s)                    p E = cong (mapᴹ (scanᶜ f (val r))) (fire-part s p E)
      fire-part (takeWhileˢ i q c k s)           p E = cong (λ x → if val (Kit.live c) then mapᴹ (takeWhileᶜ i q) x else nothing) (fire-part s p E)
      fire-part (flatMapˢ op f fl oc k r so ls)  p E with ∈-++⁻ (pendings so) p
      ... | inj₁ q = cong (λ x → merged op f x (partLanes ls E) (val (Flat.queue fl))) (fire-part so q E)
      ... | inj₂ q = cong (λ x → merged op f (part so E) x (val (Flat.queue fl))) (fire-part-lanes ls q E)
      fire-part (connectˢ S e src body)          p E with ∈-++⁻ (pendings src) p
      ... | inj₁ q = cong (λ x → connected x e (part body (S ∷ E))) (fire-part src q E)
      ... | inj₂ q = cong (connected (part src E) e) (fire-part body q (S ∷ E))

      fire-part-lanes : ∀ {Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) E → partLanes (fireLanes ls p) E ≡ partLanes ls E
      fire-part-lanes (lane c k s ∷ ls) p E with ∈-++⁻ (pendings s) p
      ... | inj₁ q = cong (λ x → if val (Kit.live c) then consᴹ x (partLanes ls E) else partLanes ls E) (fire-part s q E)
      ... | inj₂ q = cong (λ x → if val (Kit.live c) then consᴹ (part s E) x else x) (fire-part-lanes ls q E)

    -- Nor anything a kernel holds.
    mutual
      fire-holds : ∀ {Δ A} {tm : Timer h} (t : Sub h Δ A) (p : tm ∈ pendings t) {E o} → Holds t E o → Holds (fire t p) E o
      fire-holds (coldˢ s hd (frame τ e t b))     (here _) z = z
      fire-holds (mapˢ f s)                       p z = fire-holds s p z
      fire-holds (scanˢ f r s)                    p z = fire-holds s p z
      fire-holds (takeWhileˢ i q c k s)           p (u , z) = subst (heldIs c k) (sym (fire-unsub s p)) u , fire-holds s p z
      fire-holds (flatMapˢ op f fl oc k r so ls)  p {E} z with ∈-++⁻ (pendings so) p
      fire-holds (flatMapˢ op f fl oc k r so ls)  p {E} (a , b , u , z , d , y , w , zl) | inj₁ q =
        a , b , subst (heldIs oc k) (sym (fire-unsub so q)) u , fire-holds so q z
          , trans d (cong isNothing (sym (fire-part so q E))) , y , w , zl
      fire-holds (flatMapˢ op f fl oc k r so ls)  p {E} {o} (a , b , u , z , d , y , w , zl) | inj₂ q =
        a , b , u , z , d , trans y (fire-count ls q) , trans w (fire-switches ls q) , fire-holds-lanes ls q {op} {f} {E} {o} {fl} zl
      fire-holds (connectˢ S e src body)          p {E} z with ∈-++⁻ (pendings src) p
      fire-holds (connectˢ S e src body)          p {E} (zs , zb , c , x) | inj₁ q =
        fire-holds src q zs , zb , trans c (cong isNothing (sym (fire-part src q E)))
        , λ n → x (trans (cong isNothing (sym (fire-part src q E))) n)
      fire-holds (connectˢ S e src body)          p {E} (zs , zb , c , x) | inj₂ q = zs , fire-holds body q zb , c , x

      fire-holds-lanes : ∀ {Δ A B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) {op} {f : A → Obs Timeline Δ B} {E o fl}
                       → HoldsLanes op f E o fl ls → HoldsLanes op f E o fl (fireLanes ls p)
      fire-holds-lanes (lane c k s ∷ ls) p {E = E} z with ∈-++⁻ (pendings s) p
      fire-holds-lanes (lane c k s ∷ ls) p {E = E} (u , z , l , zl) | inj₁ q =
        subst (heldIs c k) (sym (fire-unsub s q)) u , fire-holds s q z
        , (λ v → trans (cong isNothing (fire-part s q E)) (l v)) , zl
      fire-holds-lanes (lane c k s ∷ ls) p {op} {f} {E} {o} {fl} (u , z , l , zl) | inj₂ q =
        u , z , l , fire-holds-lanes ls q {op} {f} {E} {o} {fl} zl

      fire-count : ∀ {Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) → count ls ≡ count (fireLanes ls p)
      fire-count (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
      ... | inj₁ q = refl
      ... | inj₂ q = cong (λ x → if val (Kit.live c) then suc x else x) (fire-count ls q)

      fire-switches : ∀ {Δ B} {tm : Timer h} (ls : List (Lane h Δ B)) (p : tm ∈ lanePendings ls) → switches ls ≡ switches (fireLanes ls p)
      fire-switches (lane c k s ∷ ls) p with ∈-++⁻ (pendings s) p
      ... | inj₁ q = refl
      ... | inj₂ q = cong (c ∷_) (fire-switches ls q)

  -- A TIMER NOT SPENT STARTS ITS FRAME: popped, its cold inside the frame,
  -- and nothing else the configuration holds moved.
  firing-start : ∀ {h} {c : Node [] R} {st : State h} {tm ts} (z : Holding c st) → State.timers st ≡ tm ∷ ts
               → lower (get (State.heap st) (Timer.handle tm)) ≡ false
               → Σ (tm ∈ pendings (Holding.tree z)) λ p →
                 Σ (Holding c (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })) λ z′ → Holding.tree z′ ≡ fire (Holding.tree z) p
  firing-start {h} {st = st} {tm} {ts} z eq s = p , record
    { tree    = fire tree p
    ; holds   = fire-holds tree p holds
    ; open≡   = trans (fire-part tree p []) open≡
    ; timed   = tabulate queued , tabulate pending′
    ; joined  = subst₂ Joined (sym (fire-subjects tree p)) (sym (fire-joiners tree p [])) joined
    ; ordered = ordered-pop {st = st} ordered eq
    ; fresh   = subst (AllPairs _≢_) (sym (fire-names tree p)) fresh
    } , refl
    where
      open Holding z
      open At (State.heap st)
      open Fired (State.heap st)
      firstAll : All (λ x → spentʰ (Timer.handle x) ≡ true ⊎ x ∈ pendings tree) (tm ∷ ts)
      firstAll = subst (All _) eq (proj₁ timed)
      p : tm ∈ pendings tree
      p with firstAll
      ... | inj₁ sp ∷ _ = absurd (trans (sym sp) s)
      ... | inj₂ m  ∷ _ = m
      sp : Split tm (pendings tree) (pendings (fire tree p))
      sp = fire-split tree p
      open Split sp
      distinct : AllPairs (λ x y → hname x ≢ hname y) (pre ++ tm ∷ post)
      distinct = subst (AllPairs _) was (pend-distinct tree fresh)
      after : All (λ u → cascade tm <ᵖ cascade u ≡ true) ts
      after = linked-after (subst (Linked _) eq (proj₁ ordered))
      lift′ : ∀ {x} → x ∈ pre ++ post → x ∈ pre ++ tm ∷ post
      lift′ m with ∈-++⁻ pre m
      ... | inj₁ m′ = ∈-++⁺ˡ m′
      ... | inj₂ m′ = ∈-++⁺ʳ pre (there m′)
      queued : ∀ {x} → x ∈ ts → spentʰ (Timer.handle x) ≡ true ⊎ x ∈ pendings (fire tree p)
      queued {x} m with lookup (tailᴬ firstAll) m
      ... | inj₁ sp′ = inj₁ sp′
      ... | inj₂ m′ with ∈-++⁻ pre (subst (x ∈_) was m′)
      ...   | inj₁ a          = inj₂ (subst (x ∈_) (sym now) (∈-++⁺ˡ a))
      ...   | inj₂ (there b)  = inj₂ (subst (x ∈_) (sym now) (∈-++⁺ʳ pre b))
      ...   | inj₂ (here refl) = absurd (trans (sym (lookup after m)) (<ᵖ-irrefl (cascade tm)))
      pending′ : ∀ {x} → x ∈ pendings (fire tree p) → spentʰ (Timer.handle x) ≡ false → x ∈ ts
      pending′ {x} m f with subst (x ∈_) eq (lookup (proj₂ timed) (subst (x ∈_) (sym was) (lift′ (subst (x ∈_) now m))) f)
      ... | here refl = ⊥-elim (once pre distinct (subst (x ∈_) now m))
      ... | there i   = i
