{-# OPTIONS --guardedness --large-indices #-}

module adequacy.Strong.Against where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Empty using (⊥)
open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Linked using (Linked) renaming ([] to []ᴸ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import denotation.MonotonicList using (Agree)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (inside; Time; Pos; From; Frame; Timeline; at; emit; stall; close; ix; last; tick; root; _<ᵖ_) renaming (done to doneᶠ; quiet to quietᶠ; sub to subᴾ)
open import operation.AbstractObservable using (base; maybe; quiet; gate; module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; note; module Pure)
open import operation.Machine using (module Machine)
import denotation.Unfold as U
open import adequacy.Placed.Order using () renaming (Placed to Placedᵍ)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import adequacy.Strong using (module Strongly)

module StrongAgainst (R : Set) where
  open Heap using (World; Kind; cell; slot; hush; play; _⊑_; _∋_; Sink; Handle; Quiet; _⨾_; same)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Shared Timeline (Out R) using (Callbacks; Heapᴹ; look; Conf; Ctl; Stack; bottom; push; rest; back; rehold; run; asking; ⟨_,_,_⟩) renaming (held to holding)
  open Pure R using (Timer; cascade)
  open Machine R using (Mach; Playing; begin)
  open SortingWalk R using (WellMach; begin-well)
  open Strongly R using (Alg; module At; Call; module Canon; Feed; module Fold; Here; Lane; Path; PathLanes; Phase; Settled; Sub; Taking; _≗_; _⊕_; _⊕ᴸ_; bodyC; coldˢ; connectˢ; deferˢ; doneˢ; emitC; ending; feedC; feeding; finC; finishing; fired; flatMapˢ; here; idle; in-body; in-defer; in-lanes; in-map; in-outer; in-scan; in-source; in-take; joiners; joinˢ; lane; mapˢ; names; next-lane; ofˢ; pendings; pendingˢ; playing; rootObs; scanˢ; srcC; subjects; take1C; take2C; takeWhileˢ; taken; taking; this-lane; top; waiting; walk; ⊕-here; ⟦_⟧)
  open Canon
  open Here

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

  -- Two nodes leaving alike: what each still runs past an unsubscribe,
  -- under every environment, the same at every depth.
  Leaves : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
  Leaves {Γ} x y = ∀ (ρ : U.NEnv Γ) n → Agree n (U.meaning (U.restᶜ {B = ⊤} x) ρ) (U.meaning (U.restᶜ {B = ⊤} y) ρ)

  -- WHAT THE GHOST HOLDS LEAVES WHAT THE HEAP WOULD: below `t`, each seen
  -- part, a held flatMap's pool and a held connect's ended source's rest
  -- each leave what the witness reads off as their leftover, to every
  -- depth, where `Lingers` pins only the next step.
  record Leaving {h} (H : Heapᴹ h) {Δ A} (t : Sub h Δ A) : Set₁ where
    field
      parts : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H ψ ≡ true → ∀ {c} → At.part H u ≡ just c → Leaves c (At.leftover H {B = ⊤} u)
      pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
            → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
            → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Leaves pl (At.pooled H fl so ls)
      rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
            → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
            → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Leaves rt (At.leftover H {B = ⊤} src)

  -- WHAT HOLDS BELOW A HELD NODE, NODE BY NODE: each node's obligation
  -- once it is held, each child held as its parent is and its step
  -- holds; a held flatMap's pool and a held connect's rest besides.
