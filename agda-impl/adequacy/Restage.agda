{-# OPTIONS --guardedness #-}

-- A PENDING NODE RESTAGED: the tree with it replaced, every call the run
-- owes carried across.  A call's code reads only its node's fields and
-- the walk to it, and a walk reads no node's children, so a call aimed
-- beside the node, or at an ancestor, aims at the same fields in the new
-- tree; one aimed at the node itself is a connect's `srcC` owing its
-- source, which the control rules out.
module adequacy.Restage where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; _<_; _≤_; _+_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; +-identityʳ; +-monoʳ-<; +-monoˡ-<; m≤n⇒m≤1+n; <-irrefl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; _∧_; _∨_; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (Lift; lift; lower)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; quiet; joins; sink; list; fifo)
open import operation.PureObservable using (module Pure)

module Restaging (R : Set) where
  open Machine R using (Mach; mach; step; silent; Playing; wkPlaying; wkTodo)
  open Unsubbing R using (_⇝_; now; then; ≗-trans; wk≗; bind≗; wk-same; wkEnv-same; from-same)
  open Growing R using (wkTree; wkLanes; wkPath; wkFeed)
  open Sequencing R using (wkEnv-wk; wk-wk; from-⨾; seq-done; wk∋-wk; wkEl-wk)
  open Pure R using (Timer; wkTimer; mapList; cascade)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack; run; Val; extend; look; cbs; wkVal; store; Callbacks; Stored; stored; get; wkAll)
  open Heap using (World; _⊑_; _⨾_; _∋_; there; new; grow; wk∋; cell; slot; Sink; Quiet; Handle) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; emitAll; done; newRef; under; readRef; writeRef; register; _>>ᴬ_; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; wkR; wkEl; Observer; Kont; wkObs; wkKont; Subject; Subscription; wkSubn; Subscribe; wkSub)
  open Run.Kit (Pureᴾ R) using (skipᴬ)
  open Strongly R using (Carried; Books; carried; Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; ending; taken; idle; feeding; finishing; bodyK; srcK
                        ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane
                        ; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf
                        ; Call; emitC; kontC; Spot; spot; coldˢ; take1C; take2C; bodyC; feedC; finC; srcC; code; Job; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Heads; Lingers; names; laneNames; pendings; rootObs
                        ; Owes; Begun; Settled; SettledLanes; Feed; Phase; timerOf; lanePendings; subjects; joiners
                        ; Name; quietName; cutNames; flatNames; subjectNames
                        ; Pinned; unpinned; pinned-trans; pinned-sym; union-pinned; under-pinned; under-moved; bursts-pinned; bursts-moved; rest-pinned; Restful; rf-idle; rf-rest; rf-union; restful-pinned; Tied
                        ; seen; seenL; seen-⊕; isTaking; ∧-split; flatMapˢ; killAllᶜ; flatK; scanˢ; joinˢ; doneˢ; deferˢ; lane; CbRel; ≗-refl; newRef≗; taking; takeK; unsubscribing; done≗; register≗; send≗; finish≗; startCold≗; stop≗; stash≗; cancel≗; eff≗; here≗; under≗; diverge≗; unfold≗; readRef≗; writeRef≗; module Canon)
                        renaming (⟦_⟧ to ⟦_⟧ᶜ; at⟦_⟧ to at⟦_⟧ᶜ)
  open Strongly.Against R using (CtlAs; StackAs; BurstAs; subAs; runAs; bottomAs; restAs; backAs; reholdAs; Held; bottomᴴ; restᴴ; playsAs; firesAs; overAs; stackJobs; SrcOf; src-of; Ticked; BurstClocked; sources; burstSpots; stackBursts; Placed; agenda)
  open Strongly.Phase R using (waiting; playing; fired)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pend; pendᴸ; syn-pos; part-plant; names-plant; holds-plant; holds-owed; settled-plant; gated-plant; fed-plant; pendings-plant; subjects-plant; joiners-plant
                     ; Same; same; same-map; same-scan; same-take; same-flat; same-connect; same-defer; head-map; head-scan)
  open Ghosting R using (walk-⊕; _≺_; measure; firstCall; each-sub; sorted-⇝)

  -- The program a subscription about to begin begins.
  subOf : ∀ {h} {t : Sub h [] R} {p c bs} → CtlAs t p c bs → Maybe (Σ (List Set) λ Δ → Σ Set λ A → T.Obs Timeline Δ A)
  subOf (subAs {s = s} _ _ _ _) = just (_ , _ , s)
  subOf _                     = nothing

  -- A path to a planted node walks as the path it replaced: a walk reads
  -- no node's children.
  mutual
    walk-planted : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ρ : Path t x) (v : Sub h Δ′ A′) (H : Here h Δ A)
                 → walk (planted ρ v) H ≡ walk ρ H
    walk-planted here         v H = refl
    walk-planted (in-map ρ)   v H = walk-planted ρ v _
    walk-planted (in-scan ρ)  v H = walk-planted ρ v _
    walk-planted (in-take ρ)  v H = walk-planted ρ v _
    walk-planted (in-outer ρ) v H = walk-planted ρ v _
    walk-planted (in-lanes {op = op} {f} {fl} ρ) v H = walk-plantedᴸ op f fl H ρ v
    walk-planted (in-source ρ) v H = walk-planted ρ v _
    walk-planted (in-body ρ)  v H = walk-planted ρ v _
    walk-planted (in-defer ρ) v H = walk-planted ρ v _

    walk-plantedᴸ : ∀ {h Δ A B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} op (f : A → T.Obs Timeline Δ B) fl (H : Here h Δ B)
                    (ρ : PathLanes ls x) (v : Sub h Δ′ A′) → walkLanes op f fl H (plantedᴸ ρ v) ≡ walkLanes op f fl H ρ
    walk-plantedᴸ op f fl H (this-lane ρ) v = walk-planted ρ v _
    walk-plantedᴸ op f fl H (next-lane ρ) v = walk-plantedᴸ op f fl H ρ v

  -- A plant owing fewer subscriptions than what it replaced owes fewer.
  mutual
    pend-less : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ρ : Path t x) (v : Sub h Δ′ A′) → pend v < pend x → pend (plant ρ v) < pend t
    pend-less here                    v lt = lt
    pend-less (in-map ρ)              v lt = pend-less ρ v lt
    pend-less (in-scan ρ)             v lt = pend-less ρ v lt
    pend-less (in-take ρ)             v lt = pend-less ρ v lt
    pend-less (in-outer {ls = ls} ρ)  v lt = +-monoˡ-< (pendᴸ ls) (pend-less ρ v lt)
    pend-less (in-lanes {t = so} ρ)   v lt = +-monoʳ-< (pend so) (pend-lessᴸ ρ v lt)
    pend-less (in-source {bd = bd} ρ) v lt = +-monoˡ-< (pend bd) (pend-less ρ v lt)
    pend-less (in-body {t = s} ρ)     v lt = +-monoʳ-< (pend s) (pend-less ρ v lt)
    pend-less (in-defer ρ)            v lt = pend-less ρ v lt

    pend-lessᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (ρ : PathLanes ls x) (v : Sub h Δ′ A′)
               → pend v < pend x → pendᴸ (plantᴸ ρ v) < pendᴸ ls
    pend-lessᴸ (this-lane {ls = ls} ρ) v lt       = +-monoˡ-< (pendᴸ ls) (pend-less ρ v lt)
    pend-lessᴸ (next-lane {l = Strongly.lane c k s} ρ) v lt = +-monoʳ-< (pend s) (pend-lessᴸ ρ v lt)

  ------------------------------------------------------------------------
  -- Where a path sits against a pending node planted over

  -- Beside the node: a path in the new tree walking alike.  Or above
  -- it, the node `ρ` below: the path to what that subtree became.
  data Fork {h Δ A Δ₀ A₀ Δ′ A′} {t : Sub h Δ A} {s₀ q₀} (π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
            {u : Sub h Δ′ A′} (π : Path t u) : Set₁ where
    apart : (π′ : Path (plant π₀ v) u) → (∀ W → walk π′ W ≡ walk π W) → Fork π₀ v π
    below : (ρ : Path u (pendingˢ s₀ q₀)) → π₀ ≡ π ⊕ ρ → (π′ : Path (plant π₀ v) (plant ρ v)) → (∀ W → walk π′ W ≡ walk π W) → Fork π₀ v π

  data ForkL {h Δ B Δ₀ A₀ Δ′ A′} {ls : List (Lane h Δ B)} {s₀ q₀} (π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
             {u : Sub h Δ′ A′} (π : PathLanes ls u) : Set₁ where
    apartᴸ : (π′ : PathLanes (plantᴸ π₀ v) u) → (∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π′ ≡ walkLanes op f fl W π)
           → ForkL π₀ v π
    belowᴸ : (ρ : Path u (pendingˢ s₀ q₀)) → π₀ ≡ π ⊕ᴸ ρ → (π′ : PathLanes (plantᴸ π₀ v) (plant ρ v))
           → (∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π′ ≡ walkLanes op f fl W π) → ForkL π₀ v π

  mutual
    fork : ∀ {h Δ A Δ₀ A₀ Δ′ A′} {t : Sub h Δ A} {s₀ q₀} (π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
           {u : Sub h Δ′ A′} (π : Path t u) → Fork π₀ v π
    fork π₀ v here = below π₀ refl here (λ _ → refl)
    fork (in-map a) v (in-map b) with fork a v b
    ... | apart π′ w     = apart (in-map π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-map e) (in-map π′) (λ _ → w _)
    fork (in-scan a) v (in-scan b) with fork a v b
    ... | apart π′ w     = apart (in-scan π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-scan e) (in-scan π′) (λ _ → w _)
    fork (in-take a) v (in-take b) with fork a v b
    ... | apart π′ w     = apart (in-take π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-take e) (in-take π′) (λ _ → w _)
    fork (in-outer a) v (in-outer b) with fork a v b
    ... | apart π′ w     = apart (in-outer π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-outer e) (in-outer π′) (λ _ → w _)
    fork (in-outer a) v (in-lanes b) = apart (in-lanes b) (λ _ → refl)
    fork (in-lanes a) v (in-outer b) = apart (in-outer b) (λ _ → refl)
    fork (in-lanes {op = op} {f} {fl} a) v (in-lanes b) with forkᴸ a v b
    ... | apartᴸ π′ w     = apart (in-lanes π′) (λ W → w op f fl W)
    ... | belowᴸ ρ e π′ w = below ρ (cong in-lanes e) (in-lanes π′) (λ W → w op f fl W)
    fork (in-source a) v (in-source b) with fork a v b
    ... | apart π′ w     = apart (in-source π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-source e) (in-source π′) (λ _ → w _)
    fork (in-source a) v (in-body b) = apart (in-body b) (λ _ → refl)
    fork (in-body a) v (in-source b) = apart (in-source b) (λ _ → refl)
    fork (in-body a) v (in-body b) with fork a v b
    ... | apart π′ w     = apart (in-body π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-body e) (in-body π′) (λ _ → w _)
    fork (in-defer a) v (in-defer b) with fork a v b
    ... | apart π′ w     = apart (in-defer π′) (λ _ → w _)
    ... | below ρ e π′ w = below ρ (cong in-defer e) (in-defer π′) (λ _ → w _)

    forkᴸ : ∀ {h Δ B Δ₀ A₀ Δ′ A′} {ls : List (Lane h Δ B)} {s₀ q₀} (π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
            {u : Sub h Δ′ A′} (π : PathLanes ls u) → ForkL π₀ v π
    forkᴸ (this-lane a) v (this-lane b) with fork a v b
    ... | apart π′ w     = apartᴸ (this-lane π′) (λ _ _ _ _ → w _)
    ... | below ρ e π′ w = belowᴸ ρ (cong this-lane e) (this-lane π′) (λ _ _ _ _ → w _)
    forkᴸ (this-lane a) v (next-lane b) = apartᴸ (next-lane b) (λ _ _ _ _ → refl)
    forkᴸ (next-lane a) v (this-lane b) = apartᴸ (this-lane b) (λ _ _ _ _ → refl)
    forkᴸ (next-lane a) v (next-lane b) with forkᴸ a v b
    ... | apartᴸ π′ w     = apartᴸ (next-lane π′) (λ op f fl W → w op f fl W)
    ... | belowᴸ ρ e π′ w = belowᴸ ρ (cong next-lane e) (next-lane π′) (λ op f fl W → w op f fl W)

  -- A leaf holds nothing pending beneath it.
  leaf-below : ∀ {h Δ A Δ₀ A₀ s₀ q₀} {u : Sub h Δ A} → Leaf u → Path u (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀) → ⊥
  leaf-below of-leaf   ()
  leaf-below cold-leaf ()
  leaf-below done-leaf ()
  leaf-below join-leaf ()

  -- Codes alike when their walks are.
  module _ {h} {t t′ : Sub h [] R} where
    emit-code : ∀ {Δ A p i xs} (π′ : Path t′ (ofˢ {Δ = Δ} {A} p i xs)) (π : Path t (ofˢ p i xs)) → walk π′ top ≡ walk π top
              → code (emitC π′) ≡ code (emitC π)
    emit-code π′ π e rewrite e = refl

    kont-code : ∀ {Δ A} {u : Sub h Δ A} (lf : Leaf u) (π′ : Path t′ u) (π : Path t u) → walk π′ top ≡ walk π top
              → code (kontC lf π′) ≡ code (kontC lf π)
    kont-code lf π′ π e rewrite e = refl

    take1-code : ∀ {Δ A i p c k q n} {s′ s : Sub h Δ A} (π′ : Path t′ (takeWhileˢ i p c k (ending q n) s′)) (π : Path t (takeWhileˢ i p c k (ending q n) s))
               → walk π′ top ≡ walk π top → code (take1C π′) ≡ code (take1C π)
    take1-code π′ π e rewrite e = refl

    src-code : ∀ {Δ A B S c b kb k fd e s₁ q rp rt} {bd′ bd : Sub h (A ∷ Δ) B}
                 (π′ : Path t′ (connectˢ S c b kb k fd rp e rt (pendingˢ {Δ = Δ} s₁ q) bd′)) (π : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q) bd))
             → (∀ W → walk π′ W ≡ walk π W) → code (srcC π′) ≡ code (srcC π)
    src-code π′ π w rewrite walk-⊕ π′ (in-source here) top | walk-⊕ π (in-source here) top | w top = refl

  -- Where a fork sends a path: the path it lands on.
  data Lands {h Δ A Δ₀ A₀ Δ′ A′} {t : Sub h Δ A} {s₀ q₀} {π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {v : Sub h Δ₀ A₀}
             {u : Sub h Δ′ A′} {π : Path t u} : ∀ {Δ″ A″} {w : Sub h Δ″ A″} → Fork π₀ v π → Path (plant π₀ v) w → Set₁ where
    lands-apart : ∀ {π′ wk} → Lands (apart π′ wk) π′
    lands-below : ∀ {ρ e π′ wk} → Lands (below ρ e π′ wk) π′

  data LandsL {h Δ B Δ₀ A₀ Δ′ A′} {ls : List (Lane h Δ B)} {s₀ q₀} {π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {v : Sub h Δ₀ A₀}
              {u : Sub h Δ′ A′} {π : PathLanes ls u} : ∀ {Δ″ A″} {w : Sub h Δ″ A″} → ForkL π₀ v π → PathLanes (plantᴸ π₀ v) w → Set₁ where
    landsᴸ-apart : ∀ {π′ : PathLanes (plantᴸ π₀ v) u} {wk : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π′ ≡ walkLanes op f fl W π}
                 → LandsL (apartᴸ π′ wk) π′
    landsᴸ-below : ∀ {ρ : Path u (pendingˢ s₀ q₀)} {e} {π′ : PathLanes (plantᴸ π₀ v) (plant ρ v)}
                     {wk : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π′ ≡ walkLanes op f fl W π}
                 → LandsL (belowᴸ ρ e π′ wk) π′

  module _ {h Δ₀ A₀ s₀ q₀} {v : Sub h Δ₀ A₀} where
    land-map : ∀ {Δ A B Δ′ A′ Δ″ A″} {f : A → B} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                 {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′ → Lands (fork (in-map {f = f} a) v (in-map b)) (in-map π′)
    land-map {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-scan : ∀ {Δ A B Δ′ A′ Δ″ A″} {f : B → A → B} {r} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                  {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′ → Lands (fork (in-scan {f = f} {r} a) v (in-scan b)) (in-scan π′)
    land-scan {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-take : ∀ {Δ A Δ′ A′ Δ″ A″} {i p c k tk} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                  {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′ → Lands (fork (in-take {i = i} {p} {c} {k} {tk} a) v (in-take b)) (in-take π′)
    land-take {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-outer : ∀ {Δ A B Δ′ A′ Δ″ A″} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                   {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′
               → Lands (fork (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} a) v (in-outer b)) (in-outer π′)
    land-outer {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-lanes : ∀ {Δ A B Δ′ A′ Δ″ A″} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {a : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : PathLanes ls u}
                   {w : Sub h Δ″ A″} {π′ : PathLanes (plantᴸ a v) w} → LandsL (forkᴸ a v b) π′
               → Lands (fork (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} a) v (in-lanes b)) (in-lanes π′)
    land-lanes {a = a} {b = b} ld with forkᴸ a v b | ld
    ... | apartᴸ _ _     | landsᴸ-apart = lands-apart
    ... | belowᴸ _ _ _ _ | landsᴸ-below = lands-below

    land-source : ∀ {Δ A B Δ′ A′ Δ″ A″} {S c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {β : Path t u}
                    {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v β) π′
                → Lands (fork (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {bd = bd} a) v (in-source β)) (in-source π′)
    land-source {a = a} {β = β} ld with fork a v β | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-body : ∀ {Δ A B Δ′ A′ Δ″ A″} {S c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {a : Path bd (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {β : Path bd u}
                  {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v β) π′
              → Lands (fork (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} a) v (in-body β)) (in-body π′)
    land-body {a = a} {β = β} ld with fork a v β | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-defer : ∀ {Δ A Δ′ A′ Δ″ A″} {k} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                   {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′ → Lands (fork (in-defer {k = k} a) v (in-defer b)) (in-defer π′)
    land-defer {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = lands-apart
    ... | below _ _ _ _ | lands-below = lands-below

    land-this : ∀ {Δ B Δ′ A′ Δ″ A″} {c k} {t : Sub h Δ B} {ls : List (Lane h Δ B)} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : Path t u}
                  {w : Sub h Δ″ A″} {π′ : Path (plant a v) w} → Lands (fork a v b) π′ → LandsL (forkᴸ (this-lane {c = c} {k} {ls = ls} a) v (this-lane b)) (this-lane π′)
    land-this {a = a} {b = b} ld with fork a v b | ld
    ... | apart _ _     | lands-apart = landsᴸ-apart
    ... | below _ _ _ _ | lands-below = landsᴸ-below

    land-next : ∀ {Δ B Δ′ A′ Δ″ A″} {l : Lane h Δ B} {ls : List (Lane h Δ B)} {a : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {b : PathLanes ls u}
                  {w : Sub h Δ″ A″} {π′ : PathLanes (plantᴸ a v) w} → LandsL (forkᴸ a v b) π′ → LandsL (forkᴸ (next-lane {l = l} a) v (next-lane b)) (next-lane π′)
    land-next {a = a} {b = b} ld with forkᴸ a v b | ld
    ... | apartᴸ _ _     | landsᴸ-apart = landsᴸ-apart
    ... | belowᴸ _ _ _ _ | landsᴸ-below = landsᴸ-below

  module _ {h Δ₀ A₀ s₀ q₀} {v : Sub h Δ₀ A₀} where
    -- The planted node is where the fork of its own path lands.
    mutual
      lands-planted : ∀ {Δ A} {t : Sub h Δ A} (π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) → Lands (fork π₀ v π₀) (planted π₀ v)
      lands-planted here          = lands-below
      lands-planted (in-map a)    = land-map (lands-planted a)
      lands-planted (in-scan a)   = land-scan (lands-planted a)
      lands-planted (in-take a)   = land-take (lands-planted a)
      lands-planted (in-outer a)  = land-outer (lands-planted a)
      lands-planted (in-lanes a)  = land-lanes (lands-plantedᴸ a)
      lands-planted (in-source a) = land-source (lands-planted a)
      lands-planted (in-body a)   = land-body (lands-planted a)
      lands-planted (in-defer a)  = land-defer (lands-planted a)

      lands-plantedᴸ : ∀ {Δ B} {ls : List (Lane h Δ B)} (π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) → LandsL (forkᴸ π₀ v π₀) (plantedᴸ π₀ v)
      lands-plantedᴸ (this-lane a) = land-this (lands-planted a)
      lands-plantedᴸ (next-lane a) = land-next (lands-plantedᴸ a)

    lands-unique : ∀ {Δ A Δ′ A′ Δ₁ A₁ Δ₂ A₂} {t : Sub h Δ A} {π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {u : Sub h Δ′ A′} {π : Path t u} {F : Fork π₀ v π}
                   {w₁ : Sub h Δ₁ A₁} {w₂ : Sub h Δ₂ A₂} {x : Path (plant π₀ v) w₁} {y : Path (plant π₀ v) w₂} → Lands F x → Lands F y → spot x ≡ spot y
    lands-unique lands-apart lands-apart = refl
    lands-unique lands-below lands-below = refl

  -- A connect's path against the path to its source: beside the plant
  -- both, or the plant in its body, the source's path beside it.
  data ExtS {h Δ A Δ₀ A₀ Δ₁ A₁ B₁} {t : Sub h Δ A} {s₀ q₀} {π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {v : Sub h Δ₀ A₀}
            {S c b kb k fd e rp rt s₁ q₁} {bd : Sub h (A₁ ∷ Δ₁) B₁} {π₁ : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q₁) bd)}
            : Fork π₀ v π₁ → Fork π₀ v (π₁ ⊕ in-source here) → Set₁ where
    exts-apart : ∀ {π″ wk wk′} → ExtS (apart π″ wk) (apart (π″ ⊕ in-source here) wk′)
    exts-body  : ∀ {ρ e π″ wk wk′} → ExtS (below (in-body ρ) e π″ wk) (apart (π″ ⊕ in-source here) wk′)
    exts-src   : ∀ {ρ e π″ wk G} → ExtS (below (in-source ρ) e π″ wk) G

  data ExtSL {h Δ B Δ₀ A₀ Δ₁ A₁ B₁} {ls : List (Lane h Δ B)} {s₀ q₀} {π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {v : Sub h Δ₀ A₀}
             {S c b kb k fd e rp rt s₁ q₁} {bd : Sub h (A₁ ∷ Δ₁) B₁} {π₁ : PathLanes ls (connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q₁) bd)}
             : ForkL π₀ v π₁ → ForkL π₀ v (π₁ ⊕ᴸ in-source here) → Set₁ where
    extsᴸ-apart : ∀ {π″ : PathLanes (plantᴸ π₀ v) (connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q₁) bd)}
                    {wk : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π″ ≡ walkLanes op f fl W π₁}
                    {wk′ : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W (π″ ⊕ᴸ in-source here) ≡ walkLanes op f fl W (π₁ ⊕ᴸ in-source here)}
                → ExtSL (apartᴸ π″ wk) (apartᴸ (π″ ⊕ᴸ in-source here) wk′)
    extsᴸ-body  : ∀ {ρ : Path bd (pendingˢ s₀ q₀)} {e′} {π″ : PathLanes (plantᴸ π₀ v) (plant (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = pendingˢ s₁ q₁} ρ) v)}
                    {wk : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π″ ≡ walkLanes op f fl W π₁}
                    {wk′ : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W (π″ ⊕ᴸ in-source here) ≡ walkLanes op f fl W (π₁ ⊕ᴸ in-source here)}
                → ExtSL (belowᴸ (in-body ρ) e′ π″ wk) (apartᴸ (π″ ⊕ᴸ in-source here) wk′)
    extsᴸ-src   : ∀ {ρ : Path (pendingˢ s₁ q₁) (pendingˢ s₀ q₀)} {e′} {π″ : PathLanes (plantᴸ π₀ v) (plant (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {bd = bd} ρ) v)}
                    {wk : ∀ {A} op (f : A → T.Obs Timeline Δ B) fl W → walkLanes op f fl W π″ ≡ walkLanes op f fl W π₁} {G}
                → ExtSL (belowᴸ (in-source ρ) e′ π″ wk) G

  module _ {h Δ₀ A₀ s₀ q₀} {v : Sub h Δ₀ A₀} {Δ₁ A₁ B₁} {S c b kb k fd e rp rt s₁ q₁} {bd : Sub h (A₁ ∷ Δ₁) B₁} where
    private
      X = connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q₁) bd

    ext-map : ∀ {Δ A B} {f : A → B} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
            → ExtS (fork a v β) (fork a v (β ⊕ in-source here)) → ExtS (fork (in-map {f = f} a) v (in-map β)) (fork (in-map a) v (in-map (β ⊕ in-source here)))
    ext-map {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-scan : ∀ {Δ A B} {f : B → A → B} {r} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
             → ExtS (fork a v β) (fork a v (β ⊕ in-source here)) → ExtS (fork (in-scan {f = f} {r} a) v (in-scan β)) (fork (in-scan a) v (in-scan (β ⊕ in-source here)))
    ext-scan {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-take : ∀ {Δ A} {i p c′ k′ tk} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
             → ExtS (fork a v β) (fork a v (β ⊕ in-source here)) → ExtS (fork (in-take {i = i} {p} {c′} {k′} {tk} a) v (in-take β)) (fork (in-take a) v (in-take (β ⊕ in-source here)))
    ext-take {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-outer : ∀ {Δ A B} {op f fl oc k′ r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
              → ExtS (fork a v β) (fork a v (β ⊕ in-source here))
              → ExtS (fork (in-outer {op = op} {f} {fl} {oc} {k′} {r} {pl} {ls = ls} a) v (in-outer β)) (fork (in-outer a) v (in-outer (β ⊕ in-source here)))
    ext-outer {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-lanes : ∀ {Δ A B} {op f fl oc k′ r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {a : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : PathLanes ls X}
              → ExtSL (forkᴸ a v β) (forkᴸ a v (β ⊕ᴸ in-source here))
              → ExtS (fork (in-lanes {op = op} {f} {fl} {oc} {k′} {r} {pl} {t = t} a) v (in-lanes β)) (fork (in-lanes a) v (in-lanes (β ⊕ᴸ in-source here)))
    ext-lanes {a = a} {β} x with forkᴸ a v β | forkᴸ a v (β ⊕ᴸ in-source here) | x
    ... | _ | _ | extsᴸ-apart = exts-apart
    ... | _ | _ | extsᴸ-body  = exts-body
    ... | _ | _ | extsᴸ-src   = exts-src

    ext-source : ∀ {Δ A B} {S′ c′ b′ kb′ k′ fd′ e′ rp′ rt′} {t : Sub h Δ A} {bd′ : Sub h (A ∷ Δ) B} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
               → ExtS (fork a v β) (fork a v (β ⊕ in-source here))
               → ExtS (fork (in-source {S = S′} {c′} {b′} {kb′} {k′} {fd′} {e′} {rp′} {rt′} {bd = bd′} a) v (in-source β)) (fork (in-source a) v (in-source (β ⊕ in-source here)))
    ext-source {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-body : ∀ {Δ A B} {S′ c′ b′ kb′ k′ fd′ e′ rp′ rt′} {t : Sub h Δ A} {bd′ : Sub h (A ∷ Δ) B} {a : Path bd′ (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path bd′ X}
             → ExtS (fork a v β) (fork a v (β ⊕ in-source here))
             → ExtS (fork (in-body {S = S′} {c′} {b′} {kb′} {k′} {fd′} {e′} {rp′} {rt′} {t = t} a) v (in-body β)) (fork (in-body a) v (in-body (β ⊕ in-source here)))
    ext-body {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-defer : ∀ {Δ A} {k′} {t : Sub h Δ A} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
              → ExtS (fork a v β) (fork a v (β ⊕ in-source here)) → ExtS (fork (in-defer {k = k′} a) v (in-defer β)) (fork (in-defer a) v (in-defer (β ⊕ in-source here)))
    ext-defer {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = exts-apart
    ... | _ | _ | exts-body  = exts-body
    ... | _ | _ | exts-src   = exts-src

    ext-this : ∀ {Δ B} {c′ k′} {t : Sub h Δ B} {ls : List (Lane h Δ B)} {a : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : Path t X}
             → ExtS (fork a v β) (fork a v (β ⊕ in-source here))
             → ExtSL (forkᴸ (this-lane {c = c′} {k′} {ls = ls} a) v (this-lane β)) (forkᴸ (this-lane a) v (this-lane (β ⊕ in-source here)))
    ext-this {a = a} {β} x with fork a v β | fork a v (β ⊕ in-source here) | x
    ... | _ | _ | exts-apart = extsᴸ-apart
    ... | _ | _ | exts-body  = extsᴸ-body
    ... | _ | _ | exts-src   = extsᴸ-src

    ext-next : ∀ {Δ B} {l : Lane h Δ B} {ls : List (Lane h Δ B)} {a : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)} {β : PathLanes ls X}
             → ExtSL (forkᴸ a v β) (forkᴸ a v (β ⊕ᴸ in-source here))
             → ExtSL (forkᴸ (next-lane {l = l} a) v (next-lane β)) (forkᴸ (next-lane a) v (next-lane (β ⊕ᴸ in-source here)))
    ext-next {a = a} {β} x with forkᴸ a v β | forkᴸ a v (β ⊕ᴸ in-source here) | x
    ... | _ | _ | extsᴸ-apart = extsᴸ-apart
    ... | _ | _ | extsᴸ-body  = extsᴸ-body
    ... | _ | _ | extsᴸ-src   = extsᴸ-src

    mutual
      exts : ∀ {Δ A} {t : Sub h Δ A} (π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (π₁ : Path t X) → ExtS (fork π₀ v π₁) (fork π₀ v (π₁ ⊕ in-source here))
      exts (in-source a) here         = exts-src
      exts (in-body a)   here         = exts-body
      exts (in-map a)    (in-map β)   = ext-map (exts a β)
      exts (in-scan a)   (in-scan β)  = ext-scan (exts a β)
      exts (in-take a)   (in-take β)  = ext-take (exts a β)
      exts (in-outer a)  (in-outer β) = ext-outer (exts a β)
      exts (in-outer a)  (in-lanes β) = exts-apart
      exts (in-lanes a)  (in-outer β) = exts-apart
      exts (in-lanes a)  (in-lanes β) = ext-lanes (extsᴸ a β)
      exts (in-source a) (in-source β) = ext-source (exts a β)
      exts (in-source a) (in-body β)  = exts-apart
      exts (in-body a)   (in-source β) = exts-apart
      exts (in-body a)   (in-body β)  = ext-body (exts a β)
      exts (in-defer a)  (in-defer β) = ext-defer (exts a β)

      extsᴸ : ∀ {Δ B} {ls : List (Lane h Δ B)} (π₀ : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (π₁ : PathLanes ls X)
            → ExtSL (forkᴸ π₀ v π₁) (forkᴸ π₀ v (π₁ ⊕ᴸ in-source here))
      extsᴸ (this-lane a) (this-lane β) = ext-this (exts a β)
      extsᴸ (this-lane a) (next-lane β) = extsᴸ-apart
      extsᴸ (next-lane a) (this-lane β) = extsᴸ-apart
      extsᴸ (next-lane a) (next-lane β) = ext-next (extsᴸ a β)

  -- A spot a connect's source sits at, owed by its call; and a call to
  -- a connect whose source sits at a path.
  data SrcSpot {h} {t : Sub h [] R} (x : Spot t) : Call t → Set₁ where
    src-spot : ∀ {Δ A B S c b kb k fd e rp rt s q} {bd : Sub h (A ∷ Δ) B} (π : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
             → x ≡ spot (π ⊕ in-source here) → SrcSpot x (srcC π)

  data SrcAt {h} {t : Sub h [] R} {Δ A s q} : Call t → Path t (pendingˢ {Δ = Δ} {A} s q) → Set₁ where
    src-at : ∀ {B S c b kb k fd e rp rt} {bd : Sub h (A ∷ Δ) B} (π : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
           → SrcAt (srcC π) (π ⊕ in-source here)

  module _ {h} {t : Sub h [] R} where

    sources-there : ∀ (j : Job t) js {x} → x ∈ sources t js → x ∈ sources t (j ∷ js)
    sources-there (_ , emitC _)   js m = m
    sources-there (_ , kontC _ _) js m = m
    sources-there (_ , take1C _)  js m = m
    sources-there (_ , take2C _)  js m = m
    sources-there (_ , bodyC _)   js m = m
    sources-there (_ , feedC _)   js m = m
    sources-there (_ , finC _)    js m = m
    sources-there (_ , srcC _)    js m = thereᴬ m

    src-mem : ∀ (js : List (Job t)) {x} → x ∈ sources t js → Σ (Job t) λ j → j ∈ js × SrcSpot x (proj₂ j)
    src-mem ((p , srcC π) ∷ js) (hereᴬ e) = (p , srcC π) , hereᴬ refl , src-spot π e
    src-mem ((p , srcC π) ∷ js) (thereᴬ m) with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , emitC _)   ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , kontC _ _) ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , take1C _)  ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , take2C _)  ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , bodyC _)   ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , feedC _)   ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp
    src-mem ((p , finC _)    ∷ js) m with src-mem js m
    ... | j , mj , sp = j , thereᴬ mj , sp

    sources-mem : ∀ (js : List (Job t)) {Δ A s q p k} {ψ : Path t (pendingˢ {Δ = Δ} {A} s q)} → (p , k) ∈ js → SrcAt k ψ → spot ψ ∈ sources t js
    sources-mem (_ ∷ js) (hereᴬ refl) (src-at _) = hereᴬ refl
    sources-mem (j ∷ js) (thereᴬ m)   sa         = sources-there j js (sources-mem js m sa)

  ------------------------------------------------------------------------
  -- What the ghost holds, carried across

  -- What a connect owes its source, alike in the two trees.
  Sourced : ∀ {h} (H : Heapᴹ h) {Δ A} {w₀ w : Sub h Δ A} → Same w₀ w → Set₁
  Sourced H (same-connect {s = s} {s′}) = At.part H s ≡ At.part H s′
  Sourced H _                           = ⊤₁

  -- A node of the rewritten tree: at or below the planted node, or one of
  -- the old tree's, held alike and with the same part.
  Kept : ∀ {h} (H : Heapᴹ h) {Δ A Δ₀ A₀ s₀ q₀ Δ″ A″} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) {w : Sub h Δ″ A″}
       → Path (plant π v) w → Set₁
  Kept H {t = t} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ planted π v ⊕ ρ)
                            ⊎ (Σ _ λ w₀ → Σ (Path t w₀) λ ψ₀ → Σ (Same w₀ w) λ sm → seen H ψ₀ ≡ seen H π′ × At.part H w₀ ≡ At.part H w × Sourced H sm
                                                                × Lands (fork π v ψ₀) π′)

  KeptL : ∀ {h} (H : Heapᴹ h) {Δ B Δ₀ A₀ s₀ q₀ Δ″ A″} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) {w : Sub h Δ″ A″}
        → PathLanes (plantᴸ π v) w → Set₁
  KeptL H {ls = ls} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ plantedᴸ π v ⊕ᴸ ρ)
                               ⊎ (Σ _ λ w₀ → Σ (PathLanes ls w₀) λ ψ₀ → Σ (Same w₀ w) λ sm → seenL H ψ₀ ≡ seenL H π′ × At.part H w₀ ≡ At.part H w × Sourced H sm
                                                                     × LandsL (forkᴸ π v ψ₀) π′)

  module _ {h} (H : Heapᴹ h) where
    mutual
      keep : ∀ {Δ A Δ₀ A₀ s₀ q₀ Δ″ A″} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
           → {w : Sub h Δ″ A″} (π′ : Path (plant π v) w) → Kept H π v π′
      keep here v eq π′ = inj₁ (π′ , refl)
      keep π₁@(in-map π) v eq here = inj₂ (_ , here , same-map , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-map π) v eq (in-map π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-map e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-map q , sm , se , pe , so , land-map ld)
      keep π₁@(in-scan π) v eq here = inj₂ (_ , here , same-scan , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-scan π) v eq (in-scan π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-scan e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-scan q , sm , se , pe , so , land-scan ld)
      keep π₁@(in-take π) v eq here = inj₂ (_ , here , same-take , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-take {c = c} {tk = tk} π) v eq (in-take π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-take e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-take q , sm , cong (λ z → At.val H (Kit.live c) ∧ isTaking tk ∧ z) se , pe , so , land-take ld)
      keep π₁@(in-outer π) v eq here = inj₂ (_ , here , same-flat , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-outer π) v eq (in-outer π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-outer e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-outer q , sm , se , pe , so , land-outer ld)
      keep (in-outer π) v eq (in-lanes π′) = inj₂ (_ , in-lanes π′ , same , refl , refl , tt₁ , lands-apart)
      keep π₁@(in-lanes π) v eq here = inj₂ (_ , here , same-flat , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-lanes π) v eq (in-outer π′) = inj₂ (_ , in-outer π′ , same , refl , refl , tt₁ , lands-apart)
      keep (in-lanes π) v eq (in-lanes π′) with keepᴸ π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-lanes e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-lanes q , sm , se , pe , so , land-lanes ld)
      keep π₁@(in-source π) v eq here = inj₂ (_ , here , same-connect , refl , sym (part-plant H π₁ v eq) , sym (part-plant H π v eq) , lands-below)
      keep (in-source {bd = bd} π) v eq (in-source π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-source e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-source q , sm , cong (is-just (At.part H bd) ∧_) se , pe , so , land-source ld)
      keep (in-source {e = e} π) v eq (in-body π′) =
        inj₂ (_ , in-body π′ , same , cong (λ z → (is-just z ∨ is-just e) ∧ seen H π′) (sym (part-plant H π v eq)) , refl , tt₁ , lands-apart)
      keep π₁@(in-body π) v eq here = inj₂ (_ , here , same-connect , refl , sym (part-plant H π₁ v eq) , refl , lands-below)
      keep (in-body π) v eq (in-source π′) = inj₂ (_ , in-source π′ , same , cong (λ z → is-just z ∧ seen H π′) (sym (part-plant H π v eq)) , refl , tt₁ , lands-apart)
      keep (in-body {e = e} {t = src} π) v eq (in-body π′) with keep π v eq π′
      ... | inj₁ (ρ , e′)                   = inj₁ (ρ , cong in-body e′)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-body q , sm , cong ((is-just (At.part H src) ∨ is-just e) ∧_) se , pe , so , land-body ld)
      keep π₁@(in-defer π) v eq here = inj₂ (_ , here , same-defer , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-defer π) v eq (in-defer π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-defer e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-defer q , sm , se , pe , so , land-defer ld)

      keepᴸ : ∀ {Δ B Δ₀ A₀ s₀ q₀ Δ″ A″} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
            → {w : Sub h Δ″ A″} (π′ : PathLanes (plantᴸ π v) w) → KeptL H π v π′
      keepᴸ (this-lane {c = c} π) v eq (this-lane π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong this-lane e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , this-lane q , sm , cong (At.val H (Kit.live c) ∧_) se , pe , so , land-this ld)
      keepᴸ (this-lane π) v eq (next-lane π′) = inj₂ (_ , next-lane π′ , same , refl , refl , tt₁ , landsᴸ-apart)
      keepᴸ (next-lane π) v eq (this-lane π′) = inj₂ (_ , this-lane π′ , same , refl , refl , tt₁ , landsᴸ-apart)
      keepᴸ (next-lane π) v eq (next-lane π′) with keepᴸ π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong next-lane e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , next-lane q , sm , se , pe , so , land-next ld)

    -- The path to the planted node is held as the path it replaced: what
    -- a path's hold reads lies beside it.
    mutual
      seen-planted : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → seen H (planted π v) ≡ seen H π
      seen-planted here v                            = refl
      seen-planted (in-map π) v                      = seen-planted π v
      seen-planted (in-scan π) v                     = seen-planted π v
      seen-planted (in-take {c = c} {tk = tk} π) v   = cong (λ z → At.val H (Kit.live c) ∧ isTaking tk ∧ z) (seen-planted π v)
      seen-planted (in-outer π) v                    = seen-planted π v
      seen-planted (in-lanes π) v                    = seen-plantedᴸ π v
      seen-planted (in-source {bd = bd} π) v         = cong (is-just (At.part H bd) ∧_) (seen-planted π v)
      seen-planted (in-body {e = e} {t = src} π) v   = cong ((is-just (At.part H src) ∨ is-just e) ∧_) (seen-planted π v)
      seen-planted (in-defer π) v                    = seen-planted π v

      seen-plantedᴸ : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → seenL H (plantedᴸ π v) ≡ seenL H π
      seen-plantedᴸ (this-lane {c = c} π) v = cong (At.val H (Kit.live c) ∧_) (seen-planted π v)
      seen-plantedᴸ (next-lane π) v         = seen-plantedᴸ π v

    -- What the ghost holds of a node planted with the same part, it holds
    -- of the tree.
    each-plant : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ A Δ₀ A₀ s₀ q₀} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
               → At.part H (pendingˢ s₀ q₀) ≡ At.part H v → (Each H P (pendingˢ s₀ q₀) → Each H P v) → Each H P t → Each H P (plant π v)
    each-plant {P} {t = t} π v eq tr ev = record { parts = pa ; pools = po ; rests = re }
      where
        inside : ∀ {Δ″ A″} {w : Sub h Δ″ A″} {ψ : Path (plant π v) w} (ρ : Path v w) → ψ ≡ planted π v ⊕ ρ → seen H ψ ≡ true
               → Each H P v × seen H ρ ≡ true
        inside ρ refl s with ∧-split (seen H (planted π v)) (trans (sym (seen-⊕ H (planted π v) ρ)) s)
        ... | sp , sρ = tr (each-sub ev π (trans (sym (seen-planted π v)) sp)) , sρ

        pa : ∀ {Δ′ A′} {w : Sub h Δ′ A′} (ψ : Path (plant π v) w) → seen H ψ ≡ true → ∀ {c} → At.part H w ≡ just c → P c
        pa ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.parts ev′ ρ sρ pw
        pa ψ s pw | inj₂ (_ , ψ₀ , _ , se , pe , _ , _) = Each.parts ev ψ₀ (trans se s) (trans pe pw)

        po : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
           → (ψ : Path (plant π v) (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
           → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
        po ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.pools ev′ ρ sρ pw
        po ψ s pw | inj₂ (_ , ψ₀ , same , se , pe , _ , _)      = Each.pools ev ψ₀ (trans se s) (trans pe pw)
        po ψ s pw | inj₂ (_ , ψ₀ , same-flat , se , pe , _ , _) = Each.pools ev ψ₀ (trans se s) (trans pe pw)

        re : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → (ψ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
           → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
           → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
        re ψ s pn ps pe′ with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.rests ev′ ρ sρ pn ps pe′
        re ψ s pn ps pe′ | inj₂ (_ , ψ₀ , same , se , pe , _ , _)          = Each.rests ev ψ₀ (trans se s) (trans pe pn) ps pe′
        re ψ s pn ps pe′ | inj₂ (_ , ψ₀ , same-connect , se , pe , so , _) = Each.rests ev ψ₀ (trans se s) (trans pe pn) (trans so ps) pe′

    -- What a node leaves running steps as it rests.
    leftover-restful : ∀ {Δ A B} (s : Sub h Δ A) → Restful (At.leftover H {B = B} s)
    leftover-restful (pendingˢ s q)                          = rf-rest
    leftover-restful (coldˢ s hd ph)                         = rf-idle
    leftover-restful (ofˢ p i xs)                            = rf-idle
    leftover-restful doneˢ                                   = rf-idle
    leftover-restful (mapˢ f s)                              = leftover-restful s
    leftover-restful (scanˢ f r s)                           = leftover-restful s
    leftover-restful (takeWhileˢ i p c k tk s)               = leftover-restful s
    leftover-restful (flatMapˢ op f fl oc k r pl so ls)      = rf-union
    leftover-restful (connectˢ S c b kb k fd rp e rt src bd) = rf-union
    leftover-restful (joinˢ j sk l x st)                     = rf-idle
    leftover-restful (deferˢ k s)                            = leftover-restful s

    if-pinned : ∀ {Γ A} b {x x′ y y′ : U.Node Γ A} → Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} x′) → Pinned (U.restˢ {B = ⊤} y) (U.restˢ {B = ⊤} y′)
              → Pinned (U.restˢ {B = ⊤} (if b then x else y)) (U.restˢ {B = ⊤} (if b then x′ else y′))
    if-pinned true  p _ = p
    if-pinned false _ q = q

    -- A node planted whose leftover pins as the pending one's: every
    -- leftover above it pins alike.
    mutual
      leftover-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀ B} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                     → (∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} (pendingˢ s₀ q₀))) (U.restˢ {B = ⊤} (At.leftover H {B = C} v)))
                     → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = B} t)) (U.restˢ {B = ⊤} (At.leftover H {B = B} (plant π v)))
      leftover-plant here v eq lv                            = lv
      leftover-plant (in-map π) v eq lv                      = leftover-plant π v eq lv
      leftover-plant (in-scan π) v eq lv                     = leftover-plant π v eq lv
      leftover-plant (in-take π) v eq lv                     = leftover-plant π v eq lv
      leftover-plant (in-defer π) v eq lv                    = leftover-plant π v eq lv
      leftover-plant (in-outer {ls = ls} π) v eq lv          = union-pinned (leftover-plant π v eq lv) (rest-pinned (At.leftoverL H ls))
      leftover-plant (in-lanes {t = so} π) v eq lv           = union-pinned (rest-pinned (At.leftover H so)) (leftoverL-plant π v eq lv)
      leftover-plant (in-body {rp = rp} {t = src} π) v eq lv =
        union-pinned (bursts-pinned rp n (U.step n)) (under-moved (U.live n) (U.live n) (leftover-plant π v eq lv))
        where n = At.sourced H (At.part H src) (At.leftover H src)
      leftover-plant (in-source {rp = rp} {t = src} {bd = bd} π) v eq lv rewrite part-plant H π v eq with At.part H src
      ... | just s  = union-pinned (bursts-pinned rp s (U.step s)) (under-pinned (U.live s) (U.restˢ {B = ⊤} (At.leftover H {B = ⊤} bd)))
      ... | nothing =
        union-pinned (bursts-moved rp stepped (leftover-plant π v eq lv)) (under-moved (U.live n) (U.live n′) (rest-pinned (At.leftover H {B = ⊤} bd)))
        where
          n  = At.leftover H src
          n′ = At.leftover H (plant π v)
          stepped : Pinned (U.step n) (U.step n′)
          stepped = pinned-trans (restful-pinned (leftover-restful src))
                      (pinned-trans (rest-pinned n) (pinned-trans (leftover-plant π v eq lv)
                        (pinned-trans (rest-pinned n′) (pinned-sym (restful-pinned (leftover-restful (plant π v)))))))

      leftoverL-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀ B} {ls : List (Lane h Δ A)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                      → (∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} (pendingˢ s₀ q₀))) (U.restˢ {B = ⊤} (At.leftover H {B = C} v)))
                      → Pinned (U.restˢ {B = ⊤} (At.leftoverL H {B = B} ls)) (U.restˢ {B = ⊤} (At.leftoverL H {B = B} (plantᴸ π v)))
      leftoverL-plant (this-lane {ls = ls} π) v eq lv          = union-pinned (leftover-plant π v eq lv) (rest-pinned (At.leftoverL H ls))
      leftoverL-plant (next-lane {l = lane c k s} π) v eq lv   = union-pinned (rest-pinned (At.leftover H s)) (leftoverL-plant π v eq lv)

    -- A pool over a planted outer or lane: what its ended parts left pins
    -- alike.
    pooled-outer : ∀ {Δ A B Δ₀ A₀ s₀ q₀} {fl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} (π : Path so (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
                 → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                 → (∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} (pendingˢ s₀ q₀))) (U.restˢ {B = ⊤} (At.leftover H {B = C} v)))
                 → Pinned (U.restˢ {B = ⊤} (At.pooled H fl so ls)) (U.restˢ {B = ⊤} (At.pooled H fl (plant π v) ls))
    pooled-outer {fl = fl} {ls = ls} π v eq lv =
      union-pinned (if-pinned (At.val H (FlatKit.Flat.outerDone fl)) (leftover-plant π v eq lv) unpinned) (rest-pinned (At.pooledL H ls))

    pooled-lanes : ∀ {Δ B Δ₀ A₀ s₀ q₀} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
                 → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                 → (∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} (pendingˢ s₀ q₀))) (U.restˢ {B = ⊤} (At.leftover H {B = C} v)))
                 → Pinned (U.restˢ {B = ⊤} (At.pooledL H {B = B} ls)) (U.restˢ {B = ⊤} (At.pooledL H {B = B} (plantᴸ π v)))
    pooled-lanes (this-lane {c = c} {ls = ls} π) v eq lv =
      if-pinned (At.val H (Kit.live c)) (rest-pinned (At.pooledL H ls)) (union-pinned (leftover-plant π v eq lv) (rest-pinned (At.pooledL H ls)))
    pooled-lanes (next-lane {l = lane c k s} π) v eq lv =
      if-pinned (At.val H (Kit.live c)) (pooled-lanes π v eq lv) (union-pinned (rest-pinned (At.leftover H s)) (pooled-lanes π v eq lv))

    -- A pool whose outer has not ended and holds no lane runs nothing.
    pooled-fresh : ∀ {Δ A B C} {fl : FlatKit.Flat A h} {so : Sub h Δ A} → At.val H (FlatKit.Flat.outerDone fl) ≡ false → Pinned (U.hushˢ {A = C}) (U.restˢ {B = ⊤} (At.pooled H {B = B} fl so []))
    pooled-fresh d rewrite d = unpinned

    -- What a node planted leaves running pins as the pending node's: each
    -- held pool and ended source above it keeps its pin.
    lingers-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                  → (∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} (pendingˢ s₀ q₀))) (U.restˢ {B = ⊤} (At.leftover H {B = C} v)))
                  → Lingers H v → Lingers H t → Lingers H (plant π v)
    lingers-plant {t = t} π v eq lv lgv lg = record { pools = po ; rests = re }
      where
        inside : ∀ {Δ″ A″} {w : Sub h Δ″ A″} {ψ : Path (plant π v) w} (ρ : Path v w) → ψ ≡ planted π v ⊕ ρ → seen H ψ ≡ true → seen H ρ ≡ true
        inside ρ refl s = proj₂ (∧-split (seen H (planted π v)) (trans (sym (seen-⊕ H (planted π v) ρ)) s))

        pool-lands : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so so′ : Sub h Δ′ A′} {ls ls′ : List (Lane h Δ′ B′)}
                       {ψ₀ : Path t (flatMapˢ op f fl oc k r pl so ls)} {ψ′ : Path (plant π v) (flatMapˢ op f fl oc k r pl so′ ls′)}
                   → Lands (fork π v ψ₀) ψ′ → Pinned (U.restˢ {B = ⊤} (At.pooled H fl so ls)) (U.restˢ {B = ⊤} (At.pooled H fl so′ ls′))
        pool-lands {fl = fl} {so = so} {ls = ls} {ψ₀ = ψ₀} ld with fork π v ψ₀ | ld
        ... | apart _ _                | lands-apart = rest-pinned (At.pooled H fl so ls)
        ... | below (in-outer ρ) _ _ _ | lands-below = pooled-outer {fl = fl} {ls = ls} ρ v eq lv
        ... | below (in-lanes ρ) _ _ _ | lands-below = union-pinned (rest-pinned (if At.val H (FlatKit.Flat.outerDone fl) then At.leftover H so else U.idleᶜ)) (pooled-lanes ρ v eq lv)

        rest-lands : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src src′ : Sub h Δ′ A′} {bd bd′ : Sub h (A′ ∷ Δ′) B′}
                       {ψ₀ : Path t (connectˢ S c b kb k fd rp e rt src bd)} {ψ′ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src′ bd′)}
                   → Lands (fork π v ψ₀) ψ′ → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = ⊤} src)) (U.restˢ {B = ⊤} (At.leftover H {B = ⊤} src′))
        rest-lands {src = src} {ψ₀ = ψ₀} ld with fork π v ψ₀ | ld
        ... | apart _ _                 | lands-apart = rest-pinned (At.leftover H {B = ⊤} src)
        ... | below (in-source ρ) _ _ _ | lands-below = leftover-plant ρ v eq lv
        ... | below (in-body ρ) _ _ _   | lands-below = rest-pinned (At.leftover H {B = ⊤} src)

        po : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
           → (ψ : Path (plant π v) (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
           → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Tied pl (At.pooled H fl so ls)
        po ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e)                                  = Lingers.pools lgv ρ (inside ρ e s) pw
        ... | inj₂ (_ , ψ₀ , same , se , pe , _ , _)        = Lingers.pools lg ψ₀ (trans se s) (trans pe pw)
        ... | inj₂ (_ , ψ₀ , same-flat , se , pe , _ , ld)  = pinned-trans (Lingers.pools lg ψ₀ (trans se s) (trans pe pw)) (pool-lands ld)

        re : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → (ψ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
           → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
           → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Tied rt (At.leftover H {B = ⊤} src)
        re ψ s pn ps pe′ with keep π v eq ψ
        ... | inj₁ (ρ , e)                                     = Lingers.rests lgv ρ (inside ρ e s) pn ps pe′
        ... | inj₂ (_ , ψ₀ , same , se , pe , _ , _)           = Lingers.rests lg ψ₀ (trans se s) (trans pe pn) ps pe′
        ... | inj₂ (_ , ψ₀ , same-connect , se , pe , so , ld) =
          pinned-trans (Lingers.rests lg ψ₀ (trans se s) (trans pe pn) (trans so ps) pe′) (rest-lands ld)

  ------------------------------------------------------------------------
  -- The run's calls, carried across

  module Moved {h} {t : Sub h [] R} {Δ₀ A₀ s₀ q₀} (π₀ : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) where
    t′ : Sub h [] R
    t′ = plant π₀ v

    rcall : (k : Call t) → ¬ SrcOf t π₀ k → Σ (Call t′) λ k′ → code k′ ≡ code k
    rcall (emitC π) _ with fork π₀ v π
    ... | apart π′ w        = emitC π′ , emit-code π′ π (w top)
    ... | below () _ _ _
    rcall (kontC lf π) _ with fork π₀ v π
    ... | apart π′ w        = kontC lf π′ , kont-code lf π′ π (w top)
    ... | below ρ _ _ _     = ⊥-elim (leaf-below lf ρ)
    rcall (take1C π) _ with fork π₀ v π
    ... | apart π′ w              = take1C π′ , take1-code π′ π (w top)
    ... | below (in-take _) _ π′ w = take1C π′ , take1-code π′ π (w top)
    rcall (take2C π) _ with fork π₀ v π
    ... | apart π′ _               = take2C π′ , refl
    ... | below (in-take _) _ π′ _ = take2C π′ , refl
    rcall (bodyC π) _ with fork π₀ v π
    ... | apart π′ _                 = bodyC π′ , refl
    ... | below (in-source _) _ π′ _ = bodyC π′ , refl
    ... | below (in-body _) _ π′ _   = bodyC π′ , refl
    rcall (feedC π) _ with fork π₀ v π
    ... | apart π′ _                 = feedC π′ , refl
    ... | below (in-source _) _ π′ _ = feedC π′ , refl
    ... | below (in-body _) _ π′ _   = feedC π′ , refl
    rcall (finC π) _ with fork π₀ v π
    ... | apart π′ _                 = finC π′ , refl
    ... | below (in-source _) _ π′ _ = finC π′ , refl
    ... | below (in-body _) _ π′ _   = finC π′ , refl
    rcall (srcC π) ns with fork π₀ v π
    ... | apart π′ w                    = srcC π′ , src-code π′ π w
    ... | below (in-source here) e _ _  = ⊥-elim (ns (src-of π e))
    ... | below (in-body _) _ π′ w      = srcC π′ , src-code π′ π w

    rcalls : (ks : List (Call t)) → All (λ k → ¬ SrcOf t π₀ k) ks → Σ (List (Call t′)) λ ks′ → ⟦ ks′ ⟧ᶜ ≡ ⟦ ks ⟧ᶜ
    rcalls []       []       = [] , refl
    rcalls (k ∷ ks) (n ∷ ns) with rcall k n | rcalls ks ns
    ... | k′ , e | ks′ , es = k′ ∷ ks′ , cong₂ _>>ᴬ_ e es

    reburst : ∀ {b} → BurstAs t b → BurstAs t′ b
    reburst (playsAs π) with fork π₀ v π
    ... | apart π′ _     = playsAs π′
    ... | below () _ _ _
    reburst (firesAs π) with fork π₀ v π
    ... | apart π′ _     = firesAs π′
    ... | below () _ _ _
    reburst overAs = overAs

    reheld : ∀ {w} {K : Stack w ⊤} → Held t K → Held t′ K
    reheld bottomᴴ = bottomᴴ
    reheld restᴴ   = restᴴ

    unat : ∀ {P : Call t → Set₁} p (ks : List (Call t)) → All (λ j → P (proj₂ j)) (at⟦ p ⟧ᶜ ks) → All P ks
    unat p []       []       = []
    unat p (k ∷ ks) (a ∷ as) = a ∷ unat p ks as

    Alone : ∀ {w p bs} {σ : w ⊑ h} {K} → StackAs t p σ K bs → Set₁
    Alone sk = All (λ j → ¬ SrcOf t π₀ (proj₂ j)) (stackJobs t sk)

    restack : ∀ {w p bs} {σ : w ⊑ h} {K} (sk : StackAs t p σ K bs) → Alone sk → StackAs t′ p σ K bs
    restack bottomAs _ = bottomAs
    restack (restAs {p = p} {m = m} {σ = σ} ks e K) a =
      restAs (proj₁ (rcalls ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)))))
             (subst (λ X → wkAct σ m ≗ X) (sym (proj₂ (rcalls ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)))))) e)
             (restack K (proj₂ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)))
    restack (backAs q {m = m} {σ = σ} ks lt e K) a =
      backAs q (proj₁ (rcalls ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a))))) lt
             (subst (λ X → wkAct σ m ≗ X) (sym (proj₂ (rcalls ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)))))) e)
             (restack K (proj₂ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)))
    restack (reholdAs b hd K) a = reholdAs (reburst b) (reheld hd) (restack K a)

    reclocked : ∀ {n b} (x : BurstAs t b) → BurstClocked t n x → BurstClocked t′ n (reburst x)
    reclocked (playsAs π) c with fork π₀ v π
    ... | apart π′ _     = c
    ... | below () _ _ _
    reclocked (firesAs π) c with fork π₀ v π
    ... | apart π′ _     = c
    ... | below () _ _ _
    reclocked overAs c = c

    reticked : ∀ {n w p bs} {σ : w ⊑ h} {K} (sk : StackAs t p σ K bs) (a : Alone sk) → Ticked t n sk → Ticked t′ n (restack sk a)
    reticked bottomAs _ c = c
    reticked (restAs {p = p} ks e K) a (c , cs) = c , reticked K (proj₂ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)) cs
    reticked (backAs q ks lt e K) a (c , cs)    = c , reticked K (proj₂ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)) cs
    reticked (reholdAs b hd K) a (c , cs)       = reclocked b c , reticked K a cs

    -- A call carried is the call to where its node's path lands.
    emit-lands : ∀ {Δ A p i xs} {ψ₀ : Path t (ofˢ {Δ = Δ} {A} p i xs)} {ψ′ : Path t′ (ofˢ {Δ = Δ} {A} p i xs)} → Lands (fork π₀ v ψ₀) ψ′
               → ∀ n → proj₁ (rcall (emitC ψ₀) n) ≡ emitC ψ′
    emit-lands {ψ₀ = ψ₀} ld n with fork π₀ v ψ₀ | ld
    ... | apart _ _      | lands-apart = refl
    ... | below () _ _ _ | _

    take1-lands : ∀ {Δ A i p c k q m} {s s′ : Sub h Δ A} {ψ₀ : Path t (takeWhileˢ i p c k (ending q m) s)} {ψ′ : Path t′ (takeWhileˢ i p c k (ending q m) s′)}
                → Lands (fork π₀ v ψ₀) ψ′ → ∀ n → proj₁ (rcall (take1C ψ₀) n) ≡ take1C ψ′
    take1-lands {ψ₀ = ψ₀} ld n with fork π₀ v ψ₀ | ld
    ... | apart _ _               | lands-apart = refl
    ... | below (in-take _) _ _ _ | lands-below = refl

    take2-lands : ∀ {Δ A i p c k} {s s′ : Sub h Δ A} {ψ₀ : Path t (takeWhileˢ i p c k taken s)} {ψ′ : Path t′ (takeWhileˢ i p c k taken s′)}
                → Lands (fork π₀ v ψ₀) ψ′ → ∀ n → proj₁ (rcall (take2C ψ₀) n) ≡ take2C ψ′
    take2-lands {ψ₀ = ψ₀} ld n with fork π₀ v ψ₀ | ld
    ... | apart _ _               | lands-apart = refl
    ... | below (in-take _) _ _ _ | lands-below = refl

    feed-lands : ∀ {Δ A B S c b kb k x r ss e rp rt} {s s′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B}
                   {ψ₀ : Path t (connectˢ S c b kb k (feeding x r ss) rp e rt s bd)} {ψ′ : Path t′ (connectˢ S c b kb k (feeding x r ss) rp e rt s′ bd′)}
               → Lands (fork π₀ v ψ₀) ψ′ → ∀ n → proj₁ (rcall (feedC ψ₀) n) ≡ feedC ψ′
    feed-lands {ψ₀ = ψ₀} ld n with fork π₀ v ψ₀ | ld
    ... | apart _ _                 | lands-apart = refl
    ... | below (in-source _) _ _ _ | lands-below = refl
    ... | below (in-body _) _ _ _   | lands-below = refl

    fin-lands : ∀ {Δ A B S c b kb k r ss e rp rt} {s s′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B}
                  {ψ₀ : Path t (connectˢ S c b kb k (finishing r ss) rp e rt s bd)} {ψ′ : Path t′ (connectˢ S c b kb k (finishing r ss) rp e rt s′ bd′)}
              → Lands (fork π₀ v ψ₀) ψ′ → ∀ n → proj₁ (rcall (finC ψ₀) n) ≡ finC ψ′
    fin-lands {ψ₀ = ψ₀} ld n with fork π₀ v ψ₀ | ld
    ... | apart _ _                 | lands-apart = refl
    ... | below (in-source _) _ _ _ | lands-below = refl
    ... | below (in-body _) _ _ _   | lands-below = refl

    -- A connect's source call carried: the call to where the source's
    -- path lands, unless the source is the planted node.
    src-call : ∀ {Δ₁ A₁ B₁ S c b kb k fd e rp rt s₁ q₁} {bd : Sub h (A₁ ∷ Δ₁) B₁} {π₁ : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s₁ q₁) bd)}
                 {ψ′ : Path t′ (pendingˢ s₁ q₁)} (n : ¬ SrcOf t π₀ (srcC π₁))
             → ExtS (fork π₀ v π₁) (fork π₀ v (π₁ ⊕ in-source here)) → Lands (fork π₀ v (π₁ ⊕ in-source here)) ψ′ → SrcAt (proj₁ (rcall (srcC π₁) n)) ψ′
    src-call {π₁ = π₁} n x ld with fork π₀ v π₁ | fork π₀ v (π₁ ⊕ in-source here) | x | ld
    ... | apart π″ _                 | _ | exts-apart | lands-apart = src-at π″
    ... | below (in-body _) _ π″ _   | _ | exts-body  | lands-apart = src-at π″
    ... | below (in-source here) e _ _ | _ | exts-src | _          = ⊥-elim (n (src-of π₁ e))

    -- Every job owed is owed carried, and every job carried was owed.
    head-mem : ∀ {p} k ks n ns → (p , proj₁ (rcall k n)) ∈ at⟦ p ⟧ᶜ (proj₁ (rcalls (k ∷ ks) (n ∷ ns)))
    head-mem k ks n ns with rcall k n | rcalls ks ns
    ... | _ , _ | _ , _ = hereᴬ refl

    tail-mem : ∀ {p j} k ks n ns → j ∈ at⟦ p ⟧ᶜ (proj₁ (rcalls ks ns)) → j ∈ at⟦ p ⟧ᶜ (proj₁ (rcalls (k ∷ ks) (n ∷ ns)))
    tail-mem k ks n ns m with rcall k n | rcalls ks ns | m
    ... | _ , _ | _ , _ | m′ = thereᴬ m′

    calls-mem : ∀ {p} (ks : List (Call t)) (ns : All (λ k → ¬ SrcOf t π₀ k) ks) {j} → j ∈ at⟦ p ⟧ᶜ ks
              → Σ (¬ SrcOf t π₀ (proj₂ j)) λ n → (proj₁ j , proj₁ (rcall (proj₂ j) n)) ∈ at⟦ p ⟧ᶜ (proj₁ (rcalls ks ns))
    calls-mem (k ∷ ks) (n ∷ ns) (hereᴬ refl) = n , head-mem k ks n ns
    calls-mem (k ∷ ks) (n ∷ ns) (thereᴬ m) with calls-mem ks ns m
    ... | n′ , m′ = n′ , tail-mem k ks n ns m′

    calls-back : ∀ {p} (ks : List (Call t)) (ns : All (λ k → ¬ SrcOf t π₀ k) ks) {j′} → j′ ∈ at⟦ p ⟧ᶜ (proj₁ (rcalls ks ns))
               → Σ (Job t) λ j → j ∈ at⟦ p ⟧ᶜ ks × Σ (¬ SrcOf t π₀ (proj₂ j)) λ n → j′ ≡ (proj₁ j , proj₁ (rcall (proj₂ j) n))
    calls-back {p} (k ∷ ks) (n ∷ ns) m with rcall k n in ek | rcalls ks ns in eks | m
    ... | _ , _ | _ , _ | hereᴬ refl = (p , k) , hereᴬ refl , n , cong (λ z → p , proj₁ z) (sym ek)
    ... | _ , _ | _ , _ | thereᴬ m′ with calls-back ks ns (subst (λ z → _ ∈ at⟦ p ⟧ᶜ (proj₁ z)) (sym eks) m′)
    ...   | j , mj , n′ , e = j , thereᴬ mj , n′ , e

    stack-mem : ∀ {w p bs} {σ : w ⊑ h} {K} (sk : StackAs t p σ K bs) (a : Alone sk) {j} → j ∈ stackJobs t sk
              → Σ (¬ SrcOf t π₀ (proj₂ j)) λ n → (proj₁ j , proj₁ (rcall (proj₂ j) n)) ∈ stackJobs t′ (restack sk a)
    stack-mem (restAs {p = p} ks e K) a m with any-++⁻ (at⟦ p ⟧ᶜ ks) m
    ... | inj₁ m₁ with calls-mem ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a))) m₁
    ...   | n , m′ = n , any-++⁺ˡ m′
    stack-mem (restAs {p = p} ks e K) a m | inj₂ m₂ with stack-mem K (proj₂ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)) m₂
    ...   | n , m′ = n , any-++⁺ʳ (at⟦ p ⟧ᶜ (proj₁ (rcalls ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)))))) m′
    stack-mem (backAs q ks lt e K) a m with any-++⁻ (at⟦ q ⟧ᶜ ks) m
    ... | inj₁ m₁ with calls-mem ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a))) m₁
    ...   | n , m′ = n , any-++⁺ˡ m′
    stack-mem (backAs q ks lt e K) a m | inj₂ m₂ with stack-mem K (proj₂ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)) m₂
    ...   | n , m′ = n , any-++⁺ʳ (at⟦ q ⟧ᶜ (proj₁ (rcalls ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)))))) m′
    stack-mem (reholdAs b hd K) a m = stack-mem K a m

    stack-back : ∀ {w p bs} {σ : w ⊑ h} {K} (sk : StackAs t p σ K bs) (a : Alone sk) {j′} → j′ ∈ stackJobs t′ (restack sk a)
               → Σ (Job t) λ j → j ∈ stackJobs t sk × Σ (¬ SrcOf t π₀ (proj₂ j)) λ n → j′ ≡ (proj₁ j , proj₁ (rcall (proj₂ j) n))
    stack-back (restAs {p = p} ks e K) a m with any-++⁻ (at⟦ p ⟧ᶜ (proj₁ (rcalls ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)))))) m
    ... | inj₁ m₁ with calls-back ks (unat p ks (proj₁ (all-++⁻ (at⟦ p ⟧ᶜ ks) a))) m₁
    ...   | j , mj , n , e = j , any-++⁺ˡ mj , n , e
    stack-back (restAs {p = p} ks e K) a m | inj₂ m₂ with stack-back K (proj₂ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)) m₂
    ...   | j , mj , n , e′ = j , any-++⁺ʳ (at⟦ p ⟧ᶜ ks) mj , n , e′
    stack-back (backAs q ks lt e K) a m with any-++⁻ (at⟦ q ⟧ᶜ (proj₁ (rcalls ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)))))) m
    ... | inj₁ m₁ with calls-back ks (unat q ks (proj₁ (all-++⁻ (at⟦ q ⟧ᶜ ks) a))) m₁
    ...   | j , mj , n , e′ = j , any-++⁺ˡ mj , n , e′
    stack-back (backAs q ks lt e K) a m | inj₂ m₂ with stack-back K (proj₂ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)) m₂
    ...   | j , mj , n , e′ = j , any-++⁺ʳ (at⟦ q ⟧ᶜ ks) mj , n , e′
    stack-back (reholdAs b hd K) a m = stack-back K a m

    spots-land : ∀ {bb Δ A s hd ph} {ψ₀ : Path t (coldˢ {Δ = Δ} {A} s hd ph)} {Δ′ A′} {w : Sub h Δ′ A′} {ψ′ : Path t′ w}
                 (b : BurstAs t bb) → Lands (fork π₀ v ψ₀) ψ′ → spot ψ₀ ∈ burstSpots t b → spot ψ′ ∈ burstSpots t′ (reburst b)
    spots-land (playsAs π) ld (hereᴬ refl) with fork π₀ v π | ld
    ... | apart _ _      | lands-apart = hereᴬ refl
    ... | below () _ _ _ | _
    spots-land (firesAs π) ld (hereᴬ refl) with fork π₀ v π | ld
    ... | apart _ _      | lands-apart = hereᴬ refl
    ... | below () _ _ _ | _

    burst-mem : ∀ {w p bs} {σ : w ⊑ h} {K} (sk : StackAs t p σ K bs) (a : Alone sk) {Δ A s hd ph} {ψ₀ : Path t (coldˢ {Δ = Δ} {A} s hd ph)}
                {Δ′ A′} {w : Sub h Δ′ A′} {ψ′ : Path t′ w} → Lands (fork π₀ v ψ₀) ψ′ → spot ψ₀ ∈ stackBursts t sk → spot ψ′ ∈ stackBursts t′ (restack sk a)
    burst-mem (restAs {p = p} ks e K) a ld m = burst-mem K (proj₂ (all-++⁻ (at⟦ p ⟧ᶜ ks) a)) ld m
    burst-mem (backAs q ks lt e K) a ld m    = burst-mem K (proj₂ (all-++⁻ (at⟦ q ⟧ᶜ ks) a)) ld m
    burst-mem (reholdAs b hd K) a ld m with any-++⁻ (burstSpots t b) m
    ... | inj₁ m₁ = any-++⁺ˡ (spots-land b ld m₁)
    ... | inj₂ m₂ = any-++⁺ʳ (burstSpots t′ (reburst b)) (burst-mem K a ld m₂)

    -- Where a call carried runs is where it ran.
    placed-call : ∀ {p} (k : Call t) n → Placed t (p , k) → Placed t′ (p , proj₁ (rcall k n))
    placed-call (emitC π) n pl with fork π₀ v π
    ... | apart _ _      = pl
    ... | below () _ _ _
    placed-call (kontC lf π) n pl with fork π₀ v π
    ... | apart _ _     = pl
    ... | below ρ _ _ _ = ⊥-elim (leaf-below lf ρ)
    placed-call (take1C π) n pl with fork π₀ v π
    ... | apart _ _               = pl
    ... | below (in-take _) _ _ _ = pl
    placed-call (take2C π) n pl with fork π₀ v π
    ... | apart _ _               = pl
    ... | below (in-take _) _ _ _ = pl
    placed-call (bodyC π) n pl with fork π₀ v π
    ... | apart _ _                 = pl
    ... | below (in-source _) _ _ _ = pl
    ... | below (in-body _) _ _ _   = pl
    placed-call (feedC π) n pl with fork π₀ v π
    ... | apart _ _                 = pl
    ... | below (in-source _) _ _ _ = pl
    ... | below (in-body _) _ _ _   = pl
    placed-call (finC π) n pl with fork π₀ v π
    ... | apart _ _                 = pl
    ... | below (in-source _) _ _ _ = pl
    ... | below (in-body _) _ _ _   = pl
    placed-call (srcC π) n pl with fork π₀ v π
    ... | apart _ _                    = pl
    ... | below (in-source here) e _ _ = ⊥-elim (n (src-of π e))
    ... | below (in-body _) _ _ _      = pl

    -- What the planted node holds below it: nothing owed but the one
    -- subscription it begins.
    record Inner {Δ₁ A₁ s₁} (ρ₀ : Path v (pendingˢ {Δ = Δ₁} {A₁} s₁ q₀)) : Set₁ where
      field
        no-of    : ∀ {Δ A q i xs} → Path v (ofˢ {Δ = Δ} {A} q i xs) → ⊥
        no-cold  : ∀ {Δ A s hd ph} → Path v (coldˢ {Δ = Δ} {A} s hd ph) → ⊥
        one-pend : ∀ {Δ A s q} (ρ : Path v (pendingˢ {Δ = Δ} {A} s q)) → spot ρ ≡ spot ρ₀
        no-end   : ∀ {Δ A i p c k q m} {s : Sub h Δ A} → Path v (takeWhileˢ i p c k (ending q m) s) → ⊥
        no-cut   : ∀ {Δ A i p c k} {s : Sub h Δ A} → Path v (takeWhileˢ i p c k taken s) → ⊥
        no-feed  : ∀ {Δ A B S c b kb k x r ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → Path v (connectˢ S c b kb k (feeding x r ss) rp e rt s bd) → ⊥
        no-fin   : ∀ {Δ A B S c b kb k r ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → Path v (connectˢ S c b kb k (finishing r ss) rp e rt s bd) → ⊥
        not-self : (ψ : Path t′ (pendingˢ s₀ q₀)) → spot ψ ≡ spot (planted π₀ v) → ⊥

    module Owning (H : Heapᴹ h) (eq : At.part H (pendingˢ s₀ q₀) ≡ At.part H v) where
      BodyOk : ∀ {t₁ : Sub h [] R} → Call t₁ → Set₁
      BodyOk (bodyC {bd = bd} _) = At.part H bd ≡ nothing
      BodyOk _                   = ⊤₁

      body-ok : ∀ {p ctl bs} {ca : CtlAs t p ctl bs} → Owned H t ca → ∀ j → j ∈ agenda t ca → BodyOk (proj₂ j)
      body-ok ow (_ , bodyC π)   m = Owned.bodies ow π m
      body-ok ow (_ , emitC _)   m = tt₁
      body-ok ow (_ , kontC _ _) m = tt₁
      body-ok ow (_ , take1C _)  m = tt₁
      body-ok ow (_ , take2C _)  m = tt₁
      body-ok ow (_ , feedC _)   m = tt₁
      body-ok ow (_ , finC _)    m = tt₁
      body-ok ow (_ , srcC _)    m = tt₁

      body-call : ∀ (k : Call t) n → BodyOk k → BodyOk (proj₁ (rcall k n))
      body-call (emitC π) n ok with fork π₀ v π
      ... | apart _ _      = tt₁
      ... | below () _ _ _
      body-call (kontC lf π) n ok with fork π₀ v π
      ... | apart _ _     = tt₁
      ... | below ρ _ _ _ = ⊥-elim (leaf-below lf ρ)
      body-call (take1C π) n ok with fork π₀ v π
      ... | apart _ _               = tt₁
      ... | below (in-take _) _ _ _ = tt₁
      body-call (take2C π) n ok with fork π₀ v π
      ... | apart _ _               = tt₁
      ... | below (in-take _) _ _ _ = tt₁
      body-call (bodyC π) n ok with fork π₀ v π
      ... | apart _ _                 = ok
      ... | below (in-source _) _ _ _ = ok
      ... | below (in-body ρ) _ _ _   = trans (part-plant H ρ v eq) ok
      body-call (feedC π) n ok with fork π₀ v π
      ... | apart _ _                 = tt₁
      ... | below (in-source _) _ _ _ = tt₁
      ... | below (in-body _) _ _ _   = tt₁
      body-call (finC π) n ok with fork π₀ v π
      ... | apart _ _                 = tt₁
      ... | below (in-source _) _ _ _ = tt₁
      ... | below (in-body _) _ _ _   = tt₁
      body-call (srcC π) n ok with fork π₀ v π
      ... | apart _ _                    = tt₁
      ... | below (in-source here) e _ _ = ⊥-elim (n (src-of π e))
      ... | below (in-body _) _ _ _      = tt₁

      -- Owed across the plant: each node beside it or above it owed as
      -- it was, the planted node owing only the subscription it begins.
      reowned : ∀ {Δ₁ A₁ s₁} (ρ₀ : Path v (pendingˢ {Δ = Δ₁} {A₁} s₁ q₀)) → Inner ρ₀
              → ∀ {w bs act act′} {σ : w ⊑ h} {K} {cd cd′} (sk : StackAs t q₀ σ K bs) (a : Alone sk) {a′}
              → Owned H t (subAs {act = act} π₀ cd sk a) → Owned H t′ (subAs {act = act′} (planted π₀ v ⊕ ρ₀) cd′ (restack sk a) a′)
      reowned ρ₀ inn sk a ow = record
        { ofs = ofs′ ; plays = plays′ ; fires = fires′ ; begun = begun′ ; ends = ends′ ; cuts = cuts′ ; feeds = feeds′ ; fins = fins′
        ; bodies = bodies′ ; placed = placed′ }
        where
          open Inner inn
          J′ = stackJobs t′ (restack sk a)

          ofs′ : ∀ {Δ A q i xs} (ψ′ : Path t′ (ofˢ {Δ = Δ} {A} q i xs)) → (q , emitC ψ′) ∈ J′
          ofs′ ψ′ with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-of ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with stack-mem sk a (Owned.ofs ow ψ₀)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (emit-lands ld n) m

          plays′ : ∀ {Δ A s hd τ r i u} {b : Frame A u} (ψ′ : Path t′ (coldˢ {Δ = Δ} s hd (playing τ r i b)))
                 → At.spentʰ H hd ≡ false → spot ψ′ ∈ stackBursts t′ (restack sk a)
          plays′ ψ′ nsp with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-cold ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) = burst-mem sk a ld (Owned.plays ow ψ₀ nsp)

          fires′ : ∀ {Δ A s hd τ e u} {m : From A u} (ψ′ : Path t′ (coldˢ {Δ = Δ} s hd (fired τ e m)))
                 → At.spentʰ H hd ≡ false → spot ψ′ ∈ stackBursts t′ (restack sk a)
          fires′ ψ′ nsp with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-cold ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) = burst-mem sk a ld (Owned.fires ow ψ₀ nsp)

          src-begun : ∀ {Δ A s q} {ψ₀ : Path t (pendingˢ {Δ = Δ} {A} s q)} {ψ′ : Path t′ (pendingˢ s q)} → Lands (fork π₀ v ψ₀) ψ′
                    → spot ψ₀ ∈ sources t (stackJobs t sk) → spot ψ′ ∈ sources t′ J′
          src-begun ld m with src-mem (stackJobs t sk) m
          ... | (q , srcC π₁) , mj , src-spot _ refl with stack-mem sk a mj
          ...   | n , m′ = sources-mem J′ m′ (src-call n (exts π₀ π₁) ld)

          begun′ : ∀ {Δ A s q} (ψ′ : Path t′ (pendingˢ {Δ = Δ} {A} s q)) → spot ψ′ ∈ spot (planted π₀ v ⊕ ρ₀) ∷ sources t′ J′
          begun′ ψ′ with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , e) = hereᴬ (trans (cong spot e) (cong (λ { (spot r) → spot (planted π₀ v ⊕ r) }) (one-pend ρ)))
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with Owned.begun ow ψ₀
          ...   | hereᴬ refl = ⊥-elim (not-self ψ′ (lands-unique ld (lands-planted π₀)))
          ...   | thereᴬ m   = thereᴬ (src-begun ld m)

          ends′ : ∀ {Δ A i p c k q m} {s : Sub h Δ A} (ψ′ : Path t′ (takeWhileˢ i p c k (ending q m) s))
                → At.val H (Kit.live c) ≡ true → (q , take1C ψ′) ∈ J′
          ends′ ψ′ l with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-end ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with stack-mem sk a (Owned.ends ow ψ₀ l)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (take1-lands ld n) m
          ends′ ψ′ l | inj₂ (_ , ψ₀ , same-take , _ , _ , _ , ld) with stack-mem sk a (Owned.ends ow ψ₀ l)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (take1-lands ld n) m

          cuts′ : ∀ {Δ A i p c k} {s : Sub h Δ A} (ψ′ : Path t′ (takeWhileˢ i p c k taken s))
                → At.val H (Kit.live c) ≡ true → Σ Pos λ q → (q , take2C ψ′) ∈ J′
          cuts′ ψ′ l with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-cut ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with Owned.cuts ow ψ₀ l
          ...   | q , m₀ with stack-mem sk a m₀
          ...     | n , m = q , subst (λ k → (_ , k) ∈ J′) (take2-lands ld n) m
          cuts′ ψ′ l | inj₂ (_ , ψ₀ , same-take , _ , _ , _ , ld) with Owned.cuts ow ψ₀ l
          ...   | q , m₀ with stack-mem sk a m₀
          ...     | n , m = q , subst (λ k → (_ , k) ∈ J′) (take2-lands ld n) m

          feeds′ : ∀ {Δ A B S c b kb k x q ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                 → (ψ′ : Path t′ (connectˢ S c b kb k (feeding x q ss) rp e rt s bd)) → (q , feedC ψ′) ∈ J′
          feeds′ ψ′ with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-feed ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with stack-mem sk a (Owned.feeds ow ψ₀)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (feed-lands ld n) m
          feeds′ ψ′ | inj₂ (_ , ψ₀ , same-connect , _ , _ , _ , ld) with stack-mem sk a (Owned.feeds ow ψ₀)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (feed-lands ld n) m

          fins′ : ∀ {Δ A B S c b kb k q ss e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                → (ψ′ : Path t′ (connectˢ S c b kb k (finishing q ss) rp e rt s bd)) → (q , finC ψ′) ∈ J′
          fins′ ψ′ with keep H π₀ v eq ψ′
          ... | inj₁ (ρ , _) = ⊥-elim (no-fin ρ)
          ... | inj₂ (_ , ψ₀ , same , _ , _ , _ , ld) with stack-mem sk a (Owned.fins ow ψ₀)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (fin-lands ld n) m
          fins′ ψ′ | inj₂ (_ , ψ₀ , same-connect , _ , _ , _ , ld) with stack-mem sk a (Owned.fins ow ψ₀)
          ...   | n , m = subst (λ k → (_ , k) ∈ J′) (fin-lands ld n) m

          bodies′ : ∀ {Δ A B S c b kb k fd e rp rt q} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                  → (ψ′ : Path t′ (connectˢ S c b kb k fd rp e rt s bd)) → (q , bodyC ψ′) ∈ J′ → At.part H bd ≡ nothing
          bodies′ ψ′ m with stack-back sk a m
          ... | j , mj , n , e = subst BodyOk (sym (cong proj₂ e)) (body-call (proj₂ j) n (body-ok ow j mj))

          placed′ : All (Placed t′) J′
          placed′ = tabulateᴬ λ {j′} m → go (stack-back sk a m)
            where go : ∀ {j′} → (Σ (Job t) λ j → j ∈ stackJobs t sk × Σ (¬ SrcOf t π₀ (proj₂ j)) λ n → j′ ≡ (proj₁ j , proj₁ (rcall (proj₂ j) n))) → Placed t′ j′
                  go (j , mj , n , e) = subst (Placed t′) (sym e) (placed-call (proj₂ j) n (lookupᴬ (Owned.placed ow) mj))

  ------------------------------------------------------------------------
  -- A map restaged: its source pending beneath it

  -- A source wrapped one step by a node that is no connect, or a
  -- connect's body.
  data Wrap {h} : ∀ {Δ A} {s : T.Obs Timeline Δ A} {q} {Δ′ B} {u : Sub h Δ′ B} → Path u (pendingˢ s q) → Set₁ where
    wrap-map  : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {f : A → B} → Wrap (in-map {f = f} {t = pendingˢ s q} here)
    wrap-scan : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {f : B → A → B} {r} → Wrap (in-scan {f = f} {r} {t = pendingˢ s q} here)
    wrap-take : ∀ {Δ A} {s : T.Obs Timeline Δ A} {q} {i p c k tk} → Wrap (in-take {i = i} {p} {c} {k} {tk} {t = pendingˢ s q} here)
    wrap-outer : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {op} {f : A → T.Obs Timeline Δ B} {fl oc k r pl} {ls : List (Lane h Δ B)}
               → Wrap (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = pendingˢ s q} {ls} here)
    wrap-body : ∀ {Δ A B} {s : T.Obs Timeline (A ∷ Δ) B} {q} {S c b kb k fd e rp rt} {src : Sub h Δ A}
              → Wrap (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd = pendingˢ s q} here)

  wrap-here : ∀ {h Δ A Δ₁ B C} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι
            → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A ∷ Δ) C} (β : Path u (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd)) → ι ≢ β ⊕ in-source here
  wrap-here wrap-map  (in-map ())
  wrap-here wrap-scan (in-scan ())
  wrap-here wrap-take (in-take ())
  wrap-here wrap-outer (in-outer ())
  wrap-here wrap-outer (in-lanes _) ()
  wrap-here wrap-body (in-source _) ()
  wrap-here wrap-body (in-body ())

  wrap-src : ∀ {h Δ A Δ₁ B} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι → Path (pendingˢ s q) u → ⊥
  wrap-src wrap-map  ()
  wrap-src wrap-scan ()
  wrap-src wrap-take ()
  wrap-src wrap-outer ()
  wrap-src wrap-body ()

  -- A path ending under a wrapped source ends under no connect's source.
  mutual
    not-src : ∀ {h Δ A Δ₀ A₀ Δ₁ B₀ C₀} {t : Sub h Δ A} {s : T.Obs Timeline Δ₀ A₀} {q} {u : Sub h Δ₁ B₀} {ι : Path u (pendingˢ s q)} → Wrap ι
            → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
              (α : Path t u) (β : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
            → α ⊕ ι ≢ β ⊕ in-source here
    not-src w here         β             eq = wrap-here w β eq
    not-src w (in-map α)   (in-map β)    eq = not-src w α β (in-map-inj eq)
      where in-map-inj : ∀ {x y} → in-map x ≡ in-map y → x ≡ y
            in-map-inj refl = refl
    not-src w (in-scan α)  (in-scan β)   eq = not-src w α β (in-scan-inj eq)
      where in-scan-inj : ∀ {x y} → in-scan x ≡ in-scan y → x ≡ y
            in-scan-inj refl = refl
    not-src w (in-take α)  (in-take β)   eq = not-src w α β (in-take-inj eq)
      where in-take-inj : ∀ {x y} → in-take x ≡ in-take y → x ≡ y
            in-take-inj refl = refl
    not-src w (in-outer α) (in-outer β)  eq = not-src w α β (in-outer-inj eq)
      where in-outer-inj : ∀ {x y} → in-outer x ≡ in-outer y → x ≡ y
            in-outer-inj refl = refl
    not-src w (in-outer α) (in-lanes β)  ()
    not-src w (in-lanes α) (in-outer β)  ()
    not-src w (in-lanes α) (in-lanes β)  eq = not-srcᴸ w α β (in-lanes-inj eq)
      where in-lanes-inj : ∀ {x y} → in-lanes x ≡ in-lanes y → x ≡ y
            in-lanes-inj refl = refl
    not-src w (in-source α) here         _  = wrap-src w α
    not-src w (in-source α) (in-source β) eq = not-src w α β (in-source-inj eq)
      where in-source-inj : ∀ {x y} → in-source x ≡ in-source y → x ≡ y
            in-source-inj refl = refl
    not-src w (in-source α) (in-body β)  ()
    not-src w (in-body α)  here          ()
    not-src w (in-body α)  (in-source β) ()
    not-src w (in-body α)  (in-body β)   eq = not-src w α β (in-body-inj eq)
      where in-body-inj : ∀ {x y} → in-body x ≡ in-body y → x ≡ y
            in-body-inj refl = refl
    not-src w (in-defer α) (in-defer β)  eq = not-src w α β (in-defer-inj eq)
      where in-defer-inj : ∀ {x y} → in-defer x ≡ in-defer y → x ≡ y
            in-defer-inj refl = refl

    not-srcᴸ : ∀ {h Δ B Δ₀ A₀ Δ₁ B₀ C₀} {ls : List (Lane h Δ B)} {s : T.Obs Timeline Δ₀ A₀} {q} {u : Sub h Δ₁ B₀} {ι : Path u (pendingˢ s q)} → Wrap ι
             → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
               (α : PathLanes ls u) (β : PathLanes ls (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
             → α ⊕ᴸ ι ≢ β ⊕ᴸ in-source here
    not-srcᴸ w (this-lane α) (this-lane β) eq = not-src w α β (this-inj eq)
      where this-inj : ∀ {x y} → this-lane x ≡ this-lane y → x ≡ y
            this-inj refl = refl
    not-srcᴸ w (this-lane α) (next-lane β) ()
    not-srcᴸ w (next-lane α) (this-lane β) ()
    not-srcᴸ w (next-lane α) (next-lane β) eq = not-srcᴸ w α β (next-inj eq)
      where next-inj : ∀ {x y} → next-lane x ≡ next-lane y → x ≡ y
            next-inj refl = refl

  module Mapped {h} {T₀ : Sub h [] R} {Δ A B} {f : A → B} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.map f s) q)) where
    v : Sub h Δ B
    v = mapˢ f (pendingˢ s q)

    open Moved π v using (t′; restack; Alone)

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π v ⊕ in-map here

    walk′ : walk π′ top ≡ walk (in-map {f = f} {t = pendingˢ s q} here) (walk π top)
    walk′ = trans (walk-⊕ (planted π v) (in-map here) top) (cong (λ W → walk (in-map {f = f} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π v top))

    -- The source compiles as the map did, under the map's observer.
    code′ : ∀ {act} → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π top)
                         × act ≗ compile (T.map f s) E′ υ (Here.obs (walk π top)) (Here.kont (walk π top)))
          → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E′ υ (Here.obs (walk π′ top)) (Here.kont (walk π′ top)))
    code′ {act} (u , E′ , υ , e , c) =
      u , E′ , υ , subst (λ W → wkEnv υ E′ ≡ Here.env W) (sym walk′) e , subst (λ W → act ≗ compile s E′ υ (Here.obs W) (Here.kont W)) (sym walk′) c

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-map (planted π v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    part′ : ∀ (H : Heapᴹ h) → At.part H t′ ≡ At.part H T₀
    part′ H = part-plant H π v refl

    names′ : names t′ ≡ names T₀
    names′ = names-plant π v refl

    less : pend t′ < pend T₀
    less = pend-less π v ≤-refl

    -- A map over a pending source holds nothing a call is owed at, and
    -- one pending node: its source.
    inner : Moved.Inner π v (in-map here)
    inner = record { no-of = λ { (in-map ()) } ; no-cold = λ { (in-map ()) } ; one-pend = λ { (in-map here) → refl }
                   ; no-end = λ { (in-map ()) } ; no-cut = λ { (in-map ()) } ; no-feed = λ { (in-map ()) } ; no-fin = λ { (in-map ()) }
                   ; not-self = λ _ () }

    -- What the relation reads of a pending map it reads alike of the
    -- map over its pending source.
    rm-owned   : ∀ {w bs act} {σ : w ⊑ h} {K} {cd cd′} (H : Heapᴹ h) (sk : StackAs T₀ q σ K bs) (a : Alone sk) {a′}
               → Owned H T₀ (subAs {act = act} π cd sk a) → Owned H t′ (subAs {act = act} π′ cd′ (restack sk a) a′)
    rm-owned H sk a ow = Moved.Owning.reowned π v H refl (in-map here) inner sk a ow

    -- The map's heads are its source's.
    rm-behind : ∀ (H : Heapᴹ h) {p} → Each H (Heads p) T₀ → Each H (Heads p) t′
    rm-behind H {p} = each-plant H π v refl tr
      where
        unmap : ∀ {c : U.Node Δ A} → Heads p (U.mapᶜ f c) → Heads p c
        unmap {c} hd e = hd (trans (head-map f (U.step c)) e)

        pa : ∀ {Δ′ A′} {w : Sub h Δ′ A′} → Each H (Heads p) (pendingˢ (T.map f s) q) → (ψ : Path v w) → seen H ψ ≡ true
           → ∀ {c} → At.part H w ≡ just c → Heads p c
        pa eu here           _ pw   = Each.parts eu here refl pw
        pa eu (in-map here)  _ refl = unmap {U.subscribe s q} (Each.parts eu here refl refl)

        tr : Each H (Heads p) (pendingˢ (T.map f s) q) → Each H (Heads p) v
        tr eu = record { parts = pa eu ; pools = λ { (in-map ()) } ; rests = λ { (in-map ()) } }

    -- A map runs what its source runs, and its source what it was
    -- pending to.
    rm-lingers : ∀ (H : Heapᴹ h) → Lingers H T₀ → Lingers H t′
    rm-lingers H = lingers-plant H π v refl (λ {C} → rest-pinned (U.restᶜ {B = C} (U.subscribe s q))) (record { pools = λ { (in-map ()) } ; rests = λ { (in-map ()) } })

    -- A pending node and a map over one register nothing, queue nothing
    -- and are owed nothing.
    rm-kernels : (H : Heapᴹ h) → Kernels H T₀ → Kernels H t′
    rm-kernels H kn = record { holds = holds-plant H π v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H π v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant π v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

    rm-meaning : (H : Heapᴹ h) → Meaning H T₀ → Meaning H t′
    rm-meaning H mn = record { fed = fed-plant H π v (λ _ fd → fd) _ (Meaning.fed mn) }

    pendings′ : pendings t′ ≡ pendings T₀
    pendings′ with pendings-plant π v
    ... | _ , _ , e , e′ = trans e′ (sym e)

    rm-queue : ∀ (H : Heapᴹ h) {p clk ts} → Queue H p clk ts T₀ → Queue H p clk ts t′
    rm-queue H {ts = ts} qu =
      record { timed   = subst (At.Timed H ts) (sym pendings′) (Queue.timed qu)
             ; joined  = subst₂ (At.Joined H) (sym (subjects-plant π v refl)) (sym (joiners-plant π v (λ _ → refl) [])) (Queue.joined qu)
             ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- A map begun runs nothing of its own: its source begins under the
  -- map's observer, one subscription fewer owed.
  map-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {f : A → B} {s : T.Obs Timeline Δ A} → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.map f s)
              → Σ (Carried g m) λ cr′ → subOf (Carried.ctlAs cr′) ≡ just (Δ , A , s) × measure (carried cr′) ≺ measure (carried cr)
  map-restage {m = mach ⟨ H , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs π cd sk a } refl =
    record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = N.t′ ; ctlAs = subAs M.π′ (M.code′ cd) (N.restack sk a) (M.alones _)
           ; meets = trans (M.part′ H) (Carried.meets cr) ; owned = M.rm-owned H sk a (Carried.owned cr)
           ; kernels = M.rm-kernels H (Carried.kernels cr) ; meaning = M.rm-meaning H (Carried.meaning cr) ; queue = M.rm-queue H (Carried.queue cr)
           ; books = record { fresh = subst (AllPairs _≢_) (sym M.names′) (Books.fresh bk)
                            ; clocked = proj₁ (Books.clocked bk) , N.reticked sk a (proj₂ (Books.clocked bk))
                            ; paidUp = Books.paidUp bk ; running = Books.running bk }
           ; sorted = Carried.sorted cr ; behind = M.rm-behind H (Carried.behind cr) ; lingers = M.rm-lingers H (Carried.lingers cr) }
    , refl , inj₁ (inj₁ M.less)
    where module M = Mapped π
          module N = Moved π M.v
          bk = Carried.books cr

  -- WHAT AN `of` RUNS: its values, then its continuation.
  Offering : ∀ {Δ A} → T.Obs Timeline Δ A → List A → Set₁
  Offering {Δ} {A} s xs = ∀ {w u} (E′ : Env Δ u) (υ : u ⊑ w) (W : Here w Δ A)
                        → compile s E′ υ (Here.obs W) (Here.kont W) ≗ (emitAll (Here.obs W) 0 xs >>ᴬ (Here.kont W same⊑ (unsubscribing skipᴬ) >>ᴬ done tt))

  -- AN `of` BEGUN: planted where it was pending, its values and then its
  -- continuation the agenda's calls, one subscription fewer owed.  An
  -- `empty` begins as a spent one.
  module Offered {h} {T₀ : Sub h [] R} {Δ A} {s : T.Obs Timeline Δ A} {xs : List A} {q} (π : Path T₀ (pendingˢ s q))
                 (sp : U.subscribe s q ≡ U.ofᶜ q 0 xs) (cs : Offering s xs) where
    v : Sub h Δ A
    v = ofˢ q 0 xs

    open Moved π v using (t′; restack; Alone; reticked)

    π′ : Path t′ v
    π′ = planted π v

    ks : List (Call t′)
    ks = emitC π′ ∷ kontC of-leaf π′ ∷ []

    -- The `of`'s code its values then its continuation, the two calls.
    code′ : ∀ {act} → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π top)
                         × act ≗ compile s E′ υ (Here.obs (walk π top)) (Here.kont (walk π top)))
          → act ≗ ⟦ ks ⟧ᶜ
    code′ (_ , E′ , υ , _ , c) =
      ≗-trans c (subst (λ W → _ ≗ (emitAll (Here.obs W) 0 xs >>ᴬ (Here.kont W same⊑ (unsubscribing skipᴬ) >>ᴬ done tt)))
                       (sym (walk-planted π v top)) (cs E′ υ (walk π top)))

    eqp : ∀ (H : Heapᴹ h) → At.part H (pendingˢ s q) ≡ At.part H v
    eqp H = cong just sp

    less : pend t′ < pend T₀
    less = pend-less π v (syn-pos s)

    postulate
      of-owned : ∀ {w bs act} {σ : w ⊑ h} {K} {cd} (H : Heapᴹ h) (sk : StackAs T₀ q σ K bs) (a : Alone sk) (e : act ≗ ⟦ ks ⟧ᶜ)
               → Owned H T₀ (subAs {act = act} π cd sk a) → Owned H t′ (runAs ks e (restack sk a))

    -- An `of` registers nothing, queues nothing and is owed nothing.
    of-kernels : (H : Heapᴹ h) → Kernels H T₀ → Kernels H t′
    of-kernels H kn = record { holds = holds-plant H π v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H π v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant π v (λ ()) (λ st → st) (Kernels.settled kn) }

    of-meaning : (H : Heapᴹ h) → Meaning H T₀ → Meaning H t′
    of-meaning H mn = record { fed = fed-plant H π v (λ _ fd → fd) _ (Meaning.fed mn) }

    pendings′ : pendings t′ ≡ pendings T₀
    pendings′ with pendings-plant π v
    ... | _ , _ , e , e′ = trans e′ (sym e)

    of-queue : ∀ (H : Heapᴹ h) {p clk ts} → Queue H p clk ts T₀ → Queue H p clk ts t′
    of-queue H {ts = ts} qu =
      record { timed   = subst (At.Timed H ts) (sym pendings′) (Queue.timed qu)
             ; joined  = subst₂ (At.Joined H) (sym (subjects-plant π v refl)) (sym (joiners-plant π v (λ _ → refl) [])) (Queue.joined qu)
             ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

    -- The `of`'s heads are the subscription's.
    of-behind : ∀ (H : Heapᴹ h) {p} → Each H (Heads p) T₀ → Each H (Heads p) t′
    of-behind H {p} = each-plant H π v (eqp H) tr
      where
        tr : Each H (Heads p) (pendingˢ s q) → Each H (Heads p) v
        tr eu = record { parts = λ { here _ pw → Each.parts eu here refl (trans (eqp H) pw) } ; pools = λ () ; rests = λ () }

    -- An `of` runs nothing past its end, nor did it pending.
    of-lingers : ∀ (H : Heapᴹ h) → Lingers H T₀ → Lingers H t′
    of-lingers H = lingers-plant H π v (eqp H) (subst (λ c → Pinned (U.restˢ {B = ⊤} c) U.hushˢ) (sym sp) unpinned) (record { pools = λ () ; rests = λ () })

  -- The configuration an `of` planted makes: its first call its values.
  Offers : ∀ {g m} → Carried g m → ∀ {Δ A} → List A → Set₁
  Offers {g} {m} cr {Δ} {A} xs = Σ (Carried g m) λ cr′ → Σ Pos λ p → Σ (Path (Carried.tree cr′) (ofˢ {Δ = Δ} {A} p 0 xs)) λ π′
                                 → firstCall (Carried.ctlAs cr′) ≡ just (emitC π′) × measure (carried cr′) ≺ measure (carried cr)

  offer-restage : ∀ {g m} (cr : Carried g m) {Δ A} {s : T.Obs Timeline Δ A} {xs : List A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , s)
                → (∀ q → U.subscribe s q ≡ U.ofᶜ q 0 xs) → Offering s xs → Offers cr {Δ} {A} xs
  offer-restage {m = mach ⟨ H , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs {q = q} π cd sk a } refl sp cs =
    record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = N.t′ ; ctlAs = runAs O.ks (O.code′ cd) (N.restack sk a)
           ; meets = trans (part-plant H π O.v (O.eqp H)) (Carried.meets cr) ; owned = O.of-owned H sk a (O.code′ cd) (Carried.owned cr)
           ; kernels = O.of-kernels H (Carried.kernels cr) ; meaning = O.of-meaning H (Carried.meaning cr) ; queue = O.of-queue H (Carried.queue cr)
           ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant π O.v refl)) (Books.fresh bk)
                            ; clocked = proj₁ (Books.clocked bk) , N.reticked sk a (proj₂ (Books.clocked bk))
                            ; paidUp = Books.paidUp bk ; running = Books.running bk }
           ; sorted = Carried.sorted cr ; behind = O.of-behind H (Carried.behind cr) ; lingers = O.of-lingers H (Carried.lingers cr) }
    , q , O.π′ , refl , inj₁ (inj₁ O.less)
    where module O = Offered π (sp q) cs
          module N = Moved π O.v
          bk = Carried.books cr

  of-restage : ∀ {g m} (cr : Carried g m) {Δ A} {xs : List A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.of xs) → Offers cr {Δ} {A} xs
  of-restage cr {xs = xs} e = offer-restage cr e (λ _ → refl) (λ _ _ W → bind≗ (≗-refl (emitAll (Here.obs W) 0 xs)) λ _ → seq-done _)

  empty-restage : ∀ {g m} (cr : Carried g m) {Δ A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.empty) → Offers cr {Δ} {A} []
  empty-restage cr e = offer-restage cr e (λ _ → refl) (λ _ _ _ → under≗ (≗-refl _) (seq-done _))

  -- A KERNEL BEGUN BY ALLOCATING: its cells allocated, its node planted
  -- in the grown world, the run at the subscription the kernel begins
  -- next, carried, one subscription fewer owed.
  Restages : ∀ {g m} → Carried g m → ∀ {Δ A} → T.Obs Timeline Δ A → Set₁
  Restages {g} {m} cr {Δ} {A} s = ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₀ → m′ ⇝ m₀ × Σ (Carried g m₀) λ cr′
                                  → subOf (Carried.ctlAs cr′) ≡ just (Δ , A , s) × measure (carried cr′) ≺ measure (carried cr)


  -- A WORLD GROWN BY ALLOCATION: every name the old heap held reads as it
  -- did, weakened.
  record Grows {h v} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) : Set₁ where
    field
      cells   : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
      slots   : ∀ {X} (s : Sink h X) → CbRel (cbs H′ (wk∋ τ s)) (wkVal (slot X) τ (cbs H s))
      stashes : ∀ (u : Quiet h) → look H′ (wk∋ τ u) ≗ wkAct τ (look H u)
      handles : ∀ (hd : Handle h) → At.spentʰ H′ (wk∋ τ hd) ≡ At.spentʰ H hd

  -- Two observers, part for part; two continuations, pointwise.
  ObsRel : ∀ {A w} → Observer A w → Observer A w → Set₁
  ObsRel o o′ = (∀ a → Observer.next o a ≗ Observer.next o′ a) × Observer.complete o ≗ Observer.complete o′ × Observer.closed o ≗ Observer.closed o′

  KontRel : ∀ {w} → Kont w → Kont w → Set₁
  KontRel {w} k k′ = ∀ {v} (σ : w ⊑ v) sub → k σ sub ≗ k′ σ sub

  -- A tree weakened owes what it did.
  mutual
    pend-grow : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → pend (wkTree τ t) ≡ pend t
    pend-grow τ (pendingˢ s q)                       = refl
    pend-grow τ (coldˢ s hd ph)                      = refl
    pend-grow τ (ofˢ p i xs)                         = refl
    pend-grow τ doneˢ                                = refl
    pend-grow τ (mapˢ f t)                           = pend-grow τ t
    pend-grow τ (scanˢ f r t)                        = pend-grow τ t
    pend-grow τ (takeWhileˢ i p c k tk t)            = pend-grow τ t
    pend-grow τ (flatMapˢ op f fl oc k r pl t ls)    = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)
    pend-grow τ (connectˢ S c b kb k fd q e rt s bd) = cong₂ _+_ (pend-grow τ s) (pend-grow τ bd)
    pend-grow τ (joinˢ j s fl x m)                   = refl
    pend-grow τ (deferˢ k t)                         = pend-grow τ t

    pend-growᴸ : ∀ {h v Δ B} (τ : h ⊑ v) (ls : List (Lane h Δ B)) → pendᴸ (wkLanes τ ls) ≡ pendᴸ ls
    pend-growᴸ τ []                 = refl
    pend-growᴸ τ (lane c k t ∷ ls) = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)

  module Grown {h v} (τ : h ⊑ v) where
    postulate
      -- The stack, its calls aimed along the weakened tree.
      grow-stack  : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} → StackAs t p σ K bs
                  → StackAs (wkTree τ t) p (σ ⨾ τ) K (mapList (mapMaybe (wkPlaying τ)) bs)
      grow-alone  : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) (sk : StackAs t p σ K bs)
                  → All (λ j → ¬ SrcOf t π (proj₂ j)) (stackJobs t sk) → All (λ j → ¬ SrcOf (wkTree τ t) (wkPath τ π) (proj₂ j)) (stackJobs (wkTree τ t) (grow-stack sk))
      grow-ticked : ∀ {t : Sub h [] R} {n p w} {σ : w ⊑ h} {K bs} (sk : StackAs t p σ K bs) → Ticked t n sk → Ticked (wkTree τ t) n (grow-stack sk)
      -- A walk along the weakened path hands the weakened observer and
      -- continuation, up to `_≗_`, and the weakened subjects.
      walk-grow   : ∀ {Δ A} {t : Sub h [] R} {u : Sub h Δ A} (π : Path t u)
                  → ObsRel (wkObs τ (Here.obs (walk π top))) (Here.obs (walk (wkPath τ π) top))
                  × KontRel (wkKont τ (Here.kont (walk π top))) (Here.kont (walk (wkPath τ π) top))
                  × wkEnv τ (Here.env (walk π top)) ≡ Here.env (walk (wkPath τ π) top)

    env-grow : ∀ {t : Sub h [] R} {Δ A} {u′ : Sub h Δ A} (π : Path t u′) {u} (E′ : Env Δ u) (υ : u ⊑ h)
             → wkEnv υ E′ ≡ Here.env (walk π top) → wkEnv (υ ⨾ τ) E′ ≡ Here.env (walk (wkPath τ π) top)
    env-grow π E′ υ e = trans (sym (wkEnv-wk υ τ E′)) (trans (cong (wkEnv τ) e) (proj₂ (proj₂ (walk-grow π))))

    -- A subscription still pending, along the weakened path.
    code-grow : ∀ {t : Sub h [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} (π : Path t (pendingˢ s q)) {u} (E′ : Env Δ u) (υ : u ⊑ h)
              → wkEnv υ E′ ≡ Here.env (walk π top)
              → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ v) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk (wkPath τ π) top)
                  × compile s E′ (υ ⨾ τ) (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
                    ≗ compile s E″ υ′ (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
    code-grow π {u} E′ υ e = u , E′ , υ ⨾ τ , env-grow π E′ υ e , ≗-refl _

    -- A node of the grown tree held where it is a flatMap, or a
    -- connect: the weakening of one, which the old tree held.
    data FlatBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      flat-back : ∀ {A′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                → FlatBack (wkTree τ (flatMapˢ op f fl oc k r pl so ls)) (flatMapˢ op f fl oc k r pl so ls)

    data ConnBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      conn-back : ∀ {A′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                → ConnBack (wkTree τ (connectˢ S c b kb k fd rp e rt src bd)) (connectˢ S c b kb k fd rp e rt src bd)

    flat-inv : ∀ {Δ′ A′ B′} {op f fl′ oc′ k′ r′ pl} {so′ : Sub v Δ′ A′} {ls′ : List (Lane v Δ′ B′)} (x : Sub h Δ′ B′)
             → flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′ ≡ wkTree τ x → FlatBack (flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′) x
    flat-inv (flatMapˢ op f fl oc k r pl so ls)     refl = flat-back
    flat-inv (pendingˢ s q)                         ()
    flat-inv (coldˢ s hd ph)                        ()
    flat-inv (ofˢ p i xs)                           ()
    flat-inv doneˢ                                  ()
    flat-inv (mapˢ f s)                             ()
    flat-inv (scanˢ f r s)                          ()
    flat-inv (takeWhileˢ i p c k tk s)              ()
    flat-inv (connectˢ S c b kb k fd rp e rt src bd) ()
    flat-inv (joinˢ j sk l x st)                    ()
    flat-inv (deferˢ k s)                           ()

    conn-inv : ∀ {Δ′ A′ B′} {S′ c′ b′ kb′ k′ fd′ rp e rt} {src′ : Sub v Δ′ A′} {bd′ : Sub v (A′ ∷ Δ′) B′} (x : Sub h Δ′ B′)
             → connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′ ≡ wkTree τ x → ConnBack (connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′) x
    conn-inv (connectˢ S c b kb k fd rp e rt src bd) refl = conn-back
    conn-inv (pendingˢ s q)                         ()
    conn-inv (coldˢ s hd ph)                        ()
    conn-inv (ofˢ p i xs)                           ()
    conn-inv doneˢ                                  ()
    conn-inv (mapˢ f s)                             ()
    conn-inv (scanˢ f r s)                          ()
    conn-inv (takeWhileˢ i p c k tk s)              ()
    conn-inv (flatMapˢ op f fl oc k r pl so ls)     ()
    conn-inv (joinˢ j sk l x st)                    ()
    conn-inv (deferˢ k s)                           ()

    -- What a weakened tree owes, and what it has begun.
    owes-wk : ∀ {Δ A} (u : Sub h Δ A) → Owes (wkTree τ u) → Owes u
    owes-wk (pendingˢ s q)                          o = o
    owes-wk (mapˢ f s)                              o = owes-wk s o
    owes-wk (scanˢ f r s)                           o = owes-wk s o
    owes-wk (connectˢ S c b kb k fd rp e rt src bd) o = owes-wk src o
    owes-wk (coldˢ s hd ph)                         ()
    owes-wk (ofˢ p i xs)                            ()
    owes-wk doneˢ                                   ()
    owes-wk (takeWhileˢ i p c k tk s)               ()
    owes-wk (flatMapˢ op f fl oc k r pl so ls)      ()
    owes-wk (joinˢ j sk l x st)                     ()
    owes-wk (deferˢ k s)                            ()

    begun-wk : ∀ {Δ A} (k : Maybe (Quiet h)) (u : Sub h Δ A) → Begun k u → Begun (mapMaybe (wk∋ τ) k) (wkTree τ u)
    begun-wk nothing  u _ = tt
    begun-wk (just _) u b = λ o → b (owes-wk u o)

    mutual
      settled-wk : ∀ {Δ A} (u : Sub h Δ A) → Settled u → Settled (wkTree τ u)
      settled-wk (pendingˢ s q)                          _                 = tt
      settled-wk (coldˢ s hd ph)                         _                 = tt
      settled-wk (ofˢ p i xs)                            _                 = tt
      settled-wk doneˢ                                   _                 = tt
      settled-wk (mapˢ f s)                              x                 = settled-wk s x
      settled-wk (scanˢ f r s)                           x                 = settled-wk s x
      settled-wk (takeWhileˢ i p c k tk s)               (b , x)           = begun-wk k s b , settled-wk s x
      settled-wk (flatMapˢ op f fl oc k r pl so ls)      (b , x , y)       = begun-wk k so b , settled-wk so x , settled-wkᴸ ls y
      settled-wk (connectˢ S c b kb k fd rp e rt src bd) (b₁ , b₂ , x , y) = begun-wk k src b₁ , begun-wk kb bd b₂ , settled-wk src x , settled-wk bd y
      settled-wk (joinˢ j sk l x st)                     _                 = tt
      settled-wk (deferˢ k s)                            (b , x)           = begun-wk k s b , settled-wk s x

      settled-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → SettledLanes ls → SettledLanes (wkLanes τ ls)
      settled-wkᴸ []                _           = tt
      settled-wkᴸ (lane c k s ∷ ls) (b , x , y) = begun-wk k s b , settled-wk s x , settled-wkᴸ ls y

    -- The pending frames' timers, weakened.
    timerOf-wk : ∀ {A} (s : Sink h A) (hd : Handle h) (ph : Phase A) → timerOf (wk∋ τ s) (wk∋ τ hd) ph ≡ mapList (wkTimer τ) (timerOf s hd ph)
    timerOf-wk s hd (waiting τ′ e (at t le b)) = refl
    timerOf-wk s hd (waiting τ′ e doneᶠᵐ)      = refl
    timerOf-wk s hd (waiting τ′ e quietᶠᵐ)     = refl
    timerOf-wk s hd (fired _ _ _)              = refl
    timerOf-wk s hd (playing _ _ _ _)          = refl

    mapL-++ : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) (xs ys : List X) → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
    mapL-++ f []       ys = refl
    mapL-++ f (x ∷ xs) ys = cong (f x ∷_) (mapL-++ f xs ys)

    ∈-mapL : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) {x xs} → x ∈ xs → f x ∈ mapList f xs
    ∈-mapL f (hereᴬ refl) = hereᴬ refl
    ∈-mapL f (thereᴬ m)   = thereᴬ (∈-mapL f m)

    all-mapL : ∀ {a b p q} {X : Set a} {Y : Set b} {P : X → Set p} {Q : Y → Set q} (f : X → Y) → (∀ {x} → P x → Q (f x))
             → ∀ {xs} → All P xs → All Q (mapList f xs)
    all-mapL f g []         = []
    all-mapL f g (px ∷ pxs) = g px ∷ all-mapL f g pxs

    linked-mapL : ∀ {ts : List (Timer h)} → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) ts
                → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (mapList (wkTimer τ) ts)
    linked-mapL []      = []
    linked-mapL [-]     = [-]
    linked-mapL (r ∷ l) = r ∷ linked-mapL l

    mutual
      pendings-wk : ∀ {Δ A} (u : Sub h Δ A) → pendings (wkTree τ u) ≡ mapList (wkTimer τ) (pendings u)
      pendings-wk (pendingˢ s q)                          = refl
      pendings-wk (coldˢ s hd ph)                         = timerOf-wk s hd ph
      pendings-wk (ofˢ p i xs)                            = refl
      pendings-wk doneˢ                                   = refl
      pendings-wk (mapˢ f s)                              = pendings-wk s
      pendings-wk (scanˢ f r s)                           = pendings-wk s
      pendings-wk (takeWhileˢ i p c k tk s)               = pendings-wk s
      pendings-wk (flatMapˢ op f fl oc k r pl so ls)      =
        trans (cong₂ _++_ (pendings-wk so) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings so) (lanePendings ls)))
      pendings-wk (connectˢ S c b kb k fd rp e rt src bd) =
        trans (cong₂ _++_ (pendings-wk src) (pendings-wk bd)) (sym (mapL-++ (wkTimer τ) (pendings src) (pendings bd)))
      pendings-wk (joinˢ j sk l x st)                     = refl
      pendings-wk (deferˢ k s)                            = pendings-wk s

      pendings-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → lanePendings (wkLanes τ ls) ≡ mapList (wkTimer τ) (lanePendings ls)
      pendings-wkᴸ []                = refl
      pendings-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ _++_ (pendings-wk s) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings s) (lanePendings ls)))

    module _ {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
      private
        cells : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
        cells = Grows.cells gr

        -- The heap-free combinators read alike from either heap.
        mapᴹ-≡ : ∀ {X Y : Set₁} (f : X → Y) m → At.mapᴹ H′ f m ≡ At.mapᴹ H f m
        mapᴹ-≡ f nothing  = refl
        mapᴹ-≡ f (just _) = refl

        consᴹ-≡ : ∀ {X : Set₁} (m : Maybe X) xs → At.consᴹ H′ m xs ≡ At.consᴹ H m xs
        consᴹ-≡ nothing  xs = refl
        consᴹ-≡ (just _) xs = refl

        merged-≡ : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl → At.merged H′ op g o L Q pl ≡ At.merged H op g o L Q pl
        merged-≡ op g nothing  []      []      pl = refl
        merged-≡ op g nothing  []      (_ ∷ _) pl = refl
        merged-≡ op g nothing  (_ ∷ _) Q       pl = refl
        merged-≡ op g (just _) L       Q       pl = refl

        connected-≡ : ∀ {Δ A B} r (e : Maybe Pos) (t : U.Node Δ A) s (mb : Maybe (U.Node (A ∷ Δ) B))
                    → At.connected H′ r e t s mb ≡ At.connected H r e t s mb
        connected-≡ r e        t s        nothing  = refl
        connected-≡ r e        t (just _) (just _) = refl
        connected-≡ r (just _) t nothing  (just _) = refl
        connected-≡ r nothing  t nothing  (just _) = refl

        joinedᶜ-≡ : ∀ {Δ A} (x : A ∈ Δ) j st → At.joinedᶜ H′ x j st ≡ At.joinedᶜ H x j st
        joinedᶜ-≡ x j nothing  = refl
        joinedᶜ-≡ x j (just _) = refl

        taking?-≡ : ∀ {Δ A} i p tk (s : Maybe (U.Node Δ A)) → At.taking? H′ i p tk s ≡ At.taking? H i p tk s
        taking?-≡ i p taking       s = mapᴹ-≡ (U.takeWhileᶜ i p) s
        taking?-≡ i p (ending k c) s = refl
        taking?-≡ i p taken        s = refl

        sourced-≡ : ∀ {Δ A} (s : Maybe (U.Node Δ A)) t → At.sourced H′ s t ≡ At.sourced H s t
        sourced-≡ (just _) t = refl
        sourced-≡ nothing  t = refl

      -- The open part, read through the weakening.
      mutual
        grow-part : ∀ {Δ A} (u : Sub h Δ A) → At.part H′ (wkTree τ u) ≡ At.part H u
        grow-part (pendingˢ s q)                 = refl
        grow-part (coldˢ s hd ph)                = cong (λ b → if b then nothing else _) (Grows.handles gr hd)
        grow-part (ofˢ p i xs)                   = refl
        grow-part doneˢ                          = refl
        grow-part (mapˢ f s)                     = trans (cong (At.mapᴹ H′ (U.mapᶜ f)) (grow-part s)) (mapᴹ-≡ (U.mapᶜ f) (At.part H s))
        grow-part (scanˢ f r s)                  =
          trans (cong₂ (λ a m → At.mapᴹ H′ (U.scanᶜ f a) m) (cells r) (grow-part s)) (mapᴹ-≡ (U.scanᶜ f (At.val H r)) (At.part H s))
        grow-part (takeWhileˢ i p c k tk s)      =
          trans (cong₂ (λ b m → if b then At.taking? H′ i p tk m else nothing) (cells (Kit.live c)) (grow-part s))
                (cong (λ m → if At.val H (Kit.live c) then m else nothing) (taking?-≡ i p tk (At.part H s)))
        grow-part (flatMapˢ op f fl oc k r pl so ls) =
          trans (cong₂ (λ o L → At.merged H′ op (λ a q → U.subscribe (f a) q) o L (At.val H′ (wkR τ (FlatKit.Flat.queue fl))) pl) (grow-part so) (grow-partᴸ ls))
                (trans (cong (λ Q → At.merged H′ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) Q pl) (cells (FlatKit.Flat.queue fl)))
                       (merged-≡ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl))
        grow-part (connectˢ S c b kb k fd rp e rt src bd) =
          trans (cong₂ (At.connected H′ rp e rt) (grow-part src) (grow-part bd)) (connected-≡ rp e rt (At.part H src) (At.part H bd))
        grow-part (joinˢ j sk l x st)            =
          trans (cong (λ b → if b then At.joinedᶜ H′ x j st else nothing) (cells l)) (cong (λ m → if At.val H l then m else nothing) (joinedᶜ-≡ x j st))
        grow-part (deferˢ k s)                   = grow-part s

        grow-partᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.partLanes H′ (wkLanes τ ls) ≡ At.partLanes H ls
        grow-partᴸ []                = refl
        grow-partᴸ (lane c k s ∷ ls) =
          trans (cong₂ (λ b L → if b then At.consᴹ H′ (At.part H′ (wkTree τ s)) L else L) (cells (Kit.live c)) (grow-partᴸ ls))
                (cong (λ m → if At.val H (Kit.live c) then m else At.partLanes H ls)
                      (trans (cong (λ m → At.consᴹ H′ m (At.partLanes H ls)) (grow-part s)) (consᴹ-≡ (At.part H s) (At.partLanes H ls))))

      -- What the weakened tree leaves running, and what its pools run.
      mutual
        leftover-wk : ∀ {Δ A B} (u : Sub h Δ A) → At.leftover H′ {B = B} (wkTree τ u) ≡ At.leftover H {B = B} u
        leftover-wk (pendingˢ s q)                     = refl
        leftover-wk (coldˢ s hd ph)                    = refl
        leftover-wk (ofˢ p i xs)                       = refl
        leftover-wk doneˢ                              = refl
        leftover-wk (mapˢ f s)                         = leftover-wk s
        leftover-wk (scanˢ f r s)                      = leftover-wk s
        leftover-wk (takeWhileˢ i p c k tk s)          = leftover-wk s
        leftover-wk (flatMapˢ op f fl oc k r pl so ls) = cong₂ U.unionᶜ (leftover-wk so) (leftover-wkᴸ ls)
        leftover-wk (connectˢ S c b kb k fd rp e rt src bd) =
          cong₂ (λ n l → U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) l))
                (trans (cong₂ (At.sourced H′) (grow-part src) (leftover-wk src)) (sourced-≡ (At.part H src) (At.leftover H src)))
                (leftover-wk {B = ⊤} bd)
        leftover-wk (joinˢ j sk l x st)                = refl
        leftover-wk (deferˢ k s)                       = leftover-wk s

        leftover-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.leftoverL H′ {B = B} (wkLanes τ ls) ≡ At.leftoverL H {B = B} ls
        leftover-wkᴸ []                = refl
        leftover-wkᴸ (lane c k s ∷ ls) = cong₂ U.unionᶜ (leftover-wk s) (leftover-wkᴸ ls)

      pooled-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.pooledL H′ {B = B} (wkLanes τ ls) ≡ At.pooledL H {B = B} ls
      pooled-wkᴸ []                = refl
      pooled-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ (λ b P → if b then P else U.unionᶜ (At.leftover H′ (wkTree τ s)) P) (cells (Kit.live c)) (pooled-wkᴸ ls))
              (cong (λ x → if At.val H (Kit.live c) then At.pooledL H ls else U.unionᶜ x (At.pooledL H ls)) (leftover-wk s))

      pooled-wk : ∀ {Δ A B} (fl : FlatKit.Flat A h) (so : Sub h Δ A) (ls : List (Lane h Δ B))
                → At.pooled H′ (FlatKit.wkFlat τ fl) (wkTree τ so) (wkLanes τ ls) ≡ At.pooled H fl so ls
      pooled-wk fl so ls =
        cong₂ U.unionᶜ (trans (cong (λ b → if b then At.leftover H′ (wkTree τ so) else U.idleᶜ) (cells (FlatKit.Flat.outerDone fl)))
                              (cong (λ x → if At.val H (FlatKit.Flat.outerDone fl) then x else U.idleᶜ) (leftover-wk so)))
                       (pooled-wkᴸ ls)

      -- A path through the weakened tree is the weakening of one through
      -- the old, seen alike.
      mutual
        unwk : ∀ {Δ A Δ′ A′} (t : Sub h Δ A) {x′ : Sub v Δ′ A′} (ψ′ : Path (wkTree τ t) x′)
             → Σ (Sub h Δ′ A′) λ x → Σ (Path t x) λ ψ → x′ ≡ wkTree τ x × seen H′ ψ′ ≡ seen H ψ
        unwk (pendingˢ s q)                     here = _ , here , refl , refl
        unwk (coldˢ s hd ph)                    here = _ , here , refl , refl
        unwk (ofˢ p i xs)                       here = _ , here , refl , refl
        unwk doneˢ                              here = _ , here , refl , refl
        unwk (joinˢ j sk l x st)                here = _ , here , refl , refl
        unwk (mapˢ f s)                         here = _ , here , refl , refl
        unwk (mapˢ f s)                         (in-map ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-map ψ , e , sn
        unwk (scanˢ f r s)                      here = _ , here , refl , refl
        unwk (scanˢ f r s)                      (in-scan ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-scan ψ , e , sn
        unwk (takeWhileˢ i p c k tk s)          here = _ , here , refl , refl
        unwk (takeWhileˢ i p c k tk s)          (in-take ψ′) =
          let x , ψ , e , sn = unwk s ψ′ in x , in-take ψ , e , cong₂ _∧_ (cells (Kit.live c)) (cong (isTaking tk ∧_) sn)
        unwk (flatMapˢ op f fl oc k r pl so ls) here = _ , here , refl , refl
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-outer ψ′) = let x , ψ , e , sn = unwk so ψ′ in x , in-outer ψ , e , sn
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-lanes ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , in-lanes ψ , e , sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) here = _ , here , refl , refl
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-source ψ′) =
          let x , ψ , eq , sn = unwk src ψ′ in x , in-source ψ , eq , cong₂ _∧_ (cong is-just (grow-part bd)) sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-body ψ′) =
          let x , ψ , eq , sn = unwk bd ψ′ in x , in-body ψ , eq , cong₂ _∧_ (cong (λ z → is-just z ∨ is-just e) (grow-part src)) sn
        unwk (deferˢ k s)                       here = _ , here , refl , refl
        unwk (deferˢ k s)                       (in-defer ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-defer ψ , e , sn

        unwkᴸ : ∀ {Δ B Δ′ A′} (ls : List (Lane h Δ B)) {x′ : Sub v Δ′ A′} (ψ′ : PathLanes (wkLanes τ ls) x′)
              → Σ (Sub h Δ′ A′) λ x → Σ (PathLanes ls x) λ ψ → x′ ≡ wkTree τ x × seenL H′ ψ′ ≡ seenL H ψ
        unwkᴸ (lane c k s ∷ ls) (this-lane ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , this-lane ψ , e , cong₂ _∧_ (cells (Kit.live c)) sn
        unwkᴸ (lane c k s ∷ ls) (next-lane ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , next-lane ψ , e , sn

      grow-each : ∀ {t : Sub h [] R} {P : ∀ {Γ A} → U.Node Γ A → Set} → Each H P t → Each H′ P (wkTree τ t)
      Each.parts (grow-each {t = t} E) ψ′ sn {c} eq =
        let x , ψ , e , s = unwk t ψ′ in
        Each.parts E ψ (trans (sym s) sn) (trans (sym (grow-part x)) (subst (λ z → At.part H′ z ≡ just c) e eq))
      Each.pools (grow-each {t = t} E) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        Each.pools E ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq)
      Each.rests (grow-each {t = t} E) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        Each.rests E ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec

      grow-lingers : ∀ {t : Sub h [] R} → Lingers H t → Lingers H′ (wkTree τ t)
      Lingers.pools (grow-lingers {t = t} L) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        subst (Tied pl) (sym (pooled-wk fl so ls)) (Lingers.pools L ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq))
      Lingers.rests (grow-lingers {t = t} L) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        subst (Tied rt) (sym (leftover-wk {B = ⊤} src))
              (Lingers.rests L ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec)

      -- What unsubscribing reaches, and the gates, read through the
      -- weakening.
      mutual
        grow-spent : ∀ {Δ A} (u : Sub h Δ A) → At.Spent H u → At.Spent H′ (wkTree τ u)
        grow-spent (pendingˢ s q)                          _         = lift tt
        grow-spent (coldˢ s hd ph)                         (lift e)  = lift (trans (Grows.handles gr hd) e)
        grow-spent (ofˢ p i xs)                            _         = lift tt
        grow-spent doneˢ                                   _         = lift tt
        grow-spent (mapˢ f s)                              x         = grow-spent s x
        grow-spent (scanˢ f r s)                           x         = grow-spent s x
        grow-spent (takeWhileˢ i p c k tk s)               x         = grow-cut↓ k s x
        grow-spent (flatMapˢ op f fl oc k r pl so ls)      (x , y)   = grow-cut↓ k so x , grow-spentᴸ ls y
        grow-spent (connectˢ S c b kb k fd rp e rt src bd) (x , y)   = grow-cut↓ k src x , grow-cut↓ kb bd y
        grow-spent (joinˢ j sk l x st)                     _         = lift tt
        grow-spent (deferˢ k s)                            x         = grow-cut↓ k s x

        grow-spentᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.SpentLanes H ls → At.SpentLanes H′ (wkLanes τ ls)
        grow-spentᴸ []                _       = lift tt
        grow-spentᴸ (lane c k s ∷ ls) (x , y) = grow-cut↓ k s x , grow-spentᴸ ls y

        grow-cut↓ : ∀ {Δ A} (k : Maybe (Quiet h)) (u : Sub h Δ A) → At.Cut↓ H k u → At.Cut↓ H′ (mapMaybe (wk∋ τ) k) (wkTree τ u)
        grow-cut↓ nothing  u _ = lift tt
        grow-cut↓ (just _) u x = grow-spent u x

      -- A cut read false through the weakening was false.
      cut-off : ∀ {Δ A} (c : Kit.Cut h) (k : Maybe (Quiet h)) (u : Sub h Δ A) → (At.val H (Kit.live c) ≡ false → At.Cut↓ H k u)
              → At.val H′ (Kit.live (Kit.wkCut τ c)) ≡ false → At.Cut↓ H′ (mapMaybe (wk∋ τ) k) (wkTree τ u)
      cut-off c k u g e = grow-cut↓ k u (g (trans (sym (cells (Kit.live c))) e))

      mutual
        grow-gated : ∀ {Δ A} (u : Sub h Δ A) → At.Gated H u → At.Gated H′ (wkTree τ u)
        grow-gated (pendingˢ s q)                          _           = lift tt
        grow-gated (coldˢ s hd ph)                         (lift g)    = lift (λ e → g (trans (sym (Grows.handles gr hd)) e))
        grow-gated (ofˢ p i xs)                            _           = lift tt
        grow-gated doneˢ                                   _           = lift tt
        grow-gated (mapˢ f s)                              x           = grow-gated s x
        grow-gated (scanˢ f r s)                           x           = grow-gated s x
        grow-gated (takeWhileˢ i p c k tk s)               (g , x)     = cut-off c k s g , grow-gated s x
        grow-gated (flatMapˢ op f fl oc k r pl so ls)      (x , y)     = grow-gated so x , grow-gatedᴸ ls y
        grow-gated (connectˢ S c b kb k fd rp e rt src bd) (g , x , y) = cut-off c k src g , grow-gated src x , grow-gated bd y
        grow-gated (joinˢ j sk l x st)                     _           = lift tt
        grow-gated (deferˢ k s)                            x           = grow-gated s x

        grow-gatedᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.GatedLanes H ls → At.GatedLanes H′ (wkLanes τ ls)
        grow-gatedᴸ []                _           = lift tt
        grow-gatedᴸ (lane c k s ∷ ls) (g , x , y) = cut-off c k s g , grow-gated s x , grow-gatedᴸ ls y

      postulate
        -- Every registered callback reads, along the growth, as the
        -- weakened kernel registered it.
        grow-holds : ∀ (t : Sub h [] R) → At.Holds H t [] rootObs → At.Holds H′ (wkTree τ t) [] rootObs

      grow-kernels : ∀ {t : Sub h [] R} → Kernels H t → Kernels H′ (wkTree τ t)
      grow-kernels {t} kn = record { holds = grow-holds t (Kernels.holds kn) ; gated = grow-gated t (Kernels.gated kn) ; settled = settled-wk t (Kernels.settled kn) }

      -- A feed weakened owes whom it owed, and what.
      private
        ∋-inj : ∀ {u w k} (ρ : u ⊑ w) {i j : u ∋ k} → wk∋ ρ i ≡ wk∋ ρ j → i ≡ j
        ∋-inj same⊑    e = e
        ∋-inj (grow ρ) e = ∋-inj ρ (there-inj′ e)
          where
            there-inj′ : ∀ {j w k} {a b : w ∋ k} → _≡_ {A = (j ∷ w) ∋ k} (there a) (there b) → a ≡ b
            there-inj′ refl = refl

        pair-back : ∀ {A} {sk s : Sink h A} {j i : Pos} → _≡_ {A = Sink v A × Pos} (wk∋ τ sk , j) (wk∋ τ s , i) → (sk , j) ≡ (s , i)
        pair-back e with ∋-inj τ (cong proj₁ e) | cong proj₂ e
        ... | refl | refl = refl

      owed-back : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j → At.Owed H fd sk j
      owed-back idle                           ()
      owed-back (feeding a q [])               ()
      owed-back (feeding a q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (feeding a q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (feeding a q ss) m)
      owed-back (finishing q [])               ()
      owed-back (finishing q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (finishing q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (finishing q ss) m)

      owed-fwd : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H fd sk j → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j
      owed-fwd idle                   ()
      owed-fwd (feeding a q [])       ()
      owed-fwd (feeding a q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (feeding a q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (feeding a q ss) m)
      owed-fwd (finishing q [])       ()
      owed-fwd (finishing q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (finishing q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (finishing q ss) m)

      owing-wk : ∀ {A} (fd : Feed A h) j → At.owing H′ (wkFeed τ fd) j ≡ At.owing H fd j
      owing-wk idle             j = refl
      owing-wk (feeding a q ss) j = refl
      owing-wk (finishing q ss) j = refl

      owingNone-≡ : ∀ {A : Set} (e : Maybe Pos) → At.owingNone H′ {A} e ≡ At.owingNone H e
      owingNone-≡ nothing  = refl
      owingNone-≡ (just _) = refl

      wkNow : ∀ {Δ} → At.Now H Δ → At.Now H′ Δ
      wkNow []             = []
      wkNow ((fd , e) ∷ ν) = (wkFeed τ fd , e) ∷ wkNow ν

      lookup-wk : ∀ {Δ A} (ν : At.Now H Δ) (x : A ∈ Δ) → lookupᴬ (wkNow ν) x ≡ (wkFeed τ (proj₁ (lookupᴬ ν x)) , proj₂ (lookupᴬ ν x))
      lookup-wk (_ ∷ ν) (hereᴬ refl) = refl
      lookup-wk (_ ∷ ν) (thereᴬ x)   = lookup-wk ν x

      -- Every live joiner held what its feed owed it, read through the
      -- weakening.
      mutual
        fed-wk : ∀ {Δ A} (u : Sub h Δ A) (ν : At.Now H Δ) → At.Fed H u ν → At.Fed H′ (wkTree τ u) (wkNow ν)
        fed-wk (pendingˢ s q)                          ν _       = lift tt
        fed-wk (coldˢ s hd ph)                         ν _       = lift tt
        fed-wk (ofˢ p i xs)                            ν _       = lift tt
        fed-wk doneˢ                                   ν _       = lift tt
        fed-wk (mapˢ f s)                              ν x       = fed-wk s ν x
        fed-wk (scanˢ f r s)                           ν x       = fed-wk s ν x
        fed-wk (takeWhileˢ i p c k tk s)               ν x       = fed-wk s ν x
        fed-wk (flatMapˢ op f fl oc k r pl so ls)      ν (x , y) = fed-wk so ν x , fed-wkᴸ ls ν y
        fed-wk (connectˢ S c b kb k fd rp e rt src bd) ν (x , y) = fed-wk src ν x , fed-wk bd ((fd , e) ∷ ν) y
        fed-wk (joinˢ j sk l x st)                     ν (lift f) =
          subst (λ p → Lift _ (At.val H′ (wkR τ l) ≡ true → (At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owing H′ (proj₁ p) j)
                                                         × (¬ At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owingNone H′ (proj₂ p))))
                (sym (lookup-wk ν x))
                (lift λ on → let (o , n) = f (trans (sym (cells l)) on) in
                  (λ m → trans (o (owed-back (proj₁ (lookupᴬ ν x)) m)) (sym (owing-wk (proj₁ (lookupᴬ ν x)) j)))
                  , (λ ¬m → trans (n (λ m → ¬m (owed-fwd (proj₁ (lookupᴬ ν x)) m))) (sym (owingNone-≡ (proj₂ (lookupᴬ ν x))))))
        fed-wk (deferˢ k s)                            ν x       = fed-wk s ν x

        fed-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) (ν : At.Now H Δ) → At.FedLanes H ls ν → At.FedLanes H′ (wkLanes τ ls) (wkNow ν)
        fed-wkᴸ []                ν _       = lift tt
        fed-wkᴸ (lane c k s ∷ ls) ν (x , y) = fed-wk s ν x , fed-wkᴸ ls ν y

      grow-meaning : ∀ {t : Sub h [] R} → Meaning H t → Meaning H′ (wkTree τ t)
      grow-meaning {t} mn = record { fed = fed-wk t [] (Meaning.fed mn) }

      -- Every live timer a pending frame's, read through the weakening.
      grow-timed : ∀ {ts : List (Timer h)} (t : Sub h [] R) → At.Timed H ts (pendings t) → At.Timed H′ (mapList (wkTimer τ) ts) (pendings (wkTree τ t))
      grow-timed {ts} t (a , b) =
        all-mapL (wkTimer τ) one a , subst (All (λ tm → At.spentʰ H′ (Timer.handle tm) ≡ false → tm ∈ mapList (wkTimer τ) ts)) (sym (pendings-wk t)) (all-mapL (wkTimer τ) two b)
        where
          one : ∀ {tm} → At.spentʰ H (Timer.handle tm) ≡ true ⊎ tm ∈ pendings t
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ true ⊎ wkTimer τ tm ∈ pendings (wkTree τ t)
          one {tm} (inj₁ e) = inj₁ (trans (Grows.handles gr (Timer.handle tm)) e)
          one      (inj₂ m) = inj₂ (subst (_ ∈_) (sym (pendings-wk t)) (∈-mapL (wkTimer τ) m))

          two : ∀ {tm} → (At.spentʰ H (Timer.handle tm) ≡ false → tm ∈ ts)
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ false → wkTimer τ tm ∈ mapList (wkTimer τ) ts
          two {tm} g e = ∈-mapL (wkTimer τ) (g (trans (sym (Grows.handles gr (Timer.handle tm))) e))

      postulate
        -- Every subject's subscribers its joiners, or silenced, read
        -- through the weakening.
        grow-joined : ∀ (t : Sub h [] R) → At.Joined H (subjects t) (joiners t []) → At.Joined H′ (subjects (wkTree τ t)) (joiners (wkTree τ t) [])

      grow-queue : ∀ {t : Sub h [] R} {p clk ts} → Queue H p clk ts t → Queue H′ p clk (mapList (wkTimer τ) ts) (wkTree τ t)
      grow-queue {t} qu = record { timed = grow-timed t (Queue.timed qu) ; joined = grow-joined t (Queue.joined qu)
                                 ; ordered = linked-mapL (Queue.ordered qu) ; ahead = all-mapL (wkTimer τ) (λ x → x) (Queue.ahead qu) }

      postulate
        grow-owned   : ∀ {t : Sub h [] R} {w} {σ : w ⊑ h} {K bs} {Δ A s q} {π : Path t (pendingˢ {Δ = Δ} {A} s q)} {act act′ cd cd′}
                         (sk : StackAs t q σ K bs) {a a′}
                     → Owned H t (subAs {act = act} π cd sk a) → Owned H′ (wkTree τ t) (subAs {act = act′} (wkPath τ π) cd′ (grow-stack sk) a′)

  postulate
    -- A compiled subscription read alike under alike observers and
    -- continuations.
    compile-cong : ∀ {Γ A u w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ w) {o o′ : Observer A w} {k k′ : Kont w}
                 → ObsRel o o′ → KontRel k k′ → compile s E υ o k ≗ compile s E υ o′ k′

    -- A compiled subscription reads its subjects weakened to the world it
    -- runs at, whichever stretch of the weakening they were carried along.
    compile-env : ∀ {Γ A u v w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ v) (ρ : v ⊑ w) {o : Observer A w} {k : Kont w}
                → compile s E (υ ⨾ ρ) o k ≗ compile s (wkEnv υ E) ρ o k

    -- A walk's continuation reads its subscription's unsubscribe only.
    walk-kont-sub : ∀ {h Δ A} {t : Sub h [] R} {x : Sub h Δ A} (π : Path t x) {v} (τ : h ⊑ v) {U U′ : Subscription v}
                  → Subscription.unsubscribe U ≗ Subscription.unsubscribe U′ → Here.kont (walk π top) τ U ≗ Here.kont (walk π top) τ U′

  ----------------------------------------------------------------------
  -- Names, weakened and planted

  -- A name carried along a growth.
  wkN : ∀ {h v} → h ⊑ v → Name h → Name v
  wkN τ (k , i) = k , wk∋ τ i

  -- A name some growth made: what the old world named, carried along.
  Img : ∀ {h₀ h} → h₀ ⊑ h → Name h → Set
  Img {h₀} ν (k , j) = Σ (h₀ ∋ k) λ i → wk∋ ν i ≡ j

  to-img : ∀ {h₀ h} (ν : h₀ ⊑ h) {x m} → wkN ν x ≡ m → Img ν m
  to-img ν {_ , i} refl = i , refl

  there-inj : ∀ {w j k k′} {i : w ∋ k} {i′ : w ∋ k′} → _≡_ {A = Name (j ∷ w)} (k , there i) (k′ , there i′) → _≡_ {A = Name w} (k , i) (k′ , i′)
  there-inj refl = refl

  wkN-inj : ∀ {h v} (τ : h ⊑ v) {x y : Name h} → wkN τ x ≡ wkN τ y → x ≡ y
  wkN-inj same⊑    e = e
  wkN-inj (grow τ) e = wkN-inj τ (there-inj e)

  quiet-wk : ∀ {h v} (τ : h ⊑ v) (k : Maybe (Quiet h)) → quietName (mapMaybe (wk∋ τ) k) ≡ mapᴸ (wkN τ) (quietName k)
  quiet-wk τ nothing  = refl
  quiet-wk τ (just _) = refl

  wk++ : ∀ {h v} (τ : h ⊑ v) xs ys {xs′ ys′ : List (Name v)} → xs′ ≡ mapᴸ (wkN τ) xs → ys′ ≡ mapᴸ (wkN τ) ys → xs′ ++ ys′ ≡ mapᴸ (wkN τ) (xs ++ ys)
  wk++ τ xs ys e₁ e₂ = trans (cong₂ _++_ e₁ e₂) (sym (map-++ (wkN τ) xs ys))

  -- A weakened tree names what the tree named, each weakened.
  mutual
    names-wkTree : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → names (wkTree τ t) ≡ mapᴸ (wkN τ) (names t)
    names-wkTree τ (pendingˢ s q)                      = refl
    names-wkTree τ (coldˢ s hd ph)                     = refl
    names-wkTree τ (ofˢ p i xs)                        = refl
    names-wkTree τ doneˢ                               = refl
    names-wkTree τ (mapˢ f t)                          = names-wkTree τ t
    names-wkTree τ (scanˢ f r t)                       = cong (_ ∷_) (names-wkTree τ t)
    names-wkTree τ (takeWhileˢ i p c k tk t)           =
      wk++ τ (cutNames c) (quietName k ++ names t) refl (wk++ τ (quietName k) (names t) (quiet-wk τ k) (names-wkTree τ t))
    names-wkTree τ (flatMapˢ op f fl oc k r pl t ls)   =
      wk++ τ (flatNames fl) (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names t ++ laneNames ls) refl
        (wk++ τ (cutNames oc) (quietName k ++ (slot _ , r) ∷ names t ++ laneNames ls) refl
          (wk++ τ (quietName k) ((slot _ , r) ∷ names t ++ laneNames ls) (quiet-wk τ k)
            (cong (_ ∷_) (wk++ τ (names t) (laneNames ls) (names-wkTree τ t) (names-wkLanes τ ls)))))
    names-wkTree τ (connectˢ S c b kb k fd q e rt s bd) =
      wk++ τ (subjectNames S) (cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names s ++ names bd) refl
        (wk++ τ (cutNames c) ((cell _ , b) ∷ quietName kb ++ quietName k ++ names s ++ names bd) refl
          (cong (_ ∷_) (wk++ τ (quietName kb) (quietName k ++ names s ++ names bd) (quiet-wk τ kb)
            (wk++ τ (quietName k) (names s ++ names bd) (quiet-wk τ k) (wk++ τ (names s) (names bd) (names-wkTree τ s) (names-wkTree τ bd))))))
    names-wkTree τ (joinˢ j s fl x m)                  = refl
    names-wkTree τ (deferˢ k t)                        = wk++ τ (quietName k) (names t) (quiet-wk τ k) (names-wkTree τ t)

    names-wkLanes : ∀ {h v Δ B} (τ : h ⊑ v) (ls : List (Lane h Δ B)) → laneNames (wkLanes τ ls) ≡ mapᴸ (wkN τ) (laneNames ls)
    names-wkLanes τ []                = refl
    names-wkLanes τ (lane c k t ∷ ls) =
      wk++ τ (cutNames c) (quietName k ++ names t ++ laneNames ls) refl
        (wk++ τ (quietName k) (names t ++ laneNames ls) (quiet-wk τ k) (wk++ τ (names t) (laneNames ls) (names-wkTree τ t) (names-wkLanes τ ls)))

  -- A weakened tree's names are apart where the tree's were.
  wk-pairs : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → AllPairs _≢_ (names t) → AllPairs _≢_ (names (wkTree τ t))
  wk-pairs τ t ap = subst (AllPairs _≢_) (sym (names-wkTree τ t)) (pairs-map⁺ (pairs-map (λ ne e → ne (wkN-inj τ e)) ap))

  -- Each name of a weakened tree a name of the tree, weakened.
  wk-img : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) {m} → m ∈ names (wkTree τ t) → Σ (Name h) λ x → x ∈ names t × wkN τ x ≡ m
  wk-img τ t {m} m∈ with ∈-map⁻ (wkN τ) (subst (m ∈_) (names-wkTree τ t) m∈)
  ... | x , x∈ , e = x , x∈ , sym e

  names-wk : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) {k} (j : v ∋ k) → (k , j) ∈ names (wkTree τ t)
           → Σ (h ∋ k) λ i → wk∋ τ i ≡ j × (k , i) ∈ names t
  names-wk τ t j m with wk-img τ t m
  ... | (_ , i) , m′ , refl = i , refl , m′

  -- A permutation keeps names apart.
  pairs-↭ : ∀ {h} {xs ys : List (Name h)} → xs ↭ ys → AllPairs _≢_ xs → AllPairs _≢_ ys
  pairs-↭ ↭-refl′           ap                      = ap
  pairs-↭ (↭-prep′ x p)     (a ∷ ap)                = All-resp-↭ p a ∷ pairs-↭ p ap
  pairs-↭ (↭-swap′ x y p)   ((xy ∷ ax) ∷ ay ∷ ap)   = ((λ e → xy (sym e)) ∷ All-resp-↭ p ay) ∷ All-resp-↭ p ax ∷ pairs-↭ p ap
  pairs-↭ (↭-trans′ p q)    ap                      = pairs-↭ q (pairs-↭ p ap)

  -- Names put in front of a stretch, or behind it.
  pre : ∀ {h} (X : List (Name h)) {ys s s′ : List (Name h)} → s′ ↭ ys ++ s → X ++ s′ ↭ ys ++ X ++ s
  pre X {ys} p = ↭-trans (↭-++⁺ˡ X p) (shifts X ys)

  post : ∀ {h} (Q : List (Name h)) {ys s s′ : List (Name h)} → s′ ↭ ys ++ s → s′ ++ Q ↭ ys ++ s ++ Q
  post Q {ys} {s} p = ↭-trans (↭-++⁺ʳ Q p) (↭-reflexive (++-assoc ys s Q))

  -- A node replanted naming `X` more than the one it replaced: the tree
  -- names `X` more.
  mutual
    names-plant-↭ : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) {X}
                  → names v ↭ X ++ names u → names (plant π v) ↭ X ++ names t
    names-plant-↭ here v e = e
    names-plant-↭ (in-map π) v {X} e = names-plant-↭ π v {X} e
    names-plant-↭ (in-scan π) v {X} e = pre (_ ∷ []) {X} (names-plant-↭ π v {X} e)
    names-plant-↭ (in-take {c = c} {k} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (names-plant-↭ π v {X} e))
    names-plant-↭ (in-outer {fl = fl} {oc} {k} {ls = ls} π) v {X} e =
      pre (flatNames fl) {X} (pre (cutNames oc) {X} (pre (quietName k) {X} (pre (_ ∷ []) {X} (post (laneNames ls) {X} (names-plant-↭ π v {X} e)))))
    names-plant-↭ (in-lanes {fl = fl} {oc} {k} {t = so} π) v {X} e =
      pre (flatNames fl) {X} (pre (cutNames oc) {X} (pre (quietName k) {X} (pre (_ ∷ []) {X} (pre (names so) {X} (names-plant-↭ᴸ π v {X} e)))))
    names-plant-↭ (in-source {S = S} {c} {kb = kb} {k} {bd = bd} π) v {X} e =
      pre (subjectNames S) {X} (pre (cutNames c) {X} (pre (_ ∷ []) {X} (pre (quietName kb) {X} (pre (quietName k) {X} (post (names bd) {X} (names-plant-↭ π v {X} e))))))
    names-plant-↭ (in-body {S = S} {c} {kb = kb} {k} {t = src} π) v {X} e =
      pre (subjectNames S) {X} (pre (cutNames c) {X} (pre (_ ∷ []) {X} (pre (quietName kb) {X} (pre (quietName k) {X} (pre (names src) {X} (names-plant-↭ π v {X} e))))))
    names-plant-↭ (in-defer {k = k} π) v {X} e = pre (quietName k) {X} (names-plant-↭ π v {X} e)

    names-plant-↭ᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) {X}
                   → names v ↭ X ++ names u → laneNames (plantᴸ π v) ↭ X ++ laneNames ls
    names-plant-↭ᴸ (this-lane {c = c} {k} {ls = ls} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (post (laneNames ls) {X} (names-plant-↭ π v {X} e)))
    names-plant-↭ᴸ (next-lane {l = lane c k s} π) v {X} e = pre (cutNames c) {X} (pre (quietName k) {X} (pre (names s) {X} (names-plant-↭ᴸ π v {X} e)))

  -- THE FRESH FRAME: a node replanted naming `X` more, `X` apart from
  -- itself and from every name the tree held, leaves the tree's names
  -- apart.
  fresh-plant : ∀ {h Δ A} {t : Sub h [] R} {u : Sub h Δ A} (π : Path t u) (v : Sub h Δ A) {X}
              → names v ↭ X ++ names u → AllPairs _≢_ X → AllPairs _≢_ (names t) → All (λ n → All (n ≢_) (names t)) X
              → AllPairs _≢_ (names (plant π v))
  fresh-plant π v e px pt dj = pairs-↭ (↭-sym (names-plant-↭ π v e)) (pairs-++⁺ px pt dj)

  -- A pending node replaced: every name the new node holds is more.
  pending-↭ : ∀ {h Δ A} (v : Sub h Δ A) → names v ↭ names v ++ []
  pending-↭ v = ↭-reflexive (sym (++-idʳ (names v)))

  -- Names no growth made, apart from every name one did.
  fresh-new : ∀ {h₀ h} (ν : h₀ ⊑ h) {ns ms : List (Name h)} → (∀ {m} → m ∈ ms → Img ν m)
            → All (λ n → ∀ {m} → Img ν m → n ≢ m) ns → All (λ n → All (n ≢_) ms) ns
  fresh-new ν im = all-map (λ f → tabulateᴬ λ m∈ → f (im m∈))

  -- A scan's observer over alike observers.
  scanO-cong : ∀ {h A B} (f : B → A → B) (r : Ref h (base B)) {o o′ : Observer B h} → ObsRel o o′ → ObsRel (Canon.scanO f r o) (Canon.scanO f r o′)
  scanO-cong f r (n , c , x) = (λ a → readRef≗ refl λ σ b → wk≗ σ (writeRef≗ refl refl (n (f b a)))) , c , x

  ≗-sym : ∀ {w B} {m m′ : Act w B} → m ≗ m′ → m′ ≗ m
  ≗-sym (done≗ e)                = done≗ (sym e)
  ≗-sym (newRef≗ e f)            = newRef≗ (sym e) λ σ r → ≗-sym (f σ r)
  ≗-sym (readRef≗ refl f)        = readRef≗ refl λ σ x → ≗-sym (f σ x)
  ≗-sym (writeRef≗ refl e k)     = writeRef≗ refl (sym e) (≗-sym k)
  ≗-sym (register≗ n c x k)      = register≗ (λ a → ≗-sym (n a)) (≗-sym c) (≗-sym x) λ σ s → ≗-sym (k σ s)
  ≗-sym (send≗ refl k)           = send≗ refl (≗-sym k)
  ≗-sym (finish≗ refl k)         = finish≗ refl (≗-sym k)
  ≗-sym (startCold≗ refl f)      = startCold≗ refl λ σ hd → ≗-sym (f σ hd)
  ≗-sym (stop≗ refl k)           = stop≗ refl (≗-sym k)
  ≗-sym (stash≗ m f)             = stash≗ (≗-sym m) λ σ q → ≗-sym (f σ q)
  ≗-sym (cancel≗ refl k)         = cancel≗ refl (≗-sym k)
  ≗-sym (eff≗ f)                 = eff≗ λ a → ≗-sym (f a)
  ≗-sym (here≗ f)                = here≗ λ p → ≗-sym (f p)
  ≗-sym (under≗ m k)             = under≗ (≗-sym m) (≗-sym k)
  ≗-sym diverge≗                 = diverge≗
  ≗-sym (unfold≗ refl n c x k m) = unfold≗ refl (λ a → ≗-sym (n a)) (≗-sym c) (≗-sym x) (λ σ q → ≗-sym (k σ q)) (≗-sym m)

  obs-trans : ∀ {A w} {o₁ o₂ o₃ : Observer A w} → ObsRel o₁ o₂ → ObsRel o₂ o₃ → ObsRel o₁ o₃
  obs-trans (n , c , x) (n′ , c′ , x′) = (λ a → ≗-trans (n a) (n′ a)) , ≗-trans c c′ , ≗-trans x x′

  obs-wk : ∀ {A w v} (ρ : w ⊑ v) {o o′ : Observer A w} → ObsRel o o′ → ObsRel (wkObs ρ o) (wkObs ρ o′)
  obs-wk ρ (n , c , x) = (λ a → wk≗ ρ (n a)) , wk≗ ρ c , wk≗ ρ x

  -- An observer weakened along a composite, as weakened twice.
  obs-⨾ : ∀ {A u v w} (σ : u ⊑ v) (τ : v ⊑ w) (o : Observer A u) → ObsRel (wkObs (σ ⨾ τ) o) (wkObs τ (wkObs σ o))
  obs-⨾ σ τ o = (λ a → ≗-sym (wk-wk σ τ _)) , ≗-sym (wk-wk σ τ _) , ≗-sym (wk-wk σ τ _)

  -- An entry of a weakened heap: the entry, its inclusion carried on.
  get-wk : ∀ {h v w k} (ρ : h ⊑ v) (xs : All (Stored h) w) (i : w ∋ k) → get (wkAll ρ xs) i ≡ stored (Stored.val (get xs i)) (Stored.into (get xs i) ⨾ ρ)
  get-wk ρ (stored x σ ∷ xs) hereʳ     = refl
  get-wk ρ (stored x σ ∷ xs) (there i) = get-wk ρ xs i

  look-ext : ∀ {h j k} (H : Heapᴹ h) (x : Val (j ∷ h) j) (i : h ∋ k)
           → look (extend H x) (there i) ≡ wkVal k (Stored.into (get H i) ⨾ new) (Stored.val (get H i))
  look-ext {k = k} H x i = cong (λ e → wkVal k (Stored.into e) (Stored.val e)) (get-wk new H i)

  -- An allocation grows the world and moves nothing.
  grows-extend : ∀ {h k} (H : Heapᴹ h) (x : Val (k ∷ h) k) → Grows new H (extend H x)
  grows-extend H x = record
    { cells   = λ {t} r → trans (cong lower (look-ext H x r)) (sym (wkEl-wk t (Stored.into (get H r)) new (lower (Stored.val (get H r)))))
    ; slots   = λ {X} s → subst (λ c → CbRel c (wkVal (slot X) new (cbs H s))) (sym (look-ext H x s))
                  ( (λ a → ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.onNext (Stored.val (get H s)) a)))
                  , ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.onComplete (Stored.val (get H s))))
                  , ≗-sym (wk-wk (Stored.into (get H s)) new (Callbacks.isClosed (Stored.val (get H s)))) )
    ; stashes = λ u → subst (λ m → m ≗ wkAct new (look H u)) (sym (look-ext H x u)) (≗-sym (wk-wk (Stored.into (get H u)) new (Stored.val (get H u))))
    ; handles = λ hd → cong lower (look-ext H x hd) }

  if≗ : ∀ {w B} b {x x′ y y′ : Act w B} → x ≗ x′ → y ≗ y′ → (if b then x else y) ≗ (if b then x′ else y′)
  if≗ true  e _ = e
  if≗ false _ e = e

  -- A takeWhile's observer over alike observers.
  takeO-cong : ∀ {h A} i (p : A → Bool) (c : Kit.Cut h) {o o′ : Observer A h} → ObsRel o o′ → ObsRel (Canon.takeWhileO i p c o) (Canon.takeWhileO i p c o′)
  takeO-cong i p c (n , cm , x) =
      (λ a → guard≗ (if≗ (p a) (n a) (bind≗ (if≗ i (under≗ (n a) (≗-refl _)) (≗-refl _)) λ _ → under≗ cm (≗-refl _))))
    , guard≗ cm
    , readRef≗ refl λ σ b → wk≗ σ (if≗ b x (≗-refl _))
    where guard≗ : ∀ {m m′} → m ≗ m′ → Kit.guard c m ≗ Kit.guard c m′
          guard≗ e = readRef≗ refl λ σ b → wk≗ σ (if≗ b e (≗-refl _))

  obs-sym : ∀ {A w} {o o′ : Observer A w} → ObsRel o o′ → ObsRel o′ o
  obs-sym (n , c , x) = (λ a → ≗-sym (n a)) , ≗-sym c , ≗-sym x

  -- A guarded observer over alike observers.
  guarded-cong : ∀ {h A} (c : Kit.Cut h) {o o′ : Observer A h} → ObsRel o o′ → ObsRel (Kit.guarded c o) (Kit.guarded c o′)
  guarded-cong c (n , cm , x) = (λ a → gd (n a)) , gd cm , readRef≗ refl λ σ b → wk≗ σ (if≗ b x (≗-refl _))
    where gd : ∀ {m m′} → m ≗ m′ → Kit.guard c m ≗ Kit.guard c m′
          gd e = readRef≗ refl λ σ b → wk≗ σ (if≗ b e (≗-refl _))

  -- A pool weakened twice, as weakened once.
  wkFlat-wk : ∀ {A u v w} (σ : u ⊑ v) (τ : v ⊑ w) (st : FlatKit.Flat A u) → FlatKit.wkFlat τ (FlatKit.wkFlat σ st) ≡ FlatKit.wkFlat (σ ⨾ τ) st
  wkFlat-wk σ τ st = flat≡ (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _)
    where flat≡ : ∀ {A w} {a a′ : Ref w (base ℕ)} {d d′ : Ref w (base Bool)} {q q′ : Ref w (fifo A)} {l l′ : Ref w (list Kit.cutTy)} {r r′ : Ref w (maybe (sink ⊤))}
                → a ≡ a′ → d ≡ d′ → q ≡ q′ → l ≡ l′ → r ≡ r′
                → _≡_ {A = FlatKit.Flat A w} (record { active = a ; outerDone = d ; queue = q ; lanes = l ; refill = r })
                                             (record { active = a′ ; outerDone = d′ ; queue = q′ ; lanes = l′ ; refill = r′ })
          flat≡ refl refl refl refl refl = refl

  -- Cutting every lane, weakened, cuts every lane of the weakened pool.
  killAll-wk : ∀ {A w v} (ρ : w ⊑ v) (st : FlatKit.Flat A w) → wkAct ρ (killAllᶜ st) ≗ killAllᶜ (FlatKit.wkFlat ρ st)
  killAll-wk ρ st = readRef≗ refl λ σ cs → writeRef≗ (sym (wk∋-wk ρ σ (FlatKit.Flat.lanes st))) refl
                      (writeRef≗ (sym (wk∋-wk ρ σ (FlatKit.Flat.active st))) refl (≗-refl _))

  -- A SCAN RESTAGED IN THE GROWN WORLD: its accumulator the newest cell,
  -- its source pending beneath it.
  module Scanned {h} {T₀ : Sub h [] R} {Δ A B} {f : B → A → B} {z : B} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.scan f z s) q)) where
    h′ : World
    h′ = cell (base B) ∷ h

    T₁ : Sub h′ [] R
    T₁ = wkTree new T₀

    π₁ : Path T₁ (pendingˢ (T.scan f z s) q)
    π₁ = wkPath new π

    v : Sub h′ Δ B
    v = scanˢ f hereʳ (pendingˢ s q)

    open Moved π₁ v using (t′; restack; Alone; reticked) public

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π₁ v ⊕ in-scan here

    walk′ : walk π′ top ≡ walk (in-scan {f = f} {r = hereʳ} {t = pendingˢ s q} here) (walk π₁ top)
    walk′ = trans (walk-⊕ (planted π₁ v) (in-scan here) top) (cong (λ W → walk (in-scan {f = f} {r = hereʳ} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π₁ v top))

    ν : h ⊑ h′
    ν = new

    wg = Grown.walk-grow ν π


    -- The source compiles as the scan's body did, under the scan's
    -- observer over the grown walk.
    code′ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) {act} → wkEnv υ E′ ≡ Here.env (walk π top)
          → act ≗ compile s E′ (υ ⨾ new) (Canon.scanO f hereʳ (wkObs new (Here.obs (walk π top)))) (wkKont new (Here.kont (walk π top)))
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h′) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {u} E′ υ {act} e c = u , E′ , υ ⨾ new
      , subst (λ W → wkEnv (υ ⨾ new) E′ ≡ Here.env W) (sym walk′) (Grown.env-grow ν π E′ υ e)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ new) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ new) (scanO-cong f hereʳ (proj₁ wg)) (proj₁ (proj₂ wg))))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-scan (planted π₁ v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₀
    less = subst (pend t′ <_) (pend-grow new T₀) (pend-less π₁ v ≤-refl)

    -- A scan over a pending source holds nothing a call is owed at, and
    -- one pending node: its source.
    inner : Moved.Inner π₁ v (in-scan here)
    inner = record { no-of = λ { (in-scan ()) } ; no-cold = λ { (in-scan ()) } ; one-pend = λ { (in-scan here) → refl }
                   ; no-end = λ { (in-scan ()) } ; no-cut = λ { (in-scan ()) } ; no-feed = λ { (in-scan ()) } ; no-fin = λ { (in-scan ()) }
                   ; not-self = λ _ () }

    -- The accumulator is a name the tree did not hold.
    scan-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    scan-fresh fs = fresh-plant π₁ v (pending-↭ v) ([] ∷ []) (wk-pairs new T₀ fs)
      (fresh-new new (λ m∈ → let (_ , _ , e) = wk-img new T₀ m∈ in to-img new e) ((λ { {_ , _} (_ , refl) () }) ∷ []))

    module _ (H′ : Heapᴹ h′) (eqv : At.part H′ (pendingˢ (T.scan f z s) q) ≡ At.part H′ v) where
      -- The scan's heads are its source's.
      rs-behind : ∀ {p} → Each H′ (Heads p) T₁ → Each H′ (Heads p) t′
      rs-behind {p} = each-plant H′ π₁ v eqv tr
        where
          unscan : ∀ {c : U.Node Δ A} {z′} → Heads p (U.scanᶜ f z′ c) → Heads p c
          unscan {c} {z′} hd e = hd (trans (head-scan f z′ (U.step c)) e)

          pa : ∀ {Δ′ A′} {w : Sub h′ Δ′ A′} → Each H′ (Heads p) (pendingˢ (T.scan f z s) q) → (ψ : Path v w) → seen H′ ψ ≡ true
             → ∀ {c} → At.part H′ w ≡ just c → Heads p c
          pa eu here            _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-scan here)  _ refl = unscan {U.subscribe s q} (Each.parts eu here refl refl)

          tr : Each H′ (Heads p) (pendingˢ (T.scan f z s) q) → Each H′ (Heads p) v
          tr eu = record { parts = pa eu ; pools = λ { (in-scan ()) } ; rests = λ { (in-scan ()) } }

      -- A scan runs what its source runs.
      rs-lingers : Lingers H′ T₁ → Lingers H′ t′
      rs-lingers = lingers-plant H′ π₁ v eqv (λ {C} → rest-pinned (U.restᶜ {B = C} (U.subscribe s q))) (record { pools = λ { (in-scan ()) } ; rests = λ { (in-scan ()) } })

      rs-kernels : Kernels H′ T₁ → Kernels H′ t′
      rs-kernels kn = record { holds = holds-plant H′ π₁ v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H′ π₁ v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant π₁ v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

      rs-meaning : Meaning H′ T₁ → Meaning H′ t′
      rs-meaning mn = record { fed = fed-plant H′ π₁ v (λ _ fd → fd) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₁
      pendings′ with pendings-plant π₁ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rs-queue : ∀ {p clk ts} → Queue H′ p clk ts T₁ → Queue H′ p clk ts t′
      rs-queue {ts = ts} qu =
        record { timed   = subst (At.Timed H′ ts) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H′) (sym (subjects-plant π₁ v refl)) (sym (joiners-plant π₁ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- A scan begun allocates its accumulator, holding the seed, and begins
  -- its source under the scan's observer, one subscription fewer owed.
  scan-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {f : B → A → B} {z : B} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.scan f z s) → Restages cr s
  scan-restage {m = mach ⟨ H , _ , run _ _ _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs {s = T.scan f z s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl =
    _ , now
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = S.t′
             ; ctlAs = subAs S.π′ (S.code′ E′ υ e (kk new hereʳ)) (S.restack sk₁ a₁) (S.alones _)
             ; meets = trans (part-plant H′ S.π₁ S.v eqv) (trans (G.grow-part gr (Carried.tree cr)) (Carried.meets cr))
             ; owned = Moved.Owning.reowned S.π₁ S.v H′ eqv (in-scan here) S.inner {cd = Grown.code-grow S.ν π E′ υ e} sk₁ a₁ (G.grow-owned gr sk (Carried.owned cr))
             ; kernels = S.rs-kernels H′ eqv (G.grow-kernels gr (Carried.kernels cr))
             ; meaning = S.rs-meaning H′ eqv (G.grow-meaning gr (Carried.meaning cr))
             ; queue = S.rs-queue H′ eqv (G.grow-queue gr (Carried.queue cr))
             ; books = record { fresh = S.scan-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , S.reticked sk₁ a₁ (G.grow-ticked sk (proj₂ (Books.clocked bk)))
                              ; paidUp = cong (mapList (wkTodo new)) (Books.paidUp bk) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl now) ; behind = S.rs-behind H′ eqv (G.grow-each gr (Carried.behind cr))
             ; lingers = S.rs-lingers H′ eqv (G.grow-lingers gr (Carried.lingers cr)) }
    , refl , inj₁ (inj₁ S.less)
    where module S = Scanned {f = f} {z = z} {s = s} π
          module G = Grown S.ν
          H′ = extend H (lift z)
          gr = grows-extend H (lift z)
          sk₁ = G.grow-stack sk
          a₁ = G.grow-alone π sk a
          eqv : At.part H′ (pendingˢ (T.scan f z s) _) ≡ At.part H′ S.v
          eqv = refl
          bk = Carried.books cr

  -- A TAKEWHILE RESTAGED IN THE WORLD GROWN TWICE: its cut the two
  -- newest cells, live and holding nothing, its source pending beneath
  -- it.
  module Taken {h} {T₀ : Sub h [] R} {Δ A} {i} {p : A → Bool} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.takeWhile i p s) q)) where
    h₁ h₂ : World
    h₁ = cell (base Bool) ∷ h
    h₂ = cell (maybe quiet) ∷ h₁

    ν₁ : h ⊑ h₁
    ν₁ = new

    ν₂ : h₁ ⊑ h₂
    ν₂ = new

    T₁ : Sub h₁ [] R
    T₁ = wkTree ν₁ T₀

    π₁ : Path T₁ (pendingˢ (T.takeWhile i p s) q)
    π₁ = wkPath ν₁ π

    T₂ : Sub h₂ [] R
    T₂ = wkTree ν₂ T₁

    π₂ : Path T₂ (pendingˢ (T.takeWhile i p s) q)
    π₂ = wkPath ν₂ π₁

    c₂ : Kit.Cut h₂
    c₂ = wkR ν₂ hereʳ , hereʳ

    v : Sub h₂ Δ A
    v = takeWhileˢ i p c₂ nothing taking (pendingˢ s q)

    open Moved π₂ v using (t′; restack; Alone; reticked) public

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π₂ v ⊕ in-take here

    walk′ : walk π′ top ≡ walk (in-take {i = i} {p} {c₂} {nothing} {taking} {t = pendingˢ s q} here) (walk π₂ top)
    walk′ = trans (walk-⊕ (planted π₂ v) (in-take here) top)
                  (cong (λ W → walk (in-take {i = i} {p} {c₂} {nothing} {taking} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π₂ v top))

    wg₁ = Grown.walk-grow ν₁ π
    wg₂ = Grown.walk-grow ν₂ π₁

    obs₂ : ObsRel (wkObs (ν₁ ⨾ ν₂) (Here.obs (walk π top))) (Here.obs (walk π₂ top))
    obs₂ = obs-trans (obs-trans (obs-⨾ ν₁ ν₂ _) (obs-wk ν₂ (proj₁ wg₁))) (proj₁ wg₂)

    -- The kernel's continuation, the take's over the twice-grown walk.
    kontₖ : Kont h₂
    kontₖ τ sub = Kit.attach (Kit.wkCut τ c₂) sub >>ᴬ Here.kont (walk π top) ((ν₁ ⨾ ν₂) ⨾ τ) (unsubscribing (Kit.cut (Kit.wkCut τ c₂)))

    kont₂ : KontRel kontₖ (takeK c₂ (Here.kont (walk π₂ top)))
    kont₂ τ sub = bind≗ (≗-refl (Kit.attach (Kit.wkCut τ c₂) sub)) λ _ →
      ≗-trans (≗-sym (from-⨾ (λ ζ → Here.kont (walk π top) ζ R′) ν₁ ν₂ τ)) (≗-trans (proj₁ (proj₂ wg₁) (ν₂ ⨾ τ) R′) (proj₁ (proj₂ wg₂) τ R′))
      where R′ = unsubscribing (Kit.cut (Kit.wkCut τ c₂))

    env₂ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) → wkEnv υ E′ ≡ Here.env (walk π top) → wkEnv (υ ⨾ (ν₁ ⨾ ν₂)) E′ ≡ Here.env (walk π₂ top)
    env₂ E′ υ e = trans (sym (wkEnv-wk υ (ν₁ ⨾ ν₂) E′)) (trans (cong (wkEnv (ν₁ ⨾ ν₂)) e) (trans (sym (wkEnv-wk ν₁ ν₂ _))
                    (trans (cong (wkEnv ν₂) (proj₂ (proj₂ wg₁))) (proj₂ (proj₂ wg₂)))))

    -- The source compiles as the take's body did, under the take's
    -- observer and continuation over the twice-grown walk.
    code′ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) {act} → wkEnv υ E′ ≡ Here.env (walk π top)
          → act ≗ compile s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (Canon.takeWhileO i p c₂ (wkObs (ν₁ ⨾ ν₂) (Here.obs (walk π top)))) kontₖ
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h₂) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {u} E′ υ {act} e c = u , E′ , υ ⨾ (ν₁ ⨾ ν₂)
      , subst (λ W → wkEnv (υ ⨾ (ν₁ ⨾ ν₂)) E′ ≡ Here.env W) (sym walk′) (env₂ E′ υ e)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (takeO-cong i p c₂ obs₂) kont₂))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-take (planted π₂ v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₀
    less = subst (pend t′ <_) (trans (pend-grow ν₂ T₁) (pend-grow ν₁ T₀)) (pend-less π₂ v ≤-refl)

    -- A live take over a pending source holds nothing a call is owed
    -- at, and one pending node: its source.
    inner : Moved.Inner π₂ v (in-take here)
    inner = record { no-of = λ { (in-take ()) } ; no-cold = λ { (in-take ()) } ; one-pend = λ { (in-take here) → refl }
                   ; no-end = λ { (in-take ()) } ; no-cut = λ { (in-take ()) } ; no-feed = λ { (in-take ()) } ; no-fin = λ { (in-take ()) }
                   ; not-self = λ _ () }

    -- The cut's cells are names the tree did not hold.
    take-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    take-fresh fs = fresh-plant π₂ v (pending-↭ v) (((λ ()) ∷ []) ∷ [] ∷ []) (wk-pairs ν₂ T₁ (wk-pairs ν₁ T₀ fs))
      (fresh-new (ν₁ ⨾ ν₂) im ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))
      where
        im : ∀ {m} → m ∈ names T₂ → Img (ν₁ ⨾ ν₂) m
        im m∈ = let (_ , x∈ , e₁) = wk-img ν₂ T₁ m∈ ; (_ , _ , e₀) = wk-img ν₁ T₀ x∈ in to-img (ν₁ ⨾ ν₂) (trans (cong (wkN ν₂) e₀) e₁)

    postulate
      -- The source heads no earlier than the take over it.
      untake     : ∀ {k} {c : U.Node Δ A} → Heads k (U.takeWhileᶜ i p c) → Heads k c

    module _ (H′ : Heapᴹ h₂) (eqv : At.part H′ (pendingˢ (T.takeWhile i p s) q) ≡ At.part H′ v)
             (held : At.val H′ (Kit.held c₂) ≡ nothing) where

      rt-behind : ∀ {k} → Each H′ (Heads k) T₂ → Each H′ (Heads k) t′
      rt-behind {k} = each-plant H′ π₂ v eqv tr
        where
          pa : ∀ {Δ′ A′} {w : Sub h₂ Δ′ A′} → Each H′ (Heads k) (pendingˢ (T.takeWhile i p s) q) → (ψ : Path v w) → seen H′ ψ ≡ true
             → ∀ {c} → At.part H′ w ≡ just c → Heads k c
          pa eu here            _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-take here)  _ refl = untake {c = U.subscribe s q} (Each.parts eu here refl refl)

          tr : Each H′ (Heads k) (pendingˢ (T.takeWhile i p s) q) → Each H′ (Heads k) v
          tr eu = record { parts = pa eu ; pools = λ { (in-take ()) } ; rests = λ { (in-take ()) } }

      rt-kernels : Kernels H′ T₂ → Kernels H′ t′
      rt-kernels kn = record { holds = holds-owed H′ π₂ v tt (Here.kont top) (λ _ → lift held , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                             ; gated = gated-plant H′ π₂ v (λ g → (λ _ → lift tt) , g) (λ _ → lift tt) (Kernels.gated kn)
                             ; settled = settled-plant π₂ v (λ _ → tt) (λ _ → tt , tt) (Kernels.settled kn) }

      -- A take runs what its source runs.
      rt-lingers : Lingers H′ T₂ → Lingers H′ t′
      rt-lingers = lingers-plant H′ π₂ v eqv (λ {C} → rest-pinned (U.restᶜ {B = C} (U.subscribe s q))) (record { pools = λ { (in-take ()) } ; rests = λ { (in-take ()) } })

      rt-meaning : Meaning H′ T₂ → Meaning H′ t′
      rt-meaning mn = record { fed = fed-plant H′ π₂ v (λ _ fd → fd) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₂
      pendings′ with pendings-plant π₂ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rt-queue : ∀ {k clk ts} → Queue H′ k clk ts T₂ → Queue H′ k clk ts t′
      rt-queue {ts = ts} qu =
        record { timed   = subst (At.Timed H′ ts) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H′) (sym (subjects-plant π₂ v refl)) (sym (joiners-plant π₂ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- An allocation's continuation, as a function.
  allocates : ∀ {w B t a} {k′ : ∀ {v} → w ⊑ v → Ref v t → Act v B} {m : Act w B} → m ≗ newRef t a k′
            → Σ (∀ {v} → w ⊑ v → Ref v t → Act v B) λ k₁ → m ≡ newRef t a k₁ × (∀ {v} (σ : w ⊑ v) r → k₁ σ r ≗ k′ σ r)
  allocates (newRef≗ refl f) = _ , refl , f

  -- A takeWhile begun allocates its cut, live and holding nothing, and
  -- begins its source under the take's observer, one subscription fewer
  -- owed.
  take-restage : ∀ {g m} (cr : Carried g m) {Δ A i} {p : A → Bool} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.takeWhile i p s) → Restages cr s
  take-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.takeWhile i p s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl
    with allocates (kk new hereʳ)
  ... | k₁ , e₁ , kk₂ =
    _ , then (cong (λ x → step (Mx x)) e₁) now
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = S.t′
             ; ctlAs = subAs S.π′ (S.code′ E′ υ e (kk₂ new hereʳ)) (S.restack sk₂ a₂) (S.alones _)
             ; meets = trans (part-plant H₂ S.π₂ S.v eqv) (trans (G₂.grow-part gr₂ S.T₁) (trans (G₁.grow-part gr₁ (Carried.tree cr)) (Carried.meets cr)))
             ; owned = Moved.Owning.reowned S.π₂ S.v H₂ eqv (in-take here) S.inner sk₂ a₂
                         (G₂.grow-owned gr₂ {cd′ = cd₂} sk₁ {a′ = a₂} (G₁.grow-owned gr₁ {cd′ = cd₁} sk {a′ = a₁} (Carried.owned cr)))
             ; kernels = S.rt-kernels H₂ eqv refl (G₂.grow-kernels gr₂ (G₁.grow-kernels gr₁ (Carried.kernels cr)))
             ; meaning = S.rt-meaning H₂ eqv refl (G₂.grow-meaning gr₂ (G₁.grow-meaning gr₁ (Carried.meaning cr)))
             ; queue = S.rt-queue H₂ eqv refl (G₂.grow-queue gr₂ (G₁.grow-queue gr₁ (Carried.queue cr)))
             ; books = record { fresh = S.take-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , S.reticked sk₂ a₂ (G₂.grow-ticked sk₁ (G₁.grow-ticked sk (proj₂ (Books.clocked bk))))
                              ; paidUp = cong (mapList (wkTodo new)) (cong (mapList (wkTodo new)) (Books.paidUp bk)) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl (then (cong (λ x → step (Mx x)) e₁) now))
             ; behind = S.rt-behind H₂ eqv refl (G₂.grow-each gr₂ (G₁.grow-each gr₁ (Carried.behind cr)))
             ; lingers = S.rt-lingers H₂ eqv refl (G₂.grow-lingers gr₂ (G₁.grow-lingers gr₁ (Carried.lingers cr))) }
    , refl , inj₁ (inj₁ S.less)
    where module S = Taken {i = i} {p = p} {s = s} π
          module G₁ = Grown S.ν₁
          module G₂ = Grown S.ν₂
          H₁ = extend H (lift true)
          H₂ = extend H₁ (lift nothing)
          Mx : Act (cell (base Bool) ∷ _) ⊤ → Mach
          Mx x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = mapList (wkTodo new) (Mach.todo m₀) }
          gr₁ = grows-extend H (lift true)
          gr₂ = grows-extend H₁ (lift nothing)
          sk₁ = G₁.grow-stack sk
          sk₂ = G₂.grow-stack sk₁
          a₁ = G₁.grow-alone π sk a
          a₂ = G₂.grow-alone S.π₁ sk₁ a₁
          cd₁ = Grown.code-grow S.ν₁ π E′ υ e
          cd₂ = Grown.code-grow S.ν₂ S.π₁ E′ (υ ⨾ S.ν₁) (Grown.env-grow S.ν₁ π E′ υ e)
          eqv : At.part H₂ (pendingˢ (T.takeWhile i p s) _) ≡ At.part H₂ S.v
          eqv = refl
          bk = Carried.books cr

  -- A value under a position keeps its tick.
  tick-ix0 : ∀ r → tick (r ++ [ ix 0 ]) ≡ tick r
  tick-ix0 []           = refl
  tick-ix0 (ix _ ∷ _)   = refl
  tick-ix0 (subᴾ _ ∷ _) = refl
  tick-ix0 (last ∷ _)   = refl

  -- A world grows only longer, so it reaches a larger one one way.
  ⊑-len : ∀ {w v} → w ⊑ v → length w ≤ length v
  ⊑-len same⊑    = ≤-refl
  ⊑-len (grow σ) = m≤n⇒m≤1+n (⊑-len σ)

  ⊑-irrel : ∀ {w v} (σ τ : w ⊑ v) → σ ≡ τ
  ⊑-irrel same⊑    same⊑    = refl
  ⊑-irrel same⊑    (grow τ) = ⊥-elim (<-irrefl refl (⊑-len τ))
  ⊑-irrel (grow σ) same⊑    = ⊥-elim (<-irrefl refl (⊑-len σ))
  ⊑-irrel (grow σ) (grow τ) = cong grow (⊑-irrel σ τ)

  ⊑≗ : ∀ {w v B} (F : w ⊑ v → Act v B) (σ τ : w ⊑ v) → F σ ≗ F τ
  ⊑≗ F σ τ = subst (λ ζ → F σ ≗ F ζ) (⊑-irrel σ τ) (≗-refl (F σ))

  -- A scope, as its two halves.
  unders : ∀ {w B l} {n : Act w B} {x : Act w ⊤} {y : Act w B} → n ≗ under l x y
         → Σ (Act w ⊤) λ x′ → Σ (Act w B) λ y′ → n ≡ under l x′ y′ × x′ ≗ x × y′ ≗ y
  unders (under≗ ex ey) = _ , _ , refl , ex , ey

  -- What is owed reads neither the act a subscription begins with nor how
  -- it was compiled.
  recode : ∀ {h} {H : Heapᴹ h} {t : Sub h [] R} {w Δ A bs} {s : T.Obs Timeline Δ A} {q} {act act′ : Act h ⊤} {σ : w ⊑ h} {K}
             {π : Path t (pendingˢ s q)} {cd cd′} {sk : StackAs t q σ K bs} {a a′}
         → Owned H t (subAs {act = act} π cd sk a) → Owned H t (subAs {act = act′} π cd′ sk a′)
  recode ow = record { ofs = Owned.ofs ow ; plays = Owned.plays ow ; fires = Owned.fires ow ; begun = Owned.begun ow ; ends = Owned.ends ow
                     ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow ; bodies = Owned.bodies ow ; placed = Owned.placed ow }

  -- A RUN AT A PENDING NODE, THE WORLD GROWN: what the relation reads of
  -- the run at its subscription, along the weakened tree and against the
  -- grown heap, the walk to it handing what it handed, weakened.
  record Grew {h₀} (H₀ : Heapᴹ h₀) {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} (π₀ : Path T₀ (pendingˢ s q))
              {u} (E′ : Env Δ u) (υ : u ⊑ h₀) {w} (σ : w ⊑ h₀) (K : Stack w ⊤) (clk : ℕ)
              {h} (ν : h₀ ⊑ h) (H : Heapᴹ h) (bs : List (Maybe (Playing h))) (ts : List (Timer h)) : Set₁ where
    field
      tree    : Sub h [] R
      path    : Path tree (pendingˢ s q)
      stack   : StackAs tree q (σ ⨾ ν) K bs
      alone   : All (λ j → ¬ SrcOf tree path (proj₂ j)) (stackJobs tree stack)
      ticked  : Ticked tree clk stack
      obsR    : ObsRel (wkObs ν (Here.obs (walk π₀ top))) (Here.obs (walk path top))
      kontR   : KontRel (wkKont ν (Here.kont (walk π₀ top))) (Here.kont (walk path top))
      envR    : wkEnv (υ ⨾ ν) E′ ≡ Here.env (walk path top)
      meets   : At.part H tree ≡ At.part H₀ T₀
      owned   : Owned H tree (subAs path (_ , E′ , υ ⨾ ν , envR , ≗-refl _) stack alone)
      kernels : Kernels H tree
      meaning : Meaning H tree
      queue   : Queue H q clk ts tree
      behind  : Each H (Heads q) tree
      lingers : Lingers H tree
      pends   : pend tree ≡ pend T₀
      named   : ∀ {k} {j : h ∋ k} → (k , j) ∈ names tree → Σ (h₀ ∋ k) λ i → wk∋ ν i ≡ j
      distinct : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names tree)

  -- One cell more.
  grew-step : ∀ {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} {π₀ : Path T₀ (pendingˢ s q)}
                {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                {h} {ν : h₀ ⊑ h} {H : Heapᴹ h} {bs ts} {k} (x : Val (k ∷ h) k)
            → Grew H₀ π₀ E′ υ σ K clk ν H bs ts
            → Grew H₀ π₀ E′ υ σ K clk (ν ⨾ new) (extend H x) (mapList (mapMaybe (wkPlaying new)) bs) (mapList (wkTimer new) ts)
  grew-step {π₀ = π₀} {E′ = E′} {υ = υ} {h = h} {ν = ν} {H = H} {k = k} x G = record
    { tree = wkTree new (tree G) ; path = wkPath new (path G) ; stack = Gw.grow-stack (stack G)
    ; alone = Gw.grow-alone (path G) (stack G) (alone G) ; ticked = Gw.grow-ticked (stack G) (ticked G)
    ; obsR = obs-trans (obs-trans (obs-⨾ ν new _) (obs-wk new (obsR G))) (proj₁ wg)
    ; kontR = λ τ sub → ≗-trans (≗-sym (from-⨾ (λ ζ → Here.kont (walk π₀ top) ζ sub) ν new τ)) (≗-trans (kontR G (new ⨾ τ) sub) (proj₁ (proj₂ wg) τ sub))
    ; envR = Gw.env-grow (path G) E′ (υ ⨾ ν) (envR G)
    ; meets = trans (Gw.grow-part gr (tree G)) (meets G)
    ; owned = Gw.grow-owned gr (stack G) (owned G)
    ; kernels = Gw.grow-kernels gr (kernels G) ; meaning = Gw.grow-meaning gr (meaning G) ; queue = Gw.grow-queue gr (queue G)
    ; behind = Gw.grow-each gr (behind G) ; lingers = Gw.grow-lingers gr (lingers G) ; pends = trans (pend-grow new (tree G)) (pends G)
    ; named = λ {_} {j} m → let (i′ , e′ , m′) = names-wk new (tree G) j m ; (i , e) = named G m′
                            in i , trans (sym (wk∋-wk ν new i)) (trans (cong (wk∋ new) e) e′)
    ; distinct = λ fs → wk-pairs new (tree G) (distinct G fs) }
    where open Grew
          module Gw = Grown (new {k} {h})
          gr = grows-extend H x
          wg = Gw.walk-grow (path G)

  -- The world a connect's kernel allocates: its subject's joiners and
  -- closed flag, its cut's flag and stash, the stash of its body's
  -- subscription.
  connectWorld : World → Set → World
  connectWorld h A = cell (maybe quiet) ∷ cell (maybe quiet) ∷ cell (base Bool) ∷ cell (base Bool) ∷ cell (joins A) ∷ h

  connectGrown : ∀ {h A} → h ⊑ connectWorld h A
  connectGrown = grow (grow (grow (grow (grow same⊑))))

  -- A CONNECT RESTAGED IN THE WORLD ITS KERNEL GREW: its subject, flag,
  -- cut and stash the newest cells, its body pending under `ix 0`, its
  -- source pending under `ix 1` and owed back where the connect began.
  module Connected {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A B} {s : T.Obs Timeline Δ A} {b : T.Obs Timeline (A ∷ Δ) B} {q}
                   {π₀ : Path T₀ (pendingˢ (T.connect s b) q)} {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                   {H₅ : Heapᴹ (connectWorld h₀ A)} {bs ts}
                   (G₅ : Grew H₀ π₀ E′ υ σ K clk connectGrown H₅ bs ts)
                   (held₅ : At.val H₅ (Kit.held (Kit.wkCut new (wkR new hereʳ , hereʳ))) ≡ nothing) (body₅ : At.val H₅ hereʳ ≡ nothing) where
    h₅ : World
    h₅ = connectWorld h₀ A

    ν₅ : h₀ ⊑ h₅
    ν₅ = connectGrown

    T₅ : Sub h₅ [] R
    T₅ = Grew.tree G₅

    π₅ : Path T₅ (pendingˢ (T.connect s b) q)
    π₅ = Grew.path G₅

    O : Observer B h₀
    O = Here.obs (walk π₀ top)

    Kt : Kont h₀
    Kt = Here.kont (walk π₀ top)

    S₅ : Subject A h₅
    S₅ = record { subscribers = wkR (grow (grow (grow (grow same⊑)))) hereʳ ; closed = wkR (grow (grow (grow same⊑))) hereʳ }

    c₅ : Kit.Cut h₅
    c₅ = Kit.wkCut new (wkR new hereʳ , hereʳ)

    v : Sub h₅ Δ B
    v = connectˢ S₅ c₅ hereʳ nothing nothing idle (q ++ [ ix 1 ]) nothing (U.subscribe s (q ++ [ ix 1 ])) (pendingˢ s (q ++ [ ix 1 ])) (pendingˢ b (q ++ [ ix 0 ]))

    open Moved π₅ v using (t′; restack; Alone; reticked) public

    ρc : Path t′ v
    ρc = planted π₅ v

    ιb : Path v (pendingˢ b (q ++ [ ix 0 ]))
    ιb = in-body here

    ιs : Path v (pendingˢ s (q ++ [ ix 1 ]))
    ιs = in-source here

    π′ : Path t′ (pendingˢ b (q ++ [ ix 0 ]))
    π′ = ρc ⊕ ιb

    W₅ : Here h₅ Δ B
    W₅ = walk π₅ top

    walkB : walk π′ top ≡ walk ιb W₅
    walkB = trans (walk-⊕ ρc ιb top) (cong (walk ιb) (walk-planted π₅ v top))

    walkS : walk (ρc ⊕ ιs) top ≡ walk ιs W₅
    walkS = trans (walk-⊕ ρc ιs top) (cong (walk ιs) (walk-planted π₅ v top))

    consE : Subject A h₅ → Env Δ h₅ → Env (A ∷ Δ) h₅
    consE = _∷_

    -- The body compiles as the kernel began it, under the body's observer
    -- over the grown walk.
    body-code : ∀ {x} → x ≗ compile b (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) same⊑ (Canon.bodyO c₅ (wkObs ν₅ O)) (bodyK hereʳ)
              → Σ World λ u′ → Σ (Env (A ∷ Δ) u′) λ E″ → Σ (u′ ⊑ h₅) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                  × x ≗ compile b E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    body-code {x} c = _ , consE S₅ (wkEnv (υ ⨾ ν₅) E′) , same⊑
      , subst (λ W → wkEnv same⊑ (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) ≡ Here.env W) (sym walkB) (trans (wkEnv-same _) (cong (consE S₅) (Grew.envR G₅)))
      , subst (λ W → x ≗ compile b (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) same⊑ (Here.obs W) (Here.kont W)) (sym walkB)
          (≗-trans c (compile-cong b _ same⊑ (proj₁ oR , bind≗ (proj₁ (proj₂ oR)) (λ _ → ≗-refl _) , proj₂ (proj₂ oR)) (λ _ _ → ≗-refl _)))
      where oR = Grew.obsR G₅

    -- What the run owes the source, at a walk handing it.
    owedSrc : Here h₅ Δ A → Act h₅ ⊤
    owedSrc W = under (ix 1) (compile s (Here.env W) same⊑ (Here.obs W) (Here.kont W)) skipᴬ

    -- The source compiles as the kernel left it owed, under the subject's
    -- feeder and the source's continuation over the grown walk.
    src-owed : (N : ∀ {v} → h₅ ⊑ v → h₀ ⊑ v) → ∀ {y}
             → y ≗ under (ix 1) (compile s E′ (υ ⨾ ν₅) (Canon.feeder S₅) (srcK c₅ hereʳ (λ ζ → Kt (N ζ)))) skipᴬ
             → wkAct same⊑ y ≗ ⟦ srcC ρc ∷ [] ⟧ᶜ
    src-owed N {y} c =
      ≗-trans (wk-same y) (≗-trans c (≗-trans
        (subst (λ E → under (ix 1) (compile s E′ (υ ⨾ ν₅) (Canon.feeder S₅) (srcK c₅ hereʳ (λ ζ → Kt (N ζ)))) skipᴬ
                    ≗ under (ix 1) (compile s E same⊑ (Canon.feeder S₅) (srcK c₅ hereʳ (Here.kont W₅))) skipᴬ)
               (Grew.envR G₅)
               (under≗ (≗-trans (compile-env s E′ (υ ⨾ ν₅) same⊑) (compile-cong s _ same⊑ fR kR)) (≗-refl skipᴬ)))
        (subst (λ W → owedSrc (walk ιs W₅) ≗ (owedSrc W >>ᴬ skipᴬ)) (sym walkS) (seq-done (owedSrc (walk ιs W₅))))))
      where
        fR : ObsRel (Canon.feeder S₅) (Canon.feeder S₅)
        fR = (λ _ → ≗-refl _) , ≗-refl _ , ≗-refl _

        kr : ∀ {v} (ζ : h₅ ⊑ v) sub → Kt (N ζ) sub ≗ Here.kont W₅ ζ sub
        kr ζ sub = ≗-trans (⊑≗ (λ z → Kt z sub) (N ζ) (ν₅ ⨾ ζ)) (Grew.kontR G₅ ζ sub)

        kR : KontRel (srcK c₅ hereʳ (λ ζ → Kt (N ζ))) (srcK c₅ hereʳ (Here.kont W₅))
        kR ψ sub = bind≗ (≗-refl (Kit.attach (Kit.wkCut ψ c₅) sub)) λ _ → readRef≗ refl λ ψ′ mb → kr (ψ ⨾ ψ′) (unsubscribing (Subscription.unsubscribe (wkSubn ψ′ sub) >>ᴬ Kit.unsubscribeVia mb))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-body ρc ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₅
    less = pend-less π₅ v ≤-refl

    -- A connect over its pending source and body registers nothing, is
    -- owed nothing and holds nothing a feed is owed.
    rc-kernels : Kernels H₅ T₅ → Kernels H₅ t′
    rc-kernels kn = record { holds = holds-owed H₅ π₅ v tt (Here.kont top) (λ _ → lift held₅ , body₅ , lift tt , lift tt , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                           ; gated = gated-plant H₅ π₅ v (λ _ → (λ _ → lift tt) , lift tt , lift tt) (λ _ → lift tt , lift tt) (Kernels.gated kn)
                           ; settled = settled-plant π₅ v (λ _ → tt) (λ _ → tt , tt , tt , tt) (Kernels.settled kn) }

    rc-meaning : Meaning H₅ T₅ → Meaning H₅ t′
    rc-meaning mn = record { fed = fed-plant H₅ π₅ v (λ _ _ → lift tt , lift tt) _ (Meaning.fed mn) }

    -- The subject's, flag's, cut's and stash's cells are names the tree
    -- did not hold.
    connect-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    connect-fresh fs = fresh-plant π₅ v (pending-↭ v) (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ ([]) ∷ []) (Grew.distinct G₅ fs)
      (fresh-new ν₅ (λ { {_ , _} m∈ → Grew.named G₅ m∈ }) ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))

    postulate
      -- Owed across the restage: each node beside the connect or above it
      -- owed as it was, the body the subscription the run begins, the
      -- source the call owed back where the connect began.
      connect-owned  : ∀ {w′ bs′ act act′} {σ′ : w′ ⊑ h₅} {K′} {cd cd′} {m : Act h₅ ⊤} (sk : StackAs T₅ q σ′ K′ bs′) (a : Alone sk) {a′}
                       (e : wkAct same⊑ m ≗ ⟦ srcC ρc ∷ [] ⟧ᶜ)
                     → Owned H₅ T₅ (subAs {act = act} π₅ cd sk a)
                     → Owned H₅ t′ (subAs {act = act′} π′ cd′ (backAs q {ρ = σ′} {σ = same⊑} (srcC ρc ∷ []) (<ᵖ-below q []) e (restack sk a)) a′)
      -- The queue, the run one level down, a new subject joined by none.
      connect-queue  : Queue H₅ q clk ts T₅ → Queue H₅ (q ++ [ ix 0 ]) clk ts t′
      -- Every head no earlier than the run one level down.
      connect-behind : Each H₅ (Heads q) T₅ → Each H₅ (Heads (q ++ [ ix 0 ])) t′

    -- A connect pending its source runs what it was pending to, its
    -- source not yet ended.
    connect-lingers : Lingers H₅ T₅ → Lingers H₅ t′
    connect-lingers = lingers-plant H₅ π₅ v refl
      (union-pinned (bursts-pinned (q ++ [ ix 1 ]) (U.subscribe s (q ++ [ ix 1 ])) (U.step (U.subscribe s (q ++ [ ix 1 ]))))
                    (under-moved (U.live (U.subscribe s (q ++ [ ix 1 ]))) (U.live (U.subscribe s (q ++ [ ix 1 ]))) (rest-pinned (U.subscribe b (q ++ [ ix 0 ])))))
      (record { pools = λ { (in-source ()) ; (in-body ()) } ; rests = λ { here _ _ _ () ; (in-source ()) ; (in-body ()) } })

  -- A connect begun allocates its subject, flag, cut and stash, begins
  -- its body under `ix 0` and owes its source back where it began, one
  -- subscription fewer owed.
  connect-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {s : T.Obs Timeline Δ A} {b : T.Obs Timeline (A ∷ Δ) B}
                  → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.connect s b) → Restages cr b
  connect-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.connect {A = A} s b} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl
    with allocates (kk new hereʳ)
  ... | k₁ , e₁ , kk₁ with allocates (kk₁ new hereʳ)
  ... | k₂ , e₂ , kk₂ with allocates (kk₂ new hereʳ)
  ... | k₃ , e₃ , kk₃ with allocates (kk₃ new hereʳ)
  ... | k₄ , e₄ , kk₄ with unders (kk₄ new hereʳ)
  ... | x′ , y′ , e₅ , ex , ey =
    _ , path
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = C.t′
             ; ctlAs = subAs C.π′ (C.body-code ex) (backAs q₀ (srcC C.ρc ∷ []) (<ᵖ-below q₀ []) eY (C.restack sk₅ a₅)) (C.alones _)
             ; meets = trans (part-plant H₅ C.π₅ C.v refl) (trans (Grew.meets G₅) (Carried.meets cr))
             ; owned = C.connect-owned sk₅ a₅ eY (Grew.owned G₅)
             ; kernels = C.rc-kernels (Grew.kernels G₅) ; meaning = C.rc-meaning (Grew.meaning G₅) ; queue = C.connect-queue (Grew.queue G₅)
             ; books = record { fresh = C.connect-fresh (Books.fresh bk)
                              ; clocked = trans ck (sym (tick-ix0 q₀)) , ck , C.reticked sk₅ a₅ (Grew.ticked G₅)
                              ; paidUp = cong wd (cong wd (cong wd (cong wd (cong wd (Books.paidUp bk))))) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl path) ; behind = C.connect-behind (Grew.behind G₅) ; lingers = C.connect-lingers (Grew.lingers G₅) }
    , refl , inj₁ (inj₁ (subst (pend C.t′ <_) (Grew.pends G₅) C.less))
    where bk = Carried.books cr
          ck = proj₁ (Books.clocked bk)
          wd : ∀ {k w′} → List (Machine.Todo R w′) → List (Machine.Todo R (k ∷ w′))
          wd = mapList (wkTodo new)
          H₁ : Heapᴹ (cell (joins A) ∷ _)
          H₁ = extend H (lift [])
          H₂ : Heapᴹ (cell (base Bool) ∷ _)
          H₂ = extend H₁ (lift false)
          H₃ : Heapᴹ (cell (base Bool) ∷ _)
          H₃ = extend H₂ (lift true)
          H₄ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₄ = extend H₃ (lift nothing)
          H₅ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₅ = extend H₄ (lift nothing)
          G₀ : Grew H π E′ υ σ K (Mach.clock m₀) same⊑ H (Mach.bursts m₀) (Mach.timers m₀)
          G₀ = record { tree = Carried.tree cr ; path = π ; stack = sk ; alone = a ; ticked = proj₂ (Books.clocked bk)
                      ; obsR = (λ _ → wk-same _) , wk-same _ , wk-same _ ; kontR = λ τ sub → from-same (λ ζ → Here.kont (walk π top) ζ sub) τ
                      ; envR = e ; meets = refl ; owned = recode (Carried.owned cr) ; kernels = Carried.kernels cr
                      ; meaning = Carried.meaning cr ; queue = Carried.queue cr ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; pends = refl
                      ; named = λ {_} {j} _ → j , refl ; distinct = λ fs → fs }
          G₅ = grew-step {k = cell (maybe quiet)} (lift nothing) (grew-step {k = cell (maybe quiet)} (lift nothing)
                 (grew-step {k = cell (base Bool)} (lift true) (grew-step {k = cell (base Bool)} (lift false) (grew-step {k = cell (joins A)} (lift []) G₀))))
          module C = Connected G₅ refl refl
          sk₅ = Grew.stack G₅
          a₅ = Grew.alone G₅
          eY = C.src-owed (λ ζ → new ⨾ (new ⨾ ((new ⨾ new) ⨾ (new ⨾ ζ)))) ey
          M₁ : Act (cell (joins A) ∷ _) ⊤ → Mach
          M₁ x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = wd (Mach.todo m₀) }
          M₂ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₂ x = record m₀ { conf = ⟨ H₂ , q₀ , run x ((σ ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₁ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₁ skipᴬ)) ; todo = wd (Mach.todo (M₁ skipᴬ)) }
          M₃ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₃ x = record m₀ { conf = ⟨ H₃ , q₀ , run x (((σ ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₂ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₂ skipᴬ)) ; todo = wd (Mach.todo (M₂ skipᴬ)) }
          M₄ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₄ x = record m₀ { conf = ⟨ H₄ , q₀ , run x ((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₃ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₃ skipᴬ)) ; todo = wd (Mach.todo (M₃ skipᴬ)) }
          M₅ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₅ x = record m₀ { conf = ⟨ H₅ , q₀ , run x (((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₄ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₄ skipᴬ)) ; todo = wd (Mach.todo (M₄ skipᴬ)) }
          path = then (cong (λ x → step (M₁ x)) e₁) (then (cong (λ x → step (M₂ x)) e₂) (then (cong (λ x → step (M₃ x)) e₃)
                   (then (cong (λ x → step (M₄ x)) e₄) (then (cong (λ x → step (M₅ x)) e₅) now))))

  -- A cell the grown world made past its old names, stored to: the run
  -- reads as it did, the tree naming only what the world held before.
  postulate
    grew-store : ∀ {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} {π₀ : Path T₀ (pendingˢ s q)}
                   {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                   {h} {ν : h₀ ⊑ h} {H : Heapᴹ h} {bs ts} {t} (i : Ref h t) (x : Run.El (Pureᴾ R) h t)
               → (∀ (j : Ref h₀ t) → wkR ν j ≢ i)
               → Grew H₀ π₀ E′ υ σ K clk ν H bs ts → Grew H₀ π₀ E′ υ σ K clk ν (store H i (lift x)) bs ts

  -- The world a flatMap's kernel allocates: its count, outer flag, queue,
  -- lanes and refill cell, its outer's cut, the refill's slot.
  flatWorld : World → Set → World
  flatWorld h A = slot ⊤ ∷ cell (maybe quiet) ∷ cell (base Bool) ∷ cell (maybe (sink ⊤)) ∷ cell (list Kit.cutTy) ∷ cell (fifo A)
                ∷ cell (base Bool) ∷ cell (base ℕ) ∷ h

  flatGrown : ∀ {h A} → h ⊑ flatWorld h A
  flatGrown = grow (grow (grow (grow (grow (grow (grow (grow same⊑)))))))

  -- A register's parts, as functions.
  registers : ∀ {w B A} {n′ : A → Act w ⊤} {c′ : Act w ⊤} {x′ : Act w Bool} {k′ : ∀ {v} → w ⊑ v → Sink v A → Act v B} {m : Act w B}
            → m ≗ register n′ c′ x′ k′
            → Σ (A → Act w ⊤) λ n → Σ (Act w ⊤) λ c → Σ (Act w Bool) λ x → Σ (∀ {v} → w ⊑ v → Sink v A → Act v B) λ k
              → m ≡ register n c x k × (∀ a → n a ≗ n′ a) × c ≗ c′ × x ≗ x′ × (∀ {v} (σ : w ⊑ v) r → k σ r ≗ k′ σ r)
  registers (register≗ en ec ex ek) = _ , _ , _ , _ , refl , en , ec , ex , ek

  -- A write's continuation.
  writes : ∀ {w B t} {r : Ref w t} {a} {k′ : Act w B} {m : Act w B} → m ≗ writeRef r a k′ → Σ (Act w B) λ k → m ≡ writeRef r a k × k ≗ k′
  writes (writeRef≗ refl refl ek) = _ , refl , ek

  -- A FLATMAP RESTAGED IN THE WORLD ITS KERNEL GREW: its pool, its
  -- outer's cut and its refill slot the newest entries, the refill cell
  -- holding the slot, its outer pending beneath it, no lane begun.
  module Flatted {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A B} {op : T.FlatOp} {f : A → T.Obs Timeline Δ B} {s : T.Obs Timeline Δ A} {q}
                 {π₀ : Path T₀ (pendingˢ (T.flatMap op f s) q)} {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                 {H₉ : Heapᴹ (flatWorld h₀ A)} {bs ts}
                 (G₉ : Grew H₀ π₀ E′ υ σ K clk flatGrown H₉ bs ts) where
    h₇ h₈ : World
    h₇ = cell (maybe quiet) ∷ cell (base Bool) ∷ cell (maybe (sink ⊤)) ∷ cell (list Kit.cutTy) ∷ cell (fifo A) ∷ cell (base Bool) ∷ cell (base ℕ) ∷ h₀
    h₈ = flatWorld h₀ A

    ν₇ : h₀ ⊑ h₇
    ν₇ = grow (grow (grow (grow (grow (grow (grow same⊑))))))

    ν₈ : h₀ ⊑ h₈
    ν₈ = flatGrown

    O : Observer B h₀
    O = Here.obs (walk π₀ top)

    Kt : Kont h₀
    Kt = Here.kont (walk π₀ top)

    -- The kernel's pool and outer cut, as it allocated them.
    st₇ : FlatKit.Flat A h₇
    st₇ = record { active = wkR (grow (grow (grow (grow (grow (grow same⊑)))))) hereʳ ; outerDone = wkR (grow (grow (grow (grow (grow same⊑))))) hereʳ
                 ; queue = wkR (grow (grow (grow (grow same⊑)))) hereʳ ; lanes = wkR (grow (grow (grow same⊑))) hereʳ ; refill = wkR (grow (grow same⊑)) hereʳ }

    oc₇ : Kit.Cut h₇
    oc₇ = wkR new hereʳ , hereʳ

    f₇ : A → Subscribe B h₇
    f₇ a = wkSub (υ ⨾ ν₇) (compile (f a) E′)

    O₇ : Observer B h₇
    O₇ = wkObs ν₇ O

    module FM₇ = FlatKit.FlatMap op f₇ O₇ st₇

    -- What the kernel hands its outer once the refill slot is stored.
    KO : Observer A h₈
    KO = Kit.guarded (Kit.wkCut new oc₇) (record { next = λ a → wkAct new (FM₇.admit op a)
                                                 ; complete = writeRef (FlatKit.Flat.outerDone (FlatKit.wkFlat new st₇)) true (wkAct new FM₇.settle)
                                                 ; closed = Observer.closed (wkObs new O₇) })

    KK : Kont h₈
    KK τ sub = Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub
               >>ᴬ Kt (ν₇ ⨾ (new ⨾ τ)) (unsubscribing (Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) >>ᴬ wkAct (new ⨾ τ) FM₇.killAll))

    -- The refill slot's callbacks as the kernel registered them.
    kcb : Callbacks ⊤ h₈
    kcb = record { onNext = λ _ → wkAct new FM₇.dequeue ; onComplete = skipᴬ ; isClosed = done false }

    fl₈ : FlatKit.Flat A h₈
    fl₈ = FlatKit.wkFlat new st₇

    oc₈ : Kit.Cut h₈
    oc₈ = Kit.wkCut new oc₇

    T₈ : Sub h₈ [] R
    T₈ = Grew.tree G₉

    π₈ : Path T₈ (pendingˢ (T.flatMap op f s) q)
    π₈ = Grew.path G₉

    W₈ : Here h₈ Δ B
    W₈ = walk π₈ top

    E₈ : Env Δ h₈
    E₈ = Here.env W₈

    O₈ : Observer B h₈
    O₈ = Here.obs W₈

    K₈ : Kont h₈
    K₈ = Here.kont W₈

    v : Sub h₈ Δ B
    v = flatMapˢ op f fl₈ oc₈ nothing hereʳ U.idleᶜ (pendingˢ s q) []

    open Moved π₈ v using (t′; restack; Alone; reticked) public

    ρf : Path t′ v
    ρf = planted π₈ v

    ιo : Path v (pendingˢ s q)
    ιo = in-outer here

    π′ : Path t′ (pendingˢ s q)
    π′ = ρf ⊕ ιo

    walk′ : walk π′ top ≡ walk ιo W₈
    walk′ = trans (walk-⊕ ρf ιo top) (cong (walk ιo) (walk-planted π₈ v top))

    o-rel : ObsRel (wkObs new O₇) O₈
    o-rel = obs-trans (obs-sym (obs-⨾ ν₇ new O)) (Grew.obsR G₉)

    -- The flatMap's kernel, weakened, read as the node's: its admit,
    -- settle and dequeue over the inner programs as the node compiles
    -- them and its observer.
    --
    -- RECOVERY: git show 188b9050f2 restores the inner programs as the kernel subscribes them related to the node's, and the kernel's weakening generic over related inners.
    postulate
      flat-wk-here : (∀ b a → wkAct new (FlatKit.FlatMap.admit op f₇ O₇ st₇ b a) ≗ FlatKit.FlatMap.admit op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇) b a)
                   × wkAct new (FlatKit.FlatMap.settle op f₇ O₇ st₇) ≗ FlatKit.FlatMap.settle op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇)
                   × wkAct new (FlatKit.FlatMap.dequeue op f₇ O₇ st₇) ≗ FlatKit.FlatMap.dequeue op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇)

    outer-rel : ObsRel KO (Canon.Flat′.outerO op f E₈ O₈ fl₈ oc₈)
    outer-rel = guarded-cong oc₈ ((λ a → proj₁ flat-wk-here op a) , writeRef≗ refl refl (proj₁ (proj₂ flat-wk-here)) , proj₂ (proj₂ o-rel))

    kont-rel : KontRel KK (flatK oc₈ fl₈ K₈)
    kont-rel τ sub = bind≗ att λ _ → ≗-trans (⊑≗ (λ z → Kt z U₁) (ν₇ ⨾ (new ⨾ τ)) (ν₈ ⨾ τ)) (≗-trans (Grew.kontR G₉ τ U₁) (walk-kont-sub π₈ τ ue))
      where
        U₁ = unsubscribing (Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) >>ᴬ wkAct (new ⨾ τ) FM₇.killAll)
        cw : Kit.wkCut (new ⨾ τ) oc₇ ≡ Kit.wkCut τ oc₈
        cw = sym (wkEl-wk Kit.cutTy new τ oc₇)
        att : Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub ≗ Kit.attach (Kit.wkCut τ oc₈) sub
        att = subst (λ c → Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub ≗ Kit.attach c sub) cw (≗-refl _)
        ue : Subscription.unsubscribe U₁ ≗ (Kit.cut (Kit.wkCut τ oc₈) >>ᴬ killAllᶜ (FlatKit.wkFlat τ fl₈))
        ue = bind≗ (subst (λ c → Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) ≗ Kit.cut c) cw (≗-refl _)) λ _ →
             subst (λ st → wkAct (new ⨾ τ) FM₇.killAll ≗ killAllᶜ st) (sym (wkFlat-wk new τ st₇)) (killAll-wk (new ⨾ τ) st₇)

    -- The outer compiles as the kernel began it, under the flatMap's
    -- outer observer and continuation over the grown walk.
    code′ : ∀ {act} → act ≗ compile s E′ (υ ⨾ ν₈) KO KK
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h₈) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {act} c = u , E′ , υ ⨾ ν₈
      , subst (λ W → wkEnv (υ ⨾ ν₈) E′ ≡ Here.env W) (sym walk′) (Grew.envR G₉)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ ν₈) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ ν₈) outer-rel kont-rel))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-outer ρf ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₈
    less = pend-less π₈ v (s≤s (≤-reflexive (+-identityʳ _)))

    -- A flatMap over a pending outer and no lane holds nothing a call is
    -- owed at, and one pending node: its outer.
    inner : Moved.Inner π₈ v ιo
    inner = record { no-of = λ { (in-outer ()) ; (in-lanes ()) } ; no-cold = λ { (in-outer ()) ; (in-lanes ()) }
                   ; one-pend = λ { (in-outer here) → refl ; (in-lanes ()) }
                   ; no-end = λ { (in-outer ()) ; (in-lanes ()) } ; no-cut = λ { (in-outer ()) ; (in-lanes ()) }
                   ; no-feed = λ { (in-outer ()) ; (in-lanes ()) } ; no-fin = λ { (in-outer ()) ; (in-lanes ()) }
                   ; not-self = λ _ () }

    -- The pool's, cut's and slot's names are names the tree did not hold.
    flat-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    flat-fresh fs = fresh-plant π₈ v (pending-↭ v) (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ ([]) ∷ [])
      (Grew.distinct G₉ fs) (fresh-new ν₈ (λ { {_ , _} m∈ → Grew.named G₉ m∈ }) ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))

    postulate
      -- The outer heads no earlier than the flatMap over it, no lane begun.
      unflat     : ∀ {k} {c : U.Node Δ A} → Heads k (U.flatMapᶜ op (λ a p → U.subscribe (f a) p) (just c) [] [] U.idleᶜ) → Heads k c

    module _ (eqv : At.part H₉ (pendingˢ (T.flatMap op f s) q) ≡ At.part H₉ v)
             (refill₉ : At.val H₉ (FlatKit.Flat.refill fl₈) ≡ just hereʳ) (slot₉ : CbRel (look H₉ hereʳ) kcb)
             (held₉ : At.val H₉ (Kit.held oc₈) ≡ nothing) (active₉ : At.val H₉ (FlatKit.Flat.active fl₈) ≡ 0)
             (lanes₉ : At.val H₉ (FlatKit.Flat.lanes fl₈) ≡ []) (done₉ : At.val H₉ (FlatKit.Flat.outerDone fl₈) ≡ false) where

      slotR : CbRel (look H₉ hereʳ) (Canon.Flat′.refillCb op f E₈ O₈ fl₈)
      slotR = (λ a → ≗-trans (proj₁ slot₉ a) (proj₂ (proj₂ flat-wk-here))) , proj₁ (proj₂ slot₉) , proj₂ (proj₂ slot₉)

      rf-kernels : Kernels H₉ T₈ → Kernels H₉ t′
      rf-kernels kn = record { holds = holds-owed H₉ π₈ v tt (Here.kont top)
                                         (λ _ → refill₉ , slotR , lift held₉ , lift tt , active₉ , ([] , cong (_++ []) lanes₉ , []) , lift tt)
                                         (Kernels.settled kn) (Kernels.holds kn)
                             ; gated = gated-plant H₉ π₈ v (λ _ → lift tt , lift tt) (λ _ → lift tt , lift tt) (Kernels.gated kn)
                             ; settled = settled-plant π₈ v (λ _ → tt) (λ _ → tt , tt , tt) (Kernels.settled kn) }

      rf-meaning : Meaning H₉ T₈ → Meaning H₉ t′
      rf-meaning mn = record { fed = fed-plant H₉ π₈ v (λ _ _ → lift tt , lift tt) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₈
      pendings′ with pendings-plant π₈ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rf-queue : ∀ {k clk′ ts′} → Queue H₉ k clk′ ts′ T₈ → Queue H₉ k clk′ ts′ t′
      rf-queue {ts′ = ts′} qu =
        record { timed   = subst (At.Timed H₉ ts′) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H₉) (sym (subjects-plant π₈ v refl)) (sym (joiners-plant π₈ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

      rf-behind : ∀ {k} → Each H₉ (Heads k) T₈ → Each H₉ (Heads k) t′
      rf-behind {k} = each-plant H₉ π₈ v eqv tr
        where
          pa : ∀ {Δ′ A′} {x : Sub h₈ Δ′ A′} → Each H₉ (Heads k) (pendingˢ (T.flatMap op f s) q) → (ψ : Path v x) → seen H₉ ψ ≡ true
             → ∀ {c} → At.part H₉ x ≡ just c → Heads k c
          pa eu here             _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-outer here)  _ refl = unflat {c = U.subscribe s q} (Each.parts eu here refl refl)
          pa eu (in-lanes ())

          tr : Each H₉ (Heads k) (pendingˢ (T.flatMap op f s) q) → Each H₉ (Heads k) v
          tr eu = record { parts = pa eu ; pools = λ { here _ _ () ; (in-outer ()) ; (in-lanes ()) } ; rests = λ { (in-outer ()) ; (in-lanes ()) } }

      rf-owned : ∀ {act act′} {cd cd′} {a′} → Owned H₉ T₈ (subAs {act = act} π₈ cd (Grew.stack G₉) (Grew.alone G₉))
               → Owned H₉ t′ (subAs {act = act′} π′ cd′ (restack (Grew.stack G₉) (Grew.alone G₉)) a′)
      rf-owned = Moved.Owning.reowned π₈ v H₉ eqv ιo inner (Grew.stack G₉) (Grew.alone G₉)

      -- A flatMap pending its outer, its pool idle and no lane, runs what
      -- it was pending to.
      rf-lingers : Lingers H₉ T₈ → Lingers H₉ t′
      rf-lingers = lingers-plant H₉ π₈ v eqv (union-pinned (rest-pinned (U.subscribe s q)) unpinned)
        (record { pools = λ { here _ _ → pooled-fresh H₉ {fl = fl₈} {so = pendingˢ s q} done₉ ; (in-outer ()) ; (in-lanes ()) } ; rests = λ { (in-outer ()) ; (in-lanes ()) } })

  -- A flatMap begun allocates its pool and its outer's cut, registers its
  -- refill slot and stores it, and begins its outer under the flatMap's
  -- observer, one subscription fewer owed.
  flat-restage : ∀ {g m} (cr : Carried g m) {Δ A B op} {f : A → T.Obs Timeline Δ B} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.flatMap op f s) → Restages cr s
  flat-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.flatMap {A = A} op f s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl
    with allocates (kk new hereʳ)
  ... | k₁ , e₁ , kk₁ with allocates (kk₁ new hereʳ)
  ... | k₂ , e₂ , kk₂ with allocates (kk₂ new hereʳ)
  ... | k₃ , e₃ , kk₃ with allocates (kk₃ new hereʳ)
  ... | k₄ , e₄ , kk₄ with allocates (kk₄ new hereʳ)
  ... | k₅ , e₅ , kk₅ with allocates (kk₅ new hereʳ)
  ... | k₆ , e₆ , kk₆ with registers (kk₆ new hereʳ)
  ... | n₇ , c₇ , x₇ , k₇ , e₇ , en , ec , ex , ek with writes (ek new hereʳ)
  ... | x₉ , e₈ , ex₉ =
    _ , path
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = F.t′
             ; ctlAs = subAs F.π′ (F.code′ ex₉) (F.restack sk₉ a₉) (F.alones _)
             ; meets = trans (part-plant H₉ F.π₈ F.v refl) (trans (Grew.meets G₉) (Carried.meets cr))
             ; owned = F.rf-owned refl refl slot₉ refl refl refl refl (Grew.owned G₉)
             ; kernels = F.rf-kernels refl refl slot₉ refl refl refl refl (Grew.kernels G₉)
             ; meaning = F.rf-meaning refl refl slot₉ refl refl refl refl (Grew.meaning G₉)
             ; queue = F.rf-queue refl refl slot₉ refl refl refl refl (Grew.queue G₉)
             ; books = record { fresh = F.flat-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , F.reticked sk₉ a₉ (Grew.ticked G₉)
                              ; paidUp = cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (Books.paidUp bk))))))))
                              ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl path) ; behind = F.rf-behind refl refl slot₉ refl refl refl refl (Grew.behind G₉)
             ; lingers = F.rf-lingers refl refl slot₉ refl refl refl refl (Grew.lingers G₉) }
    , refl , inj₁ (inj₁ (subst (pend F.t′ <_) (Grew.pends G₉) F.less))
    where bk = Carried.books cr
          wd : ∀ {k w′} → List (Machine.Todo R w′) → List (Machine.Todo R (k ∷ w′))
          wd = mapList (wkTodo new)
          H₁ : Heapᴹ (cell (base ℕ) ∷ _)
          H₁ = extend H (lift 0)
          H₂ : Heapᴹ (cell (base Bool) ∷ _)
          H₂ = extend H₁ (lift false)
          H₃ : Heapᴹ (cell (fifo A) ∷ _)
          H₃ = extend H₂ (lift [])
          H₄ : Heapᴹ (cell (list Kit.cutTy) ∷ _)
          H₄ = extend H₃ (lift [])
          H₅ : Heapᴹ (cell (maybe (sink ⊤)) ∷ _)
          H₅ = extend H₄ (lift nothing)
          H₆ : Heapᴹ (cell (base Bool) ∷ _)
          H₆ = extend H₅ (lift true)
          H₇ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₇ = extend H₆ (lift nothing)
          H₈ : Heapᴹ (slot ⊤ ∷ _)
          H₈ = extend H₇ (record { onNext = λ a → wkAct new (n₇ a) ; onComplete = wkAct new c₇ ; isClosed = wkAct new x₇ })
          H₉ = store H₈ (wkR (grow (grow (grow same⊑))) hereʳ) (lift (just hereʳ))
          G₀ : Grew H π E′ υ σ K (Mach.clock m₀) same⊑ H (Mach.bursts m₀) (Mach.timers m₀)
          G₀ = record { tree = Carried.tree cr ; path = π ; stack = sk ; alone = a ; ticked = proj₂ (Books.clocked bk)
                      ; obsR = (λ _ → wk-same _) , wk-same _ , wk-same _ ; kontR = λ τ sub → from-same (λ ζ → Here.kont (walk π top) ζ sub) τ
                      ; envR = e ; meets = refl ; owned = recode (Carried.owned cr) ; kernels = Carried.kernels cr
                      ; meaning = Carried.meaning cr ; queue = Carried.queue cr ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; pends = refl
                      ; named = λ {_} {j} _ → j , refl ; distinct = λ fs → fs }
          G₈ = grew-step {k = slot ⊤} (record { onNext = λ a → wkAct new (n₇ a) ; onComplete = wkAct new c₇ ; isClosed = wkAct new x₇ })
                 (grew-step {k = cell (maybe quiet)} (lift nothing) (grew-step {k = cell (base Bool)} (lift true)
                 (grew-step {k = cell (maybe (sink ⊤))} (lift nothing) (grew-step {k = cell (list Kit.cutTy)} (lift [])
                 (grew-step {k = cell (fifo A)} (lift []) (grew-step {k = cell (base Bool)} (lift false) (grew-step {k = cell (base ℕ)} (lift 0) G₀)))))))
          G₉ = grew-store (wkR (grow (grow (grow same⊑))) hereʳ) (just hereʳ) (λ _ ()) G₈
          module F = Flatted G₉
          sk₉ = Grew.stack G₉
          a₉ = Grew.alone G₉
          slot₉ : CbRel (look H₉ hereʳ) F.kcb
          slot₉ = (λ a → ≗-trans (wk-same _) (wk≗ new (en a))) , ≗-trans (wk-same _) (wk≗ new ec) , ≗-trans (wk-same _) (wk≗ new ex)
          M₁ : Act (cell (base ℕ) ∷ _) ⊤ → Mach
          M₁ x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = wd (Mach.todo m₀) }
          M₂ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₂ x = record m₀ { conf = ⟨ H₂ , q₀ , run x ((σ ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₁ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₁ skipᴬ)) ; todo = wd (Mach.todo (M₁ skipᴬ)) }
          M₃ : Act (cell (fifo A) ∷ _) ⊤ → Mach
          M₃ x = record m₀ { conf = ⟨ H₃ , q₀ , run x (((σ ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₂ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₂ skipᴬ)) ; todo = wd (Mach.todo (M₂ skipᴬ)) }
          M₄ : Act (cell (list Kit.cutTy) ∷ _) ⊤ → Mach
          M₄ x = record m₀ { conf = ⟨ H₄ , q₀ , run x ((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₃ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₃ skipᴬ)) ; todo = wd (Mach.todo (M₃ skipᴬ)) }
          M₅ : Act (cell (maybe (sink ⊤)) ∷ _) ⊤ → Mach
          M₅ x = record m₀ { conf = ⟨ H₅ , q₀ , run x (((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₄ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₄ skipᴬ)) ; todo = wd (Mach.todo (M₄ skipᴬ)) }
          M₆ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₆ x = record m₀ { conf = ⟨ H₆ , q₀ , run x ((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₅ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₅ skipᴬ)) ; todo = wd (Mach.todo (M₅ skipᴬ)) }
          M₇ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₇ x = record m₀ { conf = ⟨ H₇ , q₀ , run x (((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₆ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₆ skipᴬ)) ; todo = wd (Mach.todo (M₆ skipᴬ)) }
          M₈ : Act (slot ⊤ ∷ _) ⊤ → Mach
          M₈ x = record m₀ { conf = ⟨ H₈ , q₀ , run x ((((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₇ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₇ skipᴬ)) ; todo = wd (Mach.todo (M₇ skipᴬ)) }
          path = then (cong (λ x → step (M₁ x)) e₁) (then (cong (λ x → step (M₂ x)) e₂) (then (cong (λ x → step (M₃ x)) e₃) (then (cong (λ x → step (M₄ x)) e₄) (then (cong (λ x → step (M₅ x)) e₅) (then (cong (λ x → step (M₆ x)) e₆) (then (cong (λ x → step (M₇ x)) e₇) (then (cong (λ x → step (M₈ x)) e₈) now)))))))
