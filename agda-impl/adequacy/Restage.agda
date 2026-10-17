{-# OPTIONS --guardedness #-}

-- A PENDING NODE RESTAGED: the tree with it replaced, every call the run
-- owes carried across.  A call's code reads only its node's fields and
-- the walk to it, and a walk reads no node's children, so a call aimed
-- beside the node, or at an ancestor, aims at the same fields in the new
-- tree; one aimed at the node itself is a connect's `srcC` owing its
-- source, which the control rules out.
module adequacy.Restage where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; _<_; _≤_; _+_)
open import Data.Nat.Properties using (≤-refl; +-monoʳ-<; +-monoˡ-<; m≤n⇒m≤1+n; <-irrefl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; _∧_; _∨_; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; <ᵖ-below)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Frame using (module Framing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; quiet; joins)
open import operation.PureObservable using (module Pure)

module Restaging (R : Set) where
  open Machine R using (Mach; mach; step; silent; Playing; wkPlaying; wkTodo)
  open Unsubbing R using (_⇝_; now; then; ≗-trans; wk≗; bind≗; wk-same; wkEnv-same; from-same)
  open Growing R using (wkTree; wkLanes; wkPath)
  open Sequencing R using (wkEnv-wk; wk-wk; from-⨾; seq-done)
  open Pure R using (Timer; wkTimer; mapList)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack; run; Val; extend; look; cbs; wkVal)
  open Heap using (World; _⊑_; _⨾_; new; grow; wk∋; cell; slot; Sink; Quiet; Handle) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; newRef; under; readRef; _>>ᴬ_; compile; Env; wkEnv; wkAct; module Kit; Ref; wkR; wkEl; Observer; Kont; wkObs; wkKont; Subject)
  open Run.Kit (Pureᴾ R) using (skipᴬ)
  open Strongly R using (Carried; Books; carried; Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; ending; taken; idle; feeding; finishing; bodyK; srcK
                        ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane
                        ; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf
                        ; Call; emitC; kontC; Spot; spot; coldˢ; take1C; take2C; bodyC; feedC; finC; srcC; code; Job; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Heads; names; pendings
                        ; seen; seenL; seen-⊕; isTaking; ∧-split; flatMapˢ; scanˢ; joinˢ; doneˢ; deferˢ; lane; CbRel; ≗-refl; newRef≗; taking; takeK; unsubscribing; done≗; register≗; send≗; finish≗; startCold≗; stop≗; stash≗; cancel≗; eff≗; here≗; under≗; diverge≗; unfold≗; readRef≗; writeRef≗; module Canon)
                        renaming (⟦_⟧ to ⟦_⟧ᶜ; at⟦_⟧ to at⟦_⟧ᶜ)
  open Strongly.Against R using (CtlAs; StackAs; BurstAs; subAs; bottomAs; restAs; backAs; reholdAs; Held; bottomᴴ; restᴴ; playsAs; firesAs; overAs; stackJobs; SrcOf; src-of; Ticked; BurstClocked; sources; burstSpots; stackBursts; Placed; agenda)
  open Strongly.Phase R using (playing; fired)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pend; pendᴸ; part-plant; names-plant; holds-plant; holds-owed; settled-plant; gated-plant; fed-plant; pendings-plant; subjects-plant; joiners-plant
                     ; Same; same; same-map; same-scan; same-take; same-flat; same-connect; same-defer)
  open Ghosting R using (walk-⊕; _≺_; measure; each-sub; sorted-⇝)
  open Framing R using (head-map; head-scan)

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
    wrap-body : ∀ {Δ A B} {s : T.Obs Timeline (A ∷ Δ) B} {q} {S c b kb k fd e rp rt} {src : Sub h Δ A}
              → Wrap (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd = pendingˢ s q} here)

  wrap-here : ∀ {h Δ A Δ₁ B C} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι
            → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A ∷ Δ) C} (β : Path u (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd)) → ι ≢ β ⊕ in-source here
  wrap-here wrap-map  (in-map ())
  wrap-here wrap-scan (in-scan ())
  wrap-here wrap-take (in-take ())
  wrap-here wrap-body (in-source _) ()
  wrap-here wrap-body (in-body ())

  wrap-src : ∀ {h Δ A Δ₁ B} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι → Path (pendingˢ s q) u → ⊥
  wrap-src wrap-map  ()
  wrap-src wrap-scan ()
  wrap-src wrap-take ()
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
           ; sorted = Carried.sorted cr ; behind = M.rm-behind H (Carried.behind cr) }
    , refl , inj₁ (inj₁ M.less)
    where module M = Mapped π
          module N = Moved π M.v
          bk = Carried.books cr

  -- A KERNEL BEGUN BY ALLOCATING: its cells allocated, its node planted
  -- in the grown world, the run at the subscription the kernel begins
  -- next, carried, one subscription fewer owed.
  Restages : ∀ {g m} → Carried g m → ∀ {Δ A} → T.Obs Timeline Δ A → Set₁
  Restages {g} {m} cr {Δ} {A} s = ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₀ → m′ ⇝ m₀ × Σ (Carried g m₀) λ cr′
                                  → subOf (Carried.ctlAs cr′) ≡ just (Δ , A , s) × measure (carried cr′) ≺ measure (carried cr)

  postulate
    -- A flatMap allocates its pool and begins its outer.
    flat-restage    : ∀ {g m} (cr : Carried g m) {Δ A B op} {f : A → T.Obs Timeline Δ B} {s : T.Obs Timeline Δ A}
                    → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.flatMap op f s) → Restages cr s

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

    module _ {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
      postulate
        grow-part    : ∀ {Δ A} (u : Sub h Δ A) → At.part H′ (wkTree τ u) ≡ At.part H u
        grow-owned   : ∀ {t : Sub h [] R} {w} {σ : w ⊑ h} {K bs} {Δ A s q} {π : Path t (pendingˢ {Δ = Δ} {A} s q)} {act act′ cd cd′}
                         (sk : StackAs t q σ K bs) {a a′}
                     → Owned H t (subAs {act = act} π cd sk a) → Owned H′ (wkTree τ t) (subAs {act = act′} (wkPath τ π) cd′ (grow-stack sk) a′)
        grow-kernels : ∀ {t : Sub h [] R} → Kernels H t → Kernels H′ (wkTree τ t)
        grow-meaning : ∀ {t : Sub h [] R} → Meaning H t → Meaning H′ (wkTree τ t)
        grow-queue   : ∀ {t : Sub h [] R} {p clk ts} → Queue H p clk ts t → Queue H′ p clk (mapList (wkTimer τ) ts) (wkTree τ t)
        grow-each    : ∀ {t : Sub h [] R} {P : ∀ {Γ A} → U.Node Γ A → Set} → Each H P t → Each H′ P (wkTree τ t)

  postulate
    -- An allocation grows the world and moves nothing.
    grows-extend : ∀ {h k} (H : Heapᴹ h) (x : Val (k ∷ h) k) → Grows new H (extend H x)

    -- A compiled subscription read alike under alike observers and
    -- continuations.
    compile-cong : ∀ {Γ A u w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ w) {o o′ : Observer A w} {k k′ : Kont w}
                 → ObsRel o o′ → KontRel k k′ → compile s E υ o k ≗ compile s E υ o′ k′

    -- A compiled subscription reads its subjects weakened to the world it
    -- runs at, whichever stretch of the weakening they were carried along.
    compile-env : ∀ {Γ A u v w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ v) (ρ : v ⊑ w) {o : Observer A w} {k : Kont w}
                → compile s E (υ ⨾ ρ) o k ≗ compile s (wkEnv υ E) ρ o k

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

    postulate
      -- The accumulator is a name the tree did not hold.
      scan-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)

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
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl now) ; behind = S.rs-behind H′ eqv (G.grow-each gr (Carried.behind cr)) }
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

    postulate
      -- The cut's cells are names the tree did not hold.
      take-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
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
      rt-kernels kn = record { holds = holds-owed H′ π₂ v tt (λ _ → lift held , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                             ; gated = gated-plant H′ π₂ v (λ g → (λ _ → lift tt) , g) (λ _ → lift tt) (Kernels.gated kn)
                             ; settled = settled-plant π₂ v (λ _ → tt) (λ _ → tt , tt) (Kernels.settled kn) }

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
             ; behind = S.rt-behind H₂ eqv refl (G₂.grow-each gr₂ (G₁.grow-each gr₁ (Carried.behind cr))) }
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
      pends   : pend tree ≡ pend T₀

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
    ; behind = Gw.grow-each gr (behind G) ; pends = trans (pend-grow new (tree G)) (pends G) }
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
        kR ψ sub = bind≗ (≗-refl (Kit.attach (Kit.wkCut ψ c₅) sub)) λ _ → readRef≗ refl λ ψ′ mb → kr (ψ ⨾ ψ′) _

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-body ρc ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₅
    less = pend-less π₅ v ≤-refl

    -- A connect over its pending source and body registers nothing, is
    -- owed nothing and holds nothing a feed is owed.
    rc-kernels : Kernels H₅ T₅ → Kernels H₅ t′
    rc-kernels kn = record { holds = holds-owed H₅ π₅ v tt (λ _ → lift held₅ , body₅ , lift tt , lift tt , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                           ; gated = gated-plant H₅ π₅ v (λ _ → (λ _ → lift tt) , lift tt , lift tt) (λ _ → lift tt , lift tt) (Kernels.gated kn)
                           ; settled = settled-plant π₅ v (λ _ → tt) (λ _ → tt , tt , tt , tt) (Kernels.settled kn) }

    rc-meaning : Meaning H₅ T₅ → Meaning H₅ t′
    rc-meaning mn = record { fed = fed-plant H₅ π₅ v (λ _ _ → lift tt , lift tt) _ (Meaning.fed mn) }

    postulate
      -- The subject's, flag's, cut's and stash's cells are names the tree
      -- did not hold.
      connect-fresh  : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
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
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl path) ; behind = C.connect-behind (Grew.behind G₅) }
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
                      ; meaning = Carried.meaning cr ; queue = Carried.queue cr ; behind = Carried.behind cr ; pends = refl }
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
