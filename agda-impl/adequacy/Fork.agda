{-# OPTIONS --guardedness #-}

-- A PENDING NODE PLANTED OVER: where a path of the old tree sits against
-- it, and where a call aimed along one lands in the new tree.  A call's
-- code reads only its node's fields and the walk to it, and a walk reads
-- no node's children.
module adequacy.Fork where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (+-monoʳ-<; +-monoˡ-<)
open import Data.Product using (_×_; _,_; Σ; proj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.MonotonicList.Events using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Unsub using (module Unsubbing)

module Forking (R : Set) where
  open Unsubbing R using (then)
  open Shared Timeline (Out R) using (⟨_,_,_⟩)
  open Heap using (there)
  open Run (Pureᴾ R) using (done)
  open Strongly R using (Sub; pendingˢ; ofˢ; takeWhileˢ; connectˢ; Lane; ending; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf; Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; code; Phase; lane)
  open StrongAgainst R using (Spot; spot; Job)
  open StrongAgainst.Against R using (CtlAs; subAs; sources)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pend; pendᴸ)
  open GhostingPaths R using (walk-⊕)

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
