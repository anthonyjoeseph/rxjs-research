{-# OPTIONS --guardedness #-}

-- A PENDING NODE RESTAGED: the tree with it replaced, every call the run
-- owes carried across.  A call's code reads only its node's fields and
-- the walk to it, and a walk reads no node's children, so a call aimed
-- beside the node, or at an ancestor, aims at the same fields in the new
-- tree; one aimed at the node itself is a connect's `srcC` owing its
-- source, which the control rules out.
module adequacy.Restage where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl; +-monoʳ-<; +-monoˡ-<)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Timeline)
import Tree as T
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost using (module Ghosting)

module Restaging (R : Set) where
  open Machine R using (Mach; mach)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack)
  open Heap using (World; _⊑_)
  open Run (Pureᴾ R) using (_>>ᴬ_; compile; Env; wkEnv; wkAct)
  open Strongly R using (Carried; Books; carried; Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; ending; taken; feeding; finishing
                        ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane
                        ; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf
                        ; Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; code; Job; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Heads; names; pendings)
                        renaming (⟦_⟧ to ⟦_⟧ᶜ; at⟦_⟧ to at⟦_⟧ᶜ)
  open Strongly.Against R using (CtlAs; StackAs; BurstAs; subAs; bottomAs; restAs; backAs; reholdAs; Held; bottomᴴ; restᴴ; playsAs; firesAs; overAs; stackJobs; SrcOf; src-of; Ticked; BurstClocked)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pend; pendᴸ; part-plant; names-plant; holds-plant; gated-plant; fed-plant; pendings-plant; subjects-plant; joiners-plant)
  open Ghosting R using (walk-⊕; _≺_; measure)

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

  ------------------------------------------------------------------------
  -- A map restaged: its source pending beneath it

  -- A path ending under a map ends under no connect's source.
  mutual
    map-not-src : ∀ {h Δ A Δ₀ A₀ B₀ C₀} {t : Sub h Δ A} {f : A₀ → B₀} {s : T.Obs Timeline Δ₀ A₀} {q} {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
                  (α : Path t (mapˢ f (pendingˢ s q))) (β : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
                → α ⊕ in-map here ≢ β ⊕ in-source here
    map-not-src here         (in-map ())   _
    map-not-src (in-map α)   (in-map β)    eq = map-not-src α β (in-map-inj eq)
      where in-map-inj : ∀ {x y} → in-map x ≡ in-map y → x ≡ y
            in-map-inj refl = refl
    map-not-src (in-scan α)  (in-scan β)   eq = map-not-src α β (in-scan-inj eq)
      where in-scan-inj : ∀ {x y} → in-scan x ≡ in-scan y → x ≡ y
            in-scan-inj refl = refl
    map-not-src (in-take α)  (in-take β)   eq = map-not-src α β (in-take-inj eq)
      where in-take-inj : ∀ {x y} → in-take x ≡ in-take y → x ≡ y
            in-take-inj refl = refl
    map-not-src (in-outer α) (in-outer β)  eq = map-not-src α β (in-outer-inj eq)
      where in-outer-inj : ∀ {x y} → in-outer x ≡ in-outer y → x ≡ y
            in-outer-inj refl = refl
    map-not-src (in-outer α) (in-lanes β)  ()
    map-not-src (in-lanes α) (in-outer β)  ()
    map-not-src (in-lanes α) (in-lanes β)  eq = map-not-srcᴸ α β (in-lanes-inj eq)
      where in-lanes-inj : ∀ {x y} → in-lanes x ≡ in-lanes y → x ≡ y
            in-lanes-inj refl = refl
    map-not-src (in-source ()) here        _
    map-not-src (in-source α) (in-source β) eq = map-not-src α β (in-source-inj eq)
      where in-source-inj : ∀ {x y} → in-source x ≡ in-source y → x ≡ y
            in-source-inj refl = refl
    map-not-src (in-source α) (in-body β)  ()
    map-not-src (in-body α)  here          ()
    map-not-src (in-body α)  (in-source β) ()
    map-not-src (in-body α)  (in-body β)   eq = map-not-src α β (in-body-inj eq)
      where in-body-inj : ∀ {x y} → in-body x ≡ in-body y → x ≡ y
            in-body-inj refl = refl
    map-not-src (in-defer α) (in-defer β)  eq = map-not-src α β (in-defer-inj eq)
      where in-defer-inj : ∀ {x y} → in-defer x ≡ in-defer y → x ≡ y
            in-defer-inj refl = refl

    map-not-srcᴸ : ∀ {h Δ B Δ₀ A₀ B₀ C₀} {ls : List (Lane h Δ B)} {f : A₀ → B₀} {s : T.Obs Timeline Δ₀ A₀} {q} {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
                   (α : PathLanes ls (mapˢ f (pendingˢ s q))) (β : PathLanes ls (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
                 → α ⊕ᴸ in-map here ≢ β ⊕ᴸ in-source here
    map-not-srcᴸ (this-lane α) (this-lane β) eq = map-not-src α β (this-inj eq)
      where this-inj : ∀ {x y} → this-lane x ≡ this-lane y → x ≡ y
            this-inj refl = refl
    map-not-srcᴸ (this-lane α) (next-lane β) ()
    map-not-srcᴸ (next-lane α) (this-lane β) ()
    map-not-srcᴸ (next-lane α) (next-lane β) eq = map-not-srcᴸ α β (next-inj eq)
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
    alone (src-of ρ e) = map-not-src (planted π v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    part′ : ∀ (H : Heapᴹ h) → At.part H t′ ≡ At.part H T₀
    part′ H = part-plant H π v refl

    names′ : names t′ ≡ names T₀
    names′ = names-plant π v refl

    less : pend t′ < pend T₀
    less = pend-less π v ≤-refl

    postulate
      -- What the relation reads of a pending map it reads alike of the
      -- map over its pending source.
      rm-owned   : ∀ {w bs act} {σ : w ⊑ h} {K} {cd cd′} (H : Heapᴹ h) (sk : StackAs T₀ q σ K bs) (a : Alone sk) {a′}
                 → Owned H T₀ (subAs {act = act} π cd sk a) → Owned H t′ (subAs {act = act} π′ cd′ (restack sk a) a′)
      rm-behind  : ∀ (H : Heapᴹ h) {p} → Each H (Heads p) T₀ → Each H (Heads p) t′

    -- A pending node and a map over one register nothing, queue nothing
    -- and are owed nothing.
    rm-kernels : (H : Heapᴹ h) → Kernels H T₀ → Kernels H t′
    rm-kernels H kn = record { holds = holds-plant H π v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H π v (λ g → g) (λ d → d) (Kernels.gated kn) }

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
