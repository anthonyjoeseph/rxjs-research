{-# OPTIONS --guardedness #-}

-- A PENDING NODE RESTAGED: the tree with it replaced, every call the run
-- owes carried across.  A call aimed beside the node, or at an ancestor,
-- aims at the same fields in the new tree; one aimed at the node itself
-- is a connect's `srcC` owing its source, which the control rules out.
module adequacy.Moved where

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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)

module Planting (R : Set) where
  open Unsubbing R using (then)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack)
  open Heap using (_⊑_; there)
  open Run (Pureᴾ R) using (done; _>>ᴬ_; wkAct; module Kit)
  open Strongly R using (Sub; pendingˢ; ofˢ; takeWhileˢ; connectˢ; ending; taken; feeding; finishing; Path; here; in-take; in-source; in-body; _⊕_; top; Call; emitC; kontC; spot; coldˢ; take1C; take2C; bodyC; feedC; finC; srcC; code; Job; _≗_; module At; Owned; Phase)
                        renaming (⟦_⟧ to ⟦_⟧ᶜ; at⟦_⟧ to at⟦_⟧ᶜ)
  open Strongly.Against R using (CtlAs; StackAs; BurstAs; subAs; bottomAs; restAs; backAs; reholdAs; Held; bottomᴴ; restᴴ; playsAs; firesAs; overAs; stackJobs; SrcOf; src-of; Ticked; BurstClocked; sources; burstSpots; stackBursts; Placed; agenda)
  open Strongly.Phase R using (playing; fired)
  open Moving R using (plant; planted; part-plant; same; same-take; same-connect)
  open Forking R using (ExtS; Lands; SrcAt; apart; below; emit-code; exts; exts-apart; fork; kont-code; lands-apart; lands-below; lands-planted; lands-unique; leaf-below; sources-mem; src-at; src-code; src-mem; src-spot; take1-code)
  open Keeping R using (keep)

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
