{-# OPTIONS --guardedness #-}

-- EVERY NODE IN ORDER, rests and their sources included: `Placed`
-- looks at no node under a rest, a union, a burst or an ended source, so
-- the order a run's rests keep is carried beside it.  A connect is in
-- order as its source's burst is, so every piece of every cut is, and a
-- node's cut is in order by its pieces' alone.
module adequacy.Deep where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline; ix; end; root)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
import denotation.MonotonicList as M′
open import denotation.MonotonicList.Events using (Tail; Tail∞; pin; idle)
open import adequacy.Placed.Order using (Ordered; Reaches; Headed; Sorted; Alienᴱ; Atop; ordered)
open import adequacy.Placed.Rising using (AtopT)
open import adequacy.Placed.Trail using (SortedT; sortedᵀ; sortedT-idle; sortedT-∪)
open import adequacy.Placed.Burst using (ordered-tail)

open Tail∞

mutual
  Deep : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Deep c ρ = Ordered (U.meaning c ρ) × Deeps c ρ

  Deeps : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  Deeps (U.mapᶜ f c)                    ρ = Deep c ρ
  Deeps (U.scanᶜ f z c)                 ρ = Deep c ρ
  Deeps (U.takeWhileᶜ i p c)            ρ = Deep c ρ
  Deeps (U.flatMapᶜ op g o ls qs pl)    ρ = Deepᴹ o ρ × Deepᴸ ls ρ × Deep pl ρ
    × (∀ a x → Reaches (x ++ [ ix 0 ]) (U.meaning (U.flatMapᶜ op g o ls qs pl) ρ) → Deep (g a (x ++ [ ix 1 ])) ρ)
  Deeps (U.connectᶜ r b (U.live s))    ρ = Deep b (U.meaning s ρ ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r s) ρ) × Deep s ρ
  Deeps (U.connectᶜ r b (U.ended c t)) ρ = Deep b (end c ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  Deeps (U.deferᶜ l p ns)               ρ = Headed p × Sorted (U.replay ns ρ) × Alienᴱ p (U.replay ns ρ)
  Deeps (U.endingᶜ p n)                 ρ = Deep n ρ
  Deeps (U.restᶜ n)                     ρ = DeepR n ρ
  Deeps (U.unionᶜ x y)                  ρ = Deep x ρ × Deep y ρ
  Deeps (U.burstingᶜ r t)               ρ = Deep t ρ
  Deeps (U.underᶜ (U.live s) b)         ρ = Deep s ρ × Deep b (U.meaning s ρ ∷ ρ)
  Deeps (U.underᶜ (U.ended c t) b)      ρ = Deep t ρ × Deep b (end c ∷ ρ)
  Deeps _                               ρ = ⊤

  Deepᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  Deepᴹ nothing  ρ = ⊤
  Deepᴹ (just c) ρ = Deep c ρ

  Deepᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  Deepᴸ []       ρ = ⊤
  Deepᴸ (c ∷ cs) ρ = Deep c ρ × Deepᴸ cs ρ

  -- What a node's rest runs, in order to every depth: the parts its
  -- rest keeps running, never what it would subscribe next.
  DeepR : ∀ {Γ A} → U.Node Γ A → NEnv Γ → Set
  DeepR (U.mapᶜ f c)                    ρ = DeepR c ρ
  DeepR (U.scanᶜ f z c)                 ρ = DeepR c ρ
  DeepR (U.takeWhileᶜ i p c)            ρ = DeepR c ρ
  DeepR (U.flatMapᶜ op g o ls qs pl)    ρ = DeepRᴹ o ρ × DeepRᴸ ls ρ × DeepR pl ρ
  DeepR (U.connectᶜ r b (U.live s))    ρ = DeepR b (U.meaning s ρ ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r s) ρ) × Deep s ρ
  DeepR (U.connectᶜ r b (U.ended c t)) ρ = DeepR b (end c ∷ ρ) × Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  DeepR (U.endingᶜ p n)                 ρ = DeepR n ρ
  DeepR (U.restᶜ n)                     ρ = DeepR n ρ
  DeepR (U.unionᶜ x y)                  ρ = DeepR x ρ × DeepR y ρ
  DeepR (U.burstingᶜ r t)               ρ = Ordered (U.meaning (U.burstingᶜ {B = ⊤} r t) ρ) × Deep t ρ
  DeepR (U.underᶜ (U.live s) b)         ρ = Deep s ρ × DeepR b (U.meaning s ρ ∷ ρ)
  DeepR (U.underᶜ (U.ended c t) b)      ρ = Deep t ρ × DeepR b (end c ∷ ρ)
  DeepR _                               ρ = ⊤

  DeepRᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → NEnv Γ → Set
  DeepRᴹ nothing  ρ = ⊤
  DeepRᴹ (just c) ρ = DeepR c ρ

  DeepRᴸ : ∀ {Γ A} → List (U.Node Γ A) → NEnv Γ → Set
  DeepRᴸ []       ρ = ⊤
  DeepRᴸ (c ∷ cs) ρ = DeepR c ρ × DeepRᴸ cs ρ

-- What a step leaves in order to every depth.
Deepˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Deepˢ ρ (U.outˢ k a c) = Deep c ρ
Deepˢ ρ (U.skipˢ k c)  = Deep c ρ
Deepˢ ρ (U.endˢ k)     = ⊤
Deepˢ ρ U.hushˢ        = ⊤

-- A tail in order as its run of skips is.
atop-tailT : ∀ {A} k t → Atop k (M′.tailᴱ {A} t) → AtopT k t
atop-tailT k (pin h _) a = a
atop-tailT k idle      a = tt

-- A tail runs in order whatever it is read as.
atop-tail : ∀ {A B} k (t : Tail) → Atop k (M′.tailᴱ {A} t) → Atop k (M′.tailᴱ {B} t)
atop-tail k (pin _ _) a = a
atop-tail k idle      a = a

ordered-retyped : ∀ {A B} (t : Tail) → Ordered (M′.tailᴱ {A} t) → Ordered (M′.tailᴱ {B} t)
ordered-retyped (pin k r) o .ordered = atop-tail k (later r) (proj₁ (ordered o)) , ordered-retyped (later r) (proj₂ (ordered o))
ordered-retyped idle      o .ordered = tt

tail-sorted : ∀ {A} t → Ordered (M′.tailᴱ {A} t) → SortedT t
sortedᵀ (tail-sorted (pin k u) o) = atop-tailT k (later u) (proj₁ (ordered o)) , tail-sorted (later u) (proj₂ (ordered o))
sortedᵀ (tail-sorted idle      o) = tt

-- A node's rest in order leaves its cut in order.
mutual
  deep-cutR : ∀ {Γ A} (c : U.Node Γ A) {ρ} → DeepR c ρ → SortedT (U.cutᴺ c ρ)
  deep-cutR (U.framesᶜ _ _ _)                    d = sortedT-idle
  deep-cutR (U.burstᶜ _ _ _ _)                   d = sortedT-idle
  deep-cutR (U.ofᶜ _ _ _)                        d = sortedT-idle
  deep-cutR (U.mapᶜ _ c)                         d = deep-cutR c d
  deep-cutR (U.scanᶜ _ _ c)                      d = deep-cutR c d
  deep-cutR (U.takeWhileᶜ _ _ c)                 d = deep-cutR c d
  deep-cutR (U.flatMapᶜ _ g o ls _ pl)           (dᵒ , dl , dp) =
    sortedT-∪ _ _ (deep-cutRᴼ g o dᵒ) (sortedT-∪ _ _ (deep-cutRᴸ ls dl) (deep-cutR pl dp))
  deep-cutR (U.joinᶜ _ _ _ _)                    d = sortedT-idle
  deep-cutR (U.connectᶜ r b (U.live s))          (db , ob , _) = sortedT-∪ _ _ (tail-sorted _ ob) (deep-cutR b db)
  deep-cutR (U.connectᶜ r b (U.ended c t))       (db , ob , _) = sortedT-∪ _ _ (tail-sorted _ ob) (deep-cutR b db)
  deep-cutR (U.deferᶜ _ _ _)                     d = sortedT-idle
  deep-cutR (U.endingᶜ _ n)                      d = deep-cutR n d
  deep-cutR (U.restᶜ n)                          d = deep-cutR n d
  deep-cutR U.idleᶜ                              d = sortedT-idle
  deep-cutR (U.unionᶜ x y)                       (dx , dy) = sortedT-∪ _ _ (deep-cutR x dx) (deep-cutR y dy)
  deep-cutR (U.burstingᶜ r t)                    (o , _) = tail-sorted _ o
  deep-cutR (U.underᶜ (U.live s) b)              (_ , db) = deep-cutR b db
  deep-cutR (U.underᶜ (U.ended c t) b)           (_ , db) = deep-cutR b db

  deep-cutRᴼ : ∀ {Γ A B} (g : A → _ → U.Node Γ B) (o : Maybe (U.Node Γ A)) {ρ} → DeepRᴹ o ρ → SortedT (M′.cutᴼ (U.outerᴺ g o ρ))
  deep-cutRᴼ g nothing  d = sortedT-idle
  deep-cutRᴼ g (just o) d = deep-cutR o d

  deep-cutRᴸ : ∀ {Γ A} (ls : List (U.Node Γ A)) {ρ} → DeepRᴸ ls ρ → SortedT (M′.cuts (U.states ls ρ))
  deep-cutRᴸ []       d        = sortedT-idle
  deep-cutRᴸ (c ∷ cs) (d , ds) = sortedT-∪ _ _ (deep-cutR c d) (deep-cutRᴸ cs ds)

-- A node in order to every depth leaves its rest in order.
mutual
  deepR-of : ∀ {Γ A} {c : U.Node Γ A} {ρ} → Deep c ρ → DeepR c ρ
  deepR-of {c = U.framesᶜ _ _ _}              d = tt
  deepR-of {c = U.burstᶜ _ _ _ _}             d = tt
  deepR-of {c = U.ofᶜ _ _ _}                  d = tt
  deepR-of {c = U.mapᶜ _ c}                   d = deepR-of (proj₂ d)
  deepR-of {c = U.scanᶜ _ _ c}                d = deepR-of (proj₂ d)
  deepR-of {c = U.takeWhileᶜ _ _ c}           d = deepR-of (proj₂ d)
  deepR-of {c = U.flatMapᶜ _ g o ls _ pl}     (_ , dᵒ , dl , dp , _) = deepRᴹ-of o dᵒ , deepRᴸ-of ls dl , deepR-of dp
  deepR-of {c = U.joinᶜ _ _ _ _}              d = tt
  deepR-of {c = U.connectᶜ r b (U.live s)}    (_ , db , ob , ds) = deepR-of db , ob , ds
  deepR-of {c = U.connectᶜ r b (U.ended c t)} (_ , db , ob , dt) = deepR-of db , ob , dt
  deepR-of {c = U.deferᶜ _ _ _}               d = tt
  deepR-of {c = U.endingᶜ _ n}                d = deepR-of (proj₂ d)
  deepR-of {c = U.restᶜ n}                    d = proj₂ d
  deepR-of {c = U.idleᶜ}                      d = tt
  deepR-of {c = U.unionᶜ x y}                 (_ , dx , dy) = deepR-of dx , deepR-of dy
  deepR-of {c = U.burstingᶜ r t}              (o , dt) = ordered-retyped (M′.burstOn r (U.stateᴺ t _)) o , dt
  deepR-of {c = U.underᶜ (U.live s) b}        (_ , ds , db) = ds , deepR-of db
  deepR-of {c = U.underᶜ (U.ended c t) b}     (_ , dt , db) = dt , deepR-of db

  deepRᴹ-of : ∀ {Γ A} (o : Maybe (U.Node Γ A)) {ρ} → Deepᴹ o ρ → DeepRᴹ o ρ
  deepRᴹ-of nothing  d = tt
  deepRᴹ-of (just o) d = deepR-of d

  deepRᴸ-of : ∀ {Γ A} (ls : List (U.Node Γ A)) {ρ} → Deepᴸ ls ρ → DeepRᴸ ls ρ
  deepRᴸ-of []       d        = tt
  deepRᴸ-of (c ∷ cs) (d , ds) = deepR-of d , deepRᴸ-of cs ds

-- A node in order to every depth leaves its cut in order.
deep-cut : ∀ {Γ A} (c : U.Node Γ A) {ρ} → Deep c ρ → SortedT (U.cutᴺ c ρ)
deep-cut c d = deep-cutR c (deepR-of d)

-- A rest whose parts run in order is in order.
deepR-rest : ∀ {Γ A B} {c : U.Node Γ A} {ρ} → DeepR c ρ → Deep (U.restᶜ {B = B} c) ρ
deepR-rest {c = c} d = ordered-tail _ (deep-cutR c d) , d

-- So a node in order leaves its rest in order.
deep-rest : ∀ {Γ A B} {c : U.Node Γ A} {ρ} → Deep c ρ → Deep (U.restᶜ {B = B} c) ρ
deep-rest d = deepR-rest (deepR-of d)

-- Two nodes in order, their union in order.
deep-∪ : ∀ {Γ B} {x y : U.Node Γ B} {ρ} → Deep x ρ → Deep y ρ → Deep (U.unionᶜ x y) ρ
deep-∪ {x = x} {y} dx dy = ordered-tail _ (sortedT-∪ _ _ (deep-cut x dx) (deep-cut y dy)) , dx , dy

-- A program subscribed at the root is in order to every depth: each
-- operator's meaning is, by the order lemmas `Placed` is built on, at
-- the nodes `Placed` does not look at too.
postulate
  deep-subscribe : ∀ {A} (o : Obs Timeline [] A) → Deep (U.subscribe o root) []
