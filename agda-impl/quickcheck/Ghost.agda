{-# OPTIONS --guardedness #-}

-- EVERY OBSERVER, PLACED.  `make places` holds the root's record to the
-- denotation; this holds every observer the engine makes inside a run to
-- the denotation of the subtree it observes, subscribed where it is.  A
-- run is compiled as `compileᴺ` does, every node's observer watched: what
-- it is delivered, and where, goes on the record, tagged with the node, the
-- position the node was subscribed at, and what the denotation shows a
-- subscriber there.  A `connected` node is held to the hot handle its
-- `connect` was subscribed with.  Each observer's deliveries must be a
-- prefix of what it is shown, or extend it where the denotation was read
-- only so far: no event the denotation does not have, none out of place.
module quickcheck.Ghost where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; [_]; filterᵇ; upTo; length) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (tt)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; module Pure; note; same)
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; out; skip; end; hush; Pos; ix; _<ᵖ_; observe; hot; Timeline)
open import denotation.Denote using (DenEnv; ⟦_⟧[_])
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Oracle using (depth)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (natᵗ)

-- An observer: the node's path in the tree, and where it was subscribed.
Key : Set
Key = List ℕ × Pos

-- What a subscriber is shown, and whether that was cut short.
Shown : Set
Shown = List (Pos × Bool) × Bool

-- What goes on the record: whose delivery, what it should have been
-- shown, and whether this one is its completion.
Tag : Set
Tag = Key × Shown × Bool

private
  -- What a subscriber is shown: each value's position, and the completion's.
  expect : ∀ {A} → ℕ → Events A → Shown
  expect zero    _           = [] , true
  expect (suc k) (out p _ r) with expect k (Events∞.force r)
  ... | ps , c = (p , false) ∷ ps , c
  expect (suc k) (skip _ r)  = expect k (Events∞.force r)
  expect (suc k) (end p)     = (p , true) ∷ [] , false
  expect (suc k) hush        = [] , false

module Watched where
  open Run (Pureᴾ Tag)
  open Pure Tag using (runᴺ; loopᴺ; start; Pureᴿ; Res; State)

  -- The node's observer, recording each delivery before passing it on.
  watch : ∀ {A w} → List ℕ → MonotonicList A → Subscribe A w → Subscribe A w
  watch π d s ρ o k = here λ p →
    let tag : Bool → Tag
        tag b = (π , p) , expect 2000 (observe d p) , b in
    s ρ (record { next = λ a → eff (note (tag false)) λ _ → Observer.next o a
                ; complete = eff (note (tag true)) λ _ → Observer.complete o
                ; closed = Observer.closed o }) k

  -- `compileᴺ n`, every node watched against approximant n.  A connect's
  -- handle is the hot run of its source, subscribed one step in.
  mutual
    watched : ℕ → List ℕ → ∀ {Γ A w} → Obs Timeline Γ A → Env Γ w → DenEnv Γ → Subscribe A w
    watched n π t ρ δ = watch π (⟦ t ⟧[ n ] δ) (node n π t ρ δ)

    node : ℕ → List ℕ → ∀ {Γ A w} → Obs Timeline Γ A → Env Γ w → DenEnv Γ → Subscribe A w
    node n       π (cold c)          ρ δ = via (startCold c)
    node n       π empty             ρ δ = emptyᴷ
    node n       π (of xs)           ρ δ = ofᴷ xs
    node n       π (map f s)         ρ δ = mapᴷ f (watched n (0 ∷ π) s ρ δ)
    node n       π (scan f z s)      ρ δ = scanᴷ f z (watched n (0 ∷ π) s ρ δ)
    node n       π (takeWhile i p s) ρ δ = takeWhileᴷ i p (watched n (0 ∷ π) s ρ δ)
    node n       π (flatMap op f s)  ρ δ = flatMapᴷ op (λ a → watched n (1 ∷ π) (f a) ρ δ) (watched n (0 ∷ π) s ρ δ)
    node n       π (connect s b)     ρ δ σ o k = here λ p →
      connectᴷ (watched n (0 ∷ π) s ρ δ)
               (λ τ st → watched n (1 ∷ π) b (st ∷ wkEnv τ ρ) (hot (observe (⟦ s ⟧[ n ] δ) (p ++ [ ix 1 ])) ∷ δ)) σ o k
    node n       π (connected i)     ρ δ = joinᴷ (lookup ρ i)
    node zero    π (defer l)         ρ δ = ⊥ᴷ
    node (suc n) π (defer l)         ρ δ = deeper (watched n (0 ∷ π) (Later.force l) ρ δ)

  -- The root's own observer does nothing: its node is watched already.
  idle : ∀ {A} → Observer A []
  idle = record { next = λ _ → done tt ; complete = done tt ; closed = done false }

  -- The record of approximant n, on a budget of b: each delivery, where.
  deliveries : ℕ → ℕ → ∀ {A} → Obs Timeline [] A → List (Pos × Tag)
  deliveries n b t = zip (State.marks st) (mapL proj₂ (State.log st))
    where
      st = Res.state (Engine.drive (Pureᴿ b) (runᴺ b b) (loopᴺ b b) (watched n [] t [] []) idle same start)
      zip : List Pos → List Tag → List (Pos × Tag)
      zip (p ∷ ps) (x ∷ xs) = (p , x) ∷ zip ps xs
      zip _        _        = []

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  sameℕs : List ℕ → List ℕ → Bool
  sameℕs []       []       = true
  sameℕs (m ∷ ms) (n ∷ ns) = (m ≡ᵇ n) ∧ sameℕs ms ns
  sameℕs _        _        = false

  sameKey : Key → Key → Bool
  sameKey (π , p) (π′ , p′) = sameℕs π π′ ∧ samePos p p′

  sameEv : Pos × Bool → Pos × Bool → Bool
  sameEv (p , true)  (q , true)  = samePos p q
  sameEv (p , false) (q , false) = samePos p q
  sameEv _           _           = false

  prefix : List (Pos × Bool) → List (Pos × Bool) → Bool
  prefix []       _        = true
  prefix (x ∷ xs) []       = false
  prefix (x ∷ xs) (y ∷ ys) = sameEv x y ∧ prefix xs ys

  keyOf : Pos × Tag → Key
  keyOf (_ , k , _) = k

  -- One observer's deliveries, against what it was shown.
  holds : Key → List (Pos × Tag) → Bool
  holds k ds with filterᵇ (λ d → sameKey k (keyOf d)) ds
  ... | []                 = true
  ... | mine@((_ , _ , (ex , cut) , _) ∷ _) =
    let got = mapL (λ { (q , _ , _ , b) → q , b }) mine in prefix got ex ∨ (cut ∧ prefix ex got)

  every : ∀ {X : Set} → (X → Bool) → List X → Bool
  every f []       = true
  every f (x ∷ xs) = f x ∧ every f xs

  record′ : Prog natᵗ → List (Pos × Tag)
  record′ p = Watched.deliveries (depth 3 p) (500 + depth 3 p) (toObs timeline 3 p [] [] [])

ghosts : Prog natᵗ → Bool
ghosts p = every (λ d → holds (keyOf d) ds) ds
  where ds = record′ p

-- The seeds from `from`, `count` of them, with an observer out of place.
ghostFails : ℕ → ℕ → List ℕ
ghostFails from count = filterᵇ (λ s → not (ghosts (program s))) (mapL (from +_) (upTo count))

-- How many deliveries the seeds compared: a pass over empty records is no pass.
watchedCount : ℕ → ℕ → ℕ
watchedCount from count = sum (mapL (λ s → length (record′ (program s))) (mapL (from +_) (upTo count)))
