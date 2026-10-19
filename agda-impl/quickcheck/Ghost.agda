{-# OPTIONS --guardedness #-}

-- EVERY OBSERVER, PLACED.  `make placing` holds the root's trace to the
-- denotation; this holds every observer the machine makes inside a run to
-- the denotation of the subtree it observes, subscribed where it is.  A
-- run is compiled to approximant n, every node's observer watched: what
-- it is delivered, and where, goes on the record, tagged with the node, the
-- position the node was subscribed at, and what the denotation shows a
-- subscriber there: `denotation.Unfold`'s meaning.
-- A node under a `connect` is held to its meaning beside the source the
-- `connect` subscribed, fed to its joiners as the meaning feeds them.  Each observer's deliveries must be a
-- prefix of what it is shown, or extend it where the denotation was read
-- only so far: no event the denotation does not have, none out of place.
module quickcheck.Ghost where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; filterᵇ; upTo; length) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String)
import Data.String as S

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; note)
open import operation.Machine using (module Machine)
open import denotation.MonotonicList using (MonotonicList; Label; sub; last; Events; Events∞; out; skip; end; hush; Pos; ix; _<ᵖ_; observe; Timeline)
open import denotation.Unfold using (Srcs; ⟦_⟧ˢ; subscribe; []; _∷_)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Oracle using (depth; until)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Ty using (natᵗ)

-- An observer: the node's path in the tree, and where it was subscribed.
Key : Set
Key = List ℕ × Pos

-- What a subscriber is shown, and whether that was cut short.
Shown : Set
Shown = List (Pos × Bool) × Bool

-- What an entry on the record is: a subscription, a value, a completion.
data Kind : Set where
  subd : Bool → Key → Kind
  val fin : Kind

-- What goes on the record: whose entry, what it should have been shown,
-- and which kind.
Tag : Set
Tag = Key × Shown × Kind

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
  open Machine Tag using (reading; trace; launch; Read)

  -- The node's observer, recording each delivery before passing it on.
  -- `sw`: a switch's lane, dead once its outer source moves on; `par`:
  -- the observer whose subscription made this one.
  watch : ∀ {A w} → Bool → Key → List ℕ → MonotonicList A → (Key → Subscribe A w) → Subscribe A w
  watch sw par π d s ρ o k = here λ p →
    let tag : Kind → Tag
        tag b = (π , p) , expect 2000 (observe d p) , b in
    eff (note (tag (subd sw par))) λ _ →
    s (π , p) ρ (record { next = λ a → eff (note (tag val)) λ _ → Observer.next o a
                ; complete = eff (note (tag fin)) λ _ → Observer.complete o
                ; closed = Observer.closed o }) k

  isSwitch : T.FlatOp → Bool
  isSwitch T.switchᶠ = true
  isSwitch _         = false

  -- Approximant n, every node watched against its meaning.  A connect's
  -- source is the configuration it starts in, subscribed one step in; past
  -- the approximant the run stops, so a cut costs coverage, never a pass.
  mutual
    watched : ℕ → Key → List ℕ → ∀ {Γ A w} → Obs Timeline Γ A → Env Γ w → Srcs Γ → Subscribe A w
    watched = watchedS false

    watchedS : Bool → ℕ → Key → List ℕ → ∀ {Γ A w} → Obs Timeline Γ A → Env Γ w → Srcs Γ → Subscribe A w
    watchedS sw n par π t ρ δ = watch sw par π (⟦ t ⟧ˢ δ) λ me → node n me π t ρ δ

    node : ℕ → Key → List ℕ → ∀ {Γ A w} → Obs Timeline Γ A → Env Γ w → Srcs Γ → Subscribe A w
    node n       me π (cold c)          ρ δ = via (startCold c)
    node n       me π empty             ρ δ = emptyᴷ
    node n       me π (of xs)           ρ δ = ofᴷ xs
    node n       me π (map f s)         ρ δ = mapᴷ f (watched n me (0 ∷ π) s ρ δ)
    node n       me π (scan f z s)      ρ δ = scanᴷ f z (watched n me (0 ∷ π) s ρ δ)
    node n       me π (takeWhile i p s) ρ δ = takeWhileᴷ i p (watched n me (0 ∷ π) s ρ δ)
    node n       me π (flatMap op f s)  ρ δ = flatMapᴷ op (λ a → watchedS (isSwitch op) n me (1 ∷ π) (f a) ρ δ) (watched n me (0 ∷ π) s ρ δ)
    node n       me π (connect s b)     ρ δ σ o k = here λ p →
      connectᴷ (watched n me (0 ∷ π) s ρ δ)
               (λ τ st → watched n me (1 ∷ π) b (st ∷ wkEnv τ ρ) ((p ++ [ ix 1 ] , subscribe s (p ++ [ ix 1 ])) ∷ δ)) σ o k
    node n       me π (connected i)     ρ δ = joinᴷ (lookup ρ i)
    node zero    me π (defer l)         ρ δ = ⊥ᴷ
    node (suc n) me π (defer l)         ρ δ = deeper (watched n me (0 ∷ π) (Later.force l) ρ δ)

  -- The root's own observer does nothing: its node is watched already.
  idle : ∀ {A} → Observer A []
  idle = record { next = λ _ → done tt ; complete = done tt ; closed = done false }

  -- The record of approximant n, over b steps of the machine up to the
  -- horizon: each
  -- delivery, where.
  deliveries : ℕ → ℕ → ∀ {A} → Obs Timeline [] A → List (Pos × Tag)
  deliveries n b t = zip (Read.marks r) (mapL proj₂ (Read.log r))
    where
      run = trace (launch (watched n ([] , []) [] t [] []) idle)
      r = reading (until b run) 0 run
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

  delivery : Kind → Bool
  delivery (subd _ _) = false
  delivery _    = true

  isFin : Kind → Bool
  isFin fin = true
  isFin _   = false

  kindOf : Pos × Tag → Kind
  kindOf (_ , _ , _ , b) = b

  -- One observer's deliveries, against what it was shown.
  holds : Key → List (Pos × Tag) → Bool
  holds k ds with filterᵇ (λ d → sameKey k (keyOf d) ∧ delivery (kindOf d)) ds
  ... | []                 = true
  ... | mine@((_ , _ , (ex , cut) , _) ∷ _) =
    let got = mapL (λ { (q , _ , _ , b) → q , isFin b }) mine in prefix got ex ∨ (cut ∧ prefix ex got)

  -- EXACT: once the run's position is past an event an observer is shown,
  -- the observer has been delivered it.  Checked at every entry on the
  -- record, each entry's position the run's then.
  numbered : ℕ → List (Pos × Tag) → List (ℕ × Pos × Tag)
  numbered i []       = []
  numbered i (d ∷ ds) = (i , d) ∷ numbered (suc i) ds

  -- The first entry after `s` whose position is past `e`, up to the
  -- deadline `f`: past it the observer is dead, owed nothing.
  passed : ℕ → ℕ → Pos → List (ℕ × Pos × Tag) → Maybe ℕ
  passed s f e []                  = nothing
  passed s f e ((i , q , _) ∷ ds) = if f <ᵇ i then nothing else if (s <ᵇ i) ∧ (e <ᵖ q) then just i else passed s f e ds

  big : ℕ
  big = 1000000000

  minℕ : ℕ → ℕ → ℕ
  minℕ a b = if a <ᵇ b then a else b

  -- An observer's subscription: where on the record, whether a switch's
  -- lane, and its parent.
  subOf : Key → List (ℕ × Pos × Tag) → Maybe (ℕ × Bool × Key)
  subOf k []                                  = nothing
  subOf k ((i , _ , k′ , _ , subd sw par) ∷ ds) = if sameKey k k′ then just (i , sw , par) else subOf k ds
  subOf k (_ ∷ ds)                            = subOf k ds

  finOf : Key → List (ℕ × Pos × Tag) → ℕ
  finOf k []                        = big
  finOf k ((i , _ , k′ , _ , fin) ∷ ds) = if sameKey k k′ then i else finOf k ds
  finOf k (_ ∷ ds)                  = finOf k ds

  -- The outer source a switch's lane hangs off: its parent's child 0.
  outerOf : List ℕ → Key → List (ℕ × Pos × Tag) → Maybe Key
  outerOf π par []                                      = nothing
  outerOf π par ((_ , _ , (π′ , p′) , _ , subd _ par′) ∷ ds) =
    if sameℕs (0 ∷ π) π′ ∧ sameKey par par′ then just (π′ , p′) else outerOf π par ds
  outerOf π par (_ ∷ ds)                                = outerOf π par ds

  nextVal : ℕ → Key → List (ℕ × Pos × Tag) → ℕ
  nextVal s k []                        = big
  nextVal s k ((i , _ , k′ , _ , val) ∷ ds) = if (s <ᵇ i) ∧ sameKey k k′ then i else nextVal s k ds
  nextVal s k (_ ∷ ds)                  = nextVal s k ds

  moved : ℕ → Key → Key → List (ℕ × Pos × Tag) → ℕ
  moved s (1 ∷ π , _) par nds with outerOf π par nds
  ... | just ok = nextVal s ok nds
  ... | nothing = big
  moved s _ par nds = big

  -- An observer is dead once it completes, a switch moves off it, or its
  -- parent is dead.
  death : ℕ → Key → List (ℕ × Pos × Tag) → ℕ
  death zero    k nds = big
  death (suc n) k nds with subOf k nds
  ... | nothing              = big
  ... | just (s , sw , par) = minℕ (finOf k nds) (minℕ (if sw then moved s k par nds else big) (death n par nds))

  -- Each event shown, against the observer's deliveries in order.
  owed : ℕ → ℕ → List (Pos × Bool) → List ℕ → List (ℕ × Pos × Tag) → Bool
  owed s f []             _        nds = true
  owed s f ((e , _) ∷ es) dels     nds with passed s f e nds
  ... | nothing = true
  ... | just k with dels
  ...   | []        = false
  ...   | d ∷ dels′ = (d <ᵇ k) ∧ owed s f es dels′ nds

  exactAt : List (ℕ × Pos × Tag) → ℕ × Pos × Tag → Bool
  exactAt nds (s , _ , key , (ex , _) , subd _ _) =
    owed s (death 64 key nds) ex (mapL proj₁ (filterᵇ (λ { (i , d) → (s <ᵇ i) ∧ sameKey key (keyOf d) ∧ delivery (kindOf d) }) nds)) nds
  exactAt nds _ = true

  every : ∀ {X : Set} → (X → Bool) → List X → Bool
  every f []       = true
  every f (x ∷ xs) = f x ∧ every f xs

  -- `e` lies under `q ++ [ ix _ ]` or `q ++ [ sub _ ]`: where the
  -- delivery of a value at `q` runs.
  inside : Pos → Pos → Bool
  inside []      (ix _ ∷ _)  = true
  inside []      (sub _ ∷ _) = true
  inside []      _           = false
  inside (l ∷ q) (l′ ∷ e)    = samePos [ l ] [ l′ ] ∧ inside q e
  inside (_ ∷ _) []          = false

  -- After a value at `q`, nothing shown where its delivery runs.
  settles : List (Pos × Bool) → Bool
  settles []             = true
  settles ((p , b) ∷ es) = (b ∨ every (λ e → not (inside p (proj₁ e))) es) ∧ settles es

  settledAt : Pos × Tag → Bool
  settledAt (_ , _ , (ex , _) , subd _ _) = settles ex
  settledAt _                             = true

  record′ : Prog natᵗ → List (Pos × Tag)
  record′ p = Watched.deliveries (depth 3 p) 40000 (toObs timeline 3 p [] [] [])

ghosts : Prog natᵗ → Bool
ghosts p = every (λ d → holds (keyOf d) ds) ds
  where ds = record′ p

exact : Prog natᵗ → Bool
exact p = every (exactAt nds) nds
  where nds = numbered 0 (record′ p)

-- SETTLED: what each observer is shown never returns under a value it
-- was shown, where that value's delivery runs.
settled : Prog natᵗ → Bool
settled p = every settledAt (record′ p)

-- One seed's record, every entry: its number, position, observer, kind;
-- a subscription with what it is shown.
mutual
  showL : Label → String
  showL (ix n)  = showℕ n
  showL (sub p) = "s(" S.++ showP p S.++ ")"
  showL last    = "L"

  showP : Pos → String
  showP []       = ""
  showP (l ∷ []) = showL l
  showP (l ∷ ls) = showL l S.++ "." S.++ showP ls

private
  showK : Kind → String
  showK (subd b _) = if b then "SUB(sw)" else "SUB"
  showK val  = "val"
  showK fin  = "fin"

  showEx : List (Pos × Bool) → String
  showEx []             = ""
  showEx ((p , b) ∷ es) = showP p S.++ (if b then "!" else "") S.++ " " S.++ showEx es

  showE : ℕ × Pos × Tag → String
  showE (i , q , (π , p) , (ex , cut) , k) =
    showℕ i S.++ " @" S.++ showP q S.++ " node" S.++ S.concat (mapL (λ n → "/" S.++ showℕ n) π) S.++ " sub@" S.++ showP p S.++ " " S.++ showK k
    S.++ (if delivery k then "" else " shown: " S.++ showEx ex S.++ (if cut then "…" else ""))


exactWhy : Prog natᵗ → List String
exactWhy p = mapL (λ e → showE e S.++ (if exactAt nds e then "" else "   <== BEHIND")) nds
  where nds = numbered 0 (record′ p)

-- The seeds from `from`, `count` of them, with an observer behind the run.
exactFails : ℕ → ℕ → List ℕ
exactFails from count = filterᵇ (λ s → not (exact (program s))) (mapL (from +_) (upTo count))

-- The seeds from `from`, `count` of them, with an observer shown an event
-- under a value it was shown.
settledFails : ℕ → ℕ → List ℕ
settledFails from count = filterᵇ (λ s → not (settled (program s))) (mapL (from +_) (upTo count))

-- The seeds from `from`, `count` of them, with an observer out of place.
ghostFails : ℕ → ℕ → List ℕ
ghostFails from count = filterᵇ (λ s → not (ghosts (program s))) (mapL (from +_) (upTo count))

-- How many deliveries the seeds compared: a pass over empty records is no pass.
watchedCount : ℕ → ℕ → ℕ
watchedCount from count = sum (mapL (λ s → length (record′ (program s))) (mapL (from +_) (upTo count)))
