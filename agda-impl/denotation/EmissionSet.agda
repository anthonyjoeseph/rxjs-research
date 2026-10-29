{-# OPTIONS --guardedness #-}

-- THE EMISSION SET: a program's meaning as every row of work it causes, each at
-- its position.  The positions are `MonotonicList`'s, and they are totally
-- ordered, so an emission set needs no order of its own: the n-th event is the
-- n-th row by position.  An operator is a function on emission sets, defined
-- all at once — a merge is a union, a joiner is a filter and a rekey.
--
-- Work that keeps running after whoever listens stops — a connect's
-- source still in its subscribe burst — stays in the emission set as `skip`
-- rows.  An emission set's PROPER rows are those at or before its end; a hot
-- shows only those.
--
-- TRUNCATED AT THE FIRST INFINITY: a row with infinitely many rows before
-- it is never reached, which is how a synchronous loop blocks everything
-- after it, so every reading of an observable (`enter`) keeps only the
-- rows with finitely many before them (`Truncate`).  A set could hold a row past infinity where a
-- stream cannot; the operator would decide it from rows nobody reaches, and
-- the limit and the operator would disagree on it.
module denotation.EmissionSet where

open import Data.Bool using (Bool; T; not)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _∸_)
open import Data.Product using (Σ; _×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Timeline; timelineAt; _<ᵖ_; inside; ix; sub; last)
open import denotation.MonotonicList using (start; ofᴱ)

------------------------------------------------------------------------
-- Rows

data Ev (A : Set) : Set where
  out  : A → Ev A
  skip : Ev A
  end  : Ev A

EmissionSet : Set → Set₁
EmissionSet A = Pos → Ev A → Set

_≺_ : Pos → Pos → Set
p ≺ q = T (p <ᵖ q)

-- At or before.
_≼_ : Pos → Pos → Set
p ≼ q = ¬ (q ≺ p)

-- Work that is not a completion.
Work : ∀ {A} → Ev A → Set
Work end = ⊥
Work _   = ⊤

-- The rows a stream reaches, each at a finite index.
data InE {A : Set} : E.Events A → EmissionSet A where
  at-out  : ∀ {k a r} → InE (E.out k a r) k (out a)
  at-skip : ∀ {k r} → InE (E.skip k r) k skip
  at-end  : ∀ {k} → InE (E.end k) k end
  on-out  : ∀ {k a r q e} → InE (E.Events∞.force r) q e → InE (E.out k a r) q e
  on-skip : ∀ {k r q e} → InE (E.Events∞.force r) q e → InE (E.skip k r) q e

-- Rows at or before the end.
Proper : ∀ {A} → EmissionSet A → EmissionSet A
Proper t q e = t q e × (∀ {c} → t c end → q ≼ c)

-- Finitely many rows lie before `q`.
Few : ∀ {A} → EmissionSet A → Pos → Set
Few t q = Σ (List Pos) λ ks → ∀ {k e′} → t k e′ → k ≺ q → k ∈ ks

-- The rows with finitely many rows before them.
Truncate : ∀ {A} → EmissionSet A → EmissionSet A
Truncate t q e = t q e × Few t q

-- What a subscriber reaches: a proper row with finitely many rows before it.
Seen : ∀ {A} → EmissionSet A → EmissionSet A
Seen t q e = Proper t q e × Few t q

------------------------------------------------------------------------
-- Observables

-- A hot is one emission set at absolute positions; a cold, an emission set for every
-- subscription position.  Only a `connect` makes a hot.
data Den (A : Set) : Set₁ where
  hot  : EmissionSet A → Den A
  cold : (Pos → EmissionSet A) → Den A

-- JOINING A HOT AT `p`: what comes after `p`, rekeyed under `sub p`; a
-- hot already ended at `p` ends at once.  Nothing is shown for what was
-- missed: the work was the source's, and the source shows it.
data Rejoin {A : Set} (p : Pos) (t : EmissionSet A) : EmissionSet A where
  shown : ∀ {q e} → t q e → Work e → p ≺ q → Rejoin p t (q ++ [ sub p ]) e
  ended : ∀ {c} → t c end → p ≺ c → Rejoin p t (c ++ [ sub p ]) end
  late  : ∀ {c} → t c end → c ≼ p → Rejoin p t (p ++ [ last ]) end

enter : ∀ {A} → Den A → Pos → EmissionSet A
enter (hot t)  p = Truncate (Rejoin p t)
enter (cold f) p = Truncate (f p)

-- A LANE subscribed at `s`: its rows past `s`.  A lawful reading has no
-- other, and a joiner reading one before its subscription would hang its
-- rows on outer values past them (`flatMap-causal`).
After : ∀ {A} → Den A → Pos → EmissionSet A
After d s k e = enter d s k e × s ≺ k

------------------------------------------------------------------------
-- Leaves

coldᵀ : ∀ {A} → Timeline A → Den A
coldᵀ c = cold λ p → InE (start p (timelineAt c p))

emptyᵀ : ∀ {A} → Den A
emptyᵀ = cold λ p → InE (E.end (p ++ [ last ]))

ofᵀ : ∀ {A} → List A → Den A
ofᵀ xs = cold λ p → InE (ofᴱ p 0 xs)

-- No information yet: a subscription that spins and never closes.
data Spin {A : Set} (p : Pos) : EmissionSet A where
  spin : ∀ i → Spin p (p ++ [ ix i ]) skip

⊥ᵀ : ∀ {A} → Den A
⊥ᵀ = cold Spin

------------------------------------------------------------------------
-- One input

data MapT {A B : Set} (f : A → B) (t : EmissionSet A) : EmissionSet B where
  map-out  : ∀ {q a} → t q (out a) → MapT f t q (out (f a))
  map-skip : ∀ {q} → t q skip → MapT f t q skip
  map-end  : ∀ {q} → t q end → MapT f t q end

mapᵀ : ∀ {A B} → (A → B) → Den A → Den B
mapᵀ f s = cold λ p → MapT f (enter s p)

-- A `skip`, then the body: rxjs's own `defer`, synchronous.
data DeferT {A : Set} (s : Den A) (p : Pos) : EmissionSet A where
  guard : DeferT s p (p ++ [ ix 0 ]) skip
  body  : ∀ {q e} → enter s (p ++ [ ix 1 ]) q e → DeferT s p q e

deferᵀ : ∀ {A} → Den A → Den A
deferᵀ s = cold (DeferT s)

-- An input's values in position order.
module Values {A : Set} (o : EmissionSet A) where

  -- `q′` is the first value after `q`.
  Next : Pos → Pos → Set
  Next q q′ = ∀ {k b} → o k (out b) → q ≺ k → q′ ≼ k

  -- The i-th value.
  data Nth : ℕ → Pos → A → Set where
    first : ∀ {q a} → o q (out a) → (∀ {k b} → o k (out b) → q ≼ k) → Nth 0 q a
    next  : ∀ {i q a q′ a′} → Nth i q a → o q′ (out a′) → q ≺ q′ → Next q q′ → Nth (suc i) q′ a′

-- SCAN: each value as the fold of every value up to it.
module Scan {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) where
  open Values t using (Next)

  -- The fold up to the value at `q`.
  data Acc : Pos → B → Set where
    acc₀ : ∀ {q a} → t q (out a) → (∀ {k b} → t k (out b) → q ≼ k) → Acc q (f z a)
    acc  : ∀ {q b q′ a′} → Acc q b → t q′ (out a′) → q ≺ q′ → Next q q′ → Acc q′ (f b a′)

  data ScanT : EmissionSet B where
    sval  : ∀ {q b} → Acc q b → ScanT q (out b)
    sstep : ∀ {q} → t q skip → ScanT q skip
    send  : ∀ {q} → t q end → ScanT q end

scanᵀ : ∀ {A B} → (B → A → B) → B → Den A → Den B
scanᵀ f z s = cold λ p → Scan.ScanT f z (enter s p)

-- TAKEWHILE, subscribed at `p`: values while they pass.  The first
-- failing one leaves under `ix 0` of its position if inclusive, and the
-- completion under `last` either way.  What the source still runs of its
-- subscribe burst stays, as skips; the rest is unsubscribed.
module TakeWhile {A : Set} (incl : Bool) (keep : A → Bool) (t : EmissionSet A) (p : Pos) where

  -- A failing value lies before `k`.
  Failed : Pos → Set
  Failed k = Σ Pos λ q → Σ A λ a → t q (out a) × T (not (keep a)) × q ≺ k

  data TakeT : EmissionSet A where
    pass  : ∀ {q a} → t q (out a) → T (keep a) → ¬ Failed q → TakeT q (out a)
    fail  : ∀ {q a} → t q (out a) → T (not (keep a)) → ¬ Failed q → T incl → TakeT (q ++ [ ix 0 ]) (out a)
    stop  : ∀ {q a} → t q (out a) → T (not (keep a)) → ¬ Failed q → TakeT (q ++ [ last ]) end
    step  : ∀ {q} → t q skip → ¬ Failed q → TakeT q skip
    tend  : ∀ {q} → t q end → ¬ Failed q → TakeT q end
    left  : ∀ {q e} → t q e → Failed q → T (inside p q) → TakeT q skip

takeWhileᵀ : ∀ {A} → Bool → (A → Bool) → Den A → Den A
takeWhileᵀ i keep s = cold λ p → TakeWhile.TakeT i keep (enter s p) p

------------------------------------------------------------------------
-- Merge

-- The outer `o`, and each of its values `a` at `q` subscribed as a lane
-- at `q ++ [ ix 1 ]`, its first effect `q ++ [ ix 0 ]` silent.
module Merge {A B : Set} (f : A → Den B) (o : EmissionSet A) where

  Lane : Pos → A → EmissionSet B
  Lane q a = After (f a) (q ++ [ ix 1 ])

  -- Every part begun before `c` has ended by `c`.
  Done : Pos → Set
  Done c = (Σ Pos λ c₀ → o c₀ end × c₀ ≼ c)
         × (∀ {q a} → o q (out a) → q ≺ c → Σ Pos λ c′ → Lane q a c′ end × c′ ≼ c)

  -- The whole ends where the last part does; every other end is a skip.
  data MergeT : EmissionSet B where
    val   : ∀ {q a} → o q (out a) → MergeT (q ++ [ ix 0 ]) skip
    step  : ∀ {q} → o q skip → MergeT q skip
    oend  : ∀ {c} → o c end → Done c → MergeT c end
    opass : ∀ {c} → o c end → ¬ Done c → MergeT c skip
    lane  : ∀ {q a k e} → o q (out a) → Lane q a k e → Work e → MergeT k e
    lend  : ∀ {q a c} → o q (out a) → Lane q a c end → Done c → MergeT c end
    lpass : ∀ {q a c} → o q (out a) → Lane q a c end → ¬ Done c → MergeT c skip

-- MERGE, BOUNDED BY n: a value arriving with n lanes running waits in a
-- queue, and the queue's first lane is subscribed where a lane ends, that
-- end shown silent at its first effect.  Lanes start in value order, so
-- lane i is running once i ∸ n + 1 of the lanes before it have ended: it
-- starts where its value arrives, or where the (i ∸ n + 1)-th of their
-- ends falls, whichever is later.  Each is decided by the ends before the
-- start, so a lane that never starts never ends and frees nothing.
-- `just 1` is concat.
module Bounded {A B : Set} (n : ℕ) (f : A → Den B) (o : EmissionSet A) where
  open Values o

  -- `k` and one more of the lanes `ls`, each given by its ends, end
  -- where `P` holds: for `P` closed downward, the lanes' k-th end in
  -- position order, from 0, is where `P` holds.
  Kth : (Pos → Set) → List (Pos → Set) → ℕ → Set
  Kth P []       k       = ⊥
  Kth P (l ∷ ls) zero    = (Σ Pos λ c → l c × P c) ⊎ Kth P ls zero
  Kth P (l ∷ ls) (suc k) = ((Σ Pos λ c → l c × P c) × Kth P ls k) ⊎ Kth P ls (suc k)

  -- Where lane i, for the value at `q`, starts, given the lanes `ls`
  -- before it: at once, or at the end that frees it.
  data Starts (i : ℕ) (q : Pos) (ls : List (Pos → Set)) : Pos → Set where
    room   : i < n → Starts i q ls (q ++ [ ix 1 ])
    freed  : n ≤ i → Kth (_≺ q) ls (i ∸ n) → Starts i q ls (q ++ [ ix 1 ])
    queued : ∀ {c} → n ≤ i → q ≺ c → Kth (_≡ c) ls 0 → Kth (_≼ c) ls (i ∸ n)
           → ¬ Kth (_≺ c) ls (i ∸ n) → Starts i q ls (c ++ [ ix 1 ])

  -- Lane i's ends, given the lanes before it.
  Ends : ℕ → List (Pos → Set) → Pos → Set
  Ends i ls c = Σ Pos λ q → Σ A λ a → Σ Pos λ s → Nth i q a × Starts i q ls s × After (f a) s c end

  -- The lanes before lane i, the latest first.
  Sched : ℕ → List (Pos → Set)
  Sched zero    = []
  Sched (suc i) = Ends i (Sched i) ∷ Sched i

  -- Lane i, for the outer's value at `q`, subscribed at `s`.
  Sub : ℕ → Pos → Pos → A → Set
  Sub i q s a = Nth i q a × Starts i q (Sched i) s

  -- A queued lane starts past `c`.
  Queued : Pos → Set
  Queued c = Σ ℕ λ i → Σ Pos λ q → Σ A λ a → Sub i q (c ++ [ ix 1 ]) a

  -- Every part begun before `c` has ended by `c`.
  Done : Pos → Set
  Done c = (Σ Pos λ c₀ → o c₀ end × c₀ ≼ c)
         × (∀ {i q a} → Nth i q a → q ≺ c → Σ Pos λ s → Σ Pos λ c′ → Sub i q s a × After (f a) s c′ end × c′ ≼ c)

  data BoundedT : EmissionSet B where
    val     : ∀ {q a} → o q (out a) → BoundedT (q ++ [ ix 0 ]) skip
    step    : ∀ {q} → o q skip → BoundedT q skip
    oend    : ∀ {c} → o c end → Done c → BoundedT c end
    opass   : ∀ {c} → o c end → ¬ Done c → BoundedT c skip
    lane    : ∀ {i q s a k e} → Sub i q s a → After (f a) s k e → Work e → BoundedT k e
    handoff : ∀ {i q s a c} → Sub i q s a → After (f a) s c end → Queued c → BoundedT (c ++ [ ix 0 ]) skip
    lend    : ∀ {i q s a c} → Sub i q s a → After (f a) s c end → ¬ Queued c → Done c → BoundedT c end
    lpass   : ∀ {i q s a c} → Sub i q s a → After (f a) s c end → ¬ Queued c → ¬ Done c → BoundedT c skip

-- SWITCH: a value's lane runs until the next value arrives.  What a cut
-- lane still runs of its subscribe burst stays, as skips.
module Switch {A B : Set} (f : A → Den B) (o : EmissionSet A) where

  Lane : Pos → A → EmissionSet B
  Lane q a = After (f a) (q ++ [ ix 1 ])

  -- A value after `q` arrived before `k`.
  Cut : Pos → Pos → Set
  Cut q k = Σ Pos λ q′ → Σ A λ a′ → o q′ (out a′) × q ≺ q′ × q′ ≺ k

  -- No value after `q` before `c`.
  Latest : Pos → Pos → Set
  Latest q c = ∀ {q′ a′} → o q′ (out a′) → q′ ≺ c → q′ ≼ q

  -- The outer and the last lane begun before `c` have ended by `c`.
  Done : Pos → Set
  Done c = (Σ Pos λ c₀ → o c₀ end × c₀ ≼ c)
         × (∀ {q a} → o q (out a) → q ≺ c → Latest q c → Σ Pos λ c′ → Lane q a c′ end × c′ ≼ c)

  data SwitchT : EmissionSet B where
    val   : ∀ {q a} → o q (out a) → SwitchT (q ++ [ ix 0 ]) skip
    step  : ∀ {q} → o q skip → SwitchT q skip
    oend  : ∀ {c} → o c end → Done c → SwitchT c end
    opass : ∀ {c} → o c end → ¬ Done c → SwitchT c skip
    lane  : ∀ {q a k e} → o q (out a) → Lane q a k e → Work e → ¬ Cut q k → SwitchT k e
    lend  : ∀ {q a c} → o q (out a) → Lane q a c end → ¬ Cut q c → Done c → SwitchT c end
    lpass : ∀ {q a c} → o q (out a) → Lane q a c end → ¬ Cut q c → ¬ Done c → SwitchT c skip
    left  : ∀ {q a k e} → o q (out a) → Lane q a k e → Cut q k → T (inside (q ++ [ ix 1 ]) k) → SwitchT k skip

-- EXHAUST: a value's lane runs only if the last lane run has ended by the
-- time it arrives; otherwise the value is dropped.
module Exhaust {A B : Set} (f : A → Den B) (o : EmissionSet A) where
  open Values o using (Next)

  Lane : Pos → A → EmissionSet B
  Lane q a = After (f a) (q ++ [ ix 1 ])

  -- At the value at `q′`, the last lane run is the value at `q`'s.
  data Cur : Pos → Pos → Set where
    cur₀ : ∀ {q a} → o q (out a) → (∀ {k b} → o k (out b) → q ≼ k) → Cur q q
    run  : ∀ {q₁ q a c q₂ a₂} → Cur q₁ q → o q (out a) → Lane q a c end → c ≺ q₂
         → o q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ q₂
    drop : ∀ {q₁ q a q₂ a₂} → Cur q₁ q → o q (out a) → (∀ {c} → Lane q a c end → q₂ ≼ c)
         → o q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ q

  -- The value at `q` runs its lane.
  Run : Pos → Set
  Run q = Cur q q

  -- The outer and every lane run begun before `c` have ended by `c`.
  Done : Pos → Set
  Done c = (Σ Pos λ c₀ → o c₀ end × c₀ ≼ c)
         × (∀ {q a} → o q (out a) → q ≺ c → Run q → Σ Pos λ c′ → Lane q a c′ end × c′ ≼ c)

  data ExhaustT : EmissionSet B where
    val   : ∀ {q a} → o q (out a) → ExhaustT (q ++ [ ix 0 ]) skip
    step  : ∀ {q} → o q skip → ExhaustT q skip
    oend  : ∀ {c} → o c end → Done c → ExhaustT c end
    opass : ∀ {c} → o c end → ¬ Done c → ExhaustT c skip
    lane  : ∀ {q a k e} → o q (out a) → Run q → Lane q a k e → Work e → ExhaustT k e
    lend  : ∀ {q a c} → o q (out a) → Run q → Lane q a c end → Done c → ExhaustT c end
    lpass : ∀ {q a c} → o q (out a) → Run q → Lane q a c end → ¬ Done c → ExhaustT c skip

------------------------------------------------------------------------
-- Connect

-- Subscribed at `p`: the body at `p ++ [ ix 0 ]` over the source made hot,
-- then the source at `r = p ++ [ ix 1 ]`.  Each source step at `k` shows
-- silent at its first effect if the body has not ended by `k`; once it
-- has, what remains of the source's subscribe burst still runs, at its
-- own positions.  The body's end ends the connect.
--
-- Liveness is read AT `k`, never at the shown row: a body end at
-- `k ++ [ ix 0 ]` lies in the source's world, which no lawful body
-- reaches, and reading there would make the connect hang on a row past
-- the one it produces (`connect-causal`).
module Connect {A B : Set} (s : Den A) (F : Den A → Den B) (p : Pos) where

  r : Pos
  r = p ++ [ ix 1 ]

  σ : EmissionSet A
  σ = enter s r

  β : EmissionSet B
  β = enter (F (hot (Proper σ))) (p ++ [ ix 0 ])

  -- The body has not ended by `q`.
  Alive : Pos → Set
  Alive q = ∀ {c} → β c end → q ≺ c

  data ConnT : EmissionSet B where
    body   : ∀ {k e} → β k e → ConnT k e
    shown  : ∀ {k e} → σ k e → Alive k → ConnT (k ++ [ ix 0 ]) skip
    pinned : ∀ {k e} → σ k e → ¬ Alive k → T (inside r k) → ConnT k skip

connectᵀ : ∀ {A B} → Den A → (Den A → Den B) → Den B
connectᵀ s F = cold λ p → Connect.ConnT s F p

------------------------------------------------------------------------
-- FlatMap

flatMapᵀ : ∀ {A B} → FlatOp → (A → Den B) → Den A → Den B
flatMapᵀ (mergeᶠ nothing)  f s = cold λ p → Merge.MergeT f (enter s p)
flatMapᵀ (mergeᶠ (just n)) f s = cold λ p → Bounded.BoundedT n f (enter s p)
flatMapᵀ switchᶠ           f s = cold λ p → Switch.SwitchT f (enter s p)
flatMapᵀ exhaustᶠ          f s = cold λ p → Exhaust.ExhaustT f (enter s p)

------------------------------------------------------------------------
-- A program tree's emission set

DenEnv : List Set → Set₁
DenEnv = All Den

-- APPROXIMANT n: every path through more than n `defer`s cut off at ⊥ᵀ,
-- as `denotation.Denote`'s.
approxᵀ : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → Den A
approxᵀ n       (cold c)          ρ = coldᵀ c
approxᵀ n       empty             ρ = emptyᵀ
approxᵀ n       (of xs)           ρ = ofᵀ xs
approxᵀ n       (map f s)         ρ = mapᵀ f (approxᵀ n s ρ)
approxᵀ n       (scan f z s)      ρ = scanᵀ f z (approxᵀ n s ρ)
approxᵀ n       (takeWhile i p s) ρ = takeWhileᵀ i p (approxᵀ n s ρ)
approxᵀ n       (flatMap op f s)  ρ = flatMapᵀ op (λ a → approxᵀ n (f a) ρ) (approxᵀ n s ρ)
approxᵀ n       (connect s b)     ρ = connectᵀ (approxᵀ n s ρ) λ h → approxᵀ n b (h ∷ ρ)
approxᵀ n       (connected i)     ρ = lookup ρ i
approxᵀ zero    (defer l)         ρ = ⊥ᵀ
approxᵀ (suc n) (defer l)         ρ = deferᵀ (approxᵀ n (Later.force l) ρ)

-- THE LIMIT: a row every approximant has from some index on.
data Lim {A : Set} (c : ℕ → EmissionSet A) (q : Pos) (e : Ev A) : Set where
  from : ∀ N → (∀ n → N ≤ n → c n q e) → Lim c q e

-- THE MEANING: each operator applied to its children's meanings.  Only a
-- `defer`, the one recursion, is a limit: of its approximants.
⟦_⟧ᵀ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
⟦ cold c ⟧ᵀ          ρ = coldᵀ c
⟦ empty ⟧ᵀ           ρ = emptyᵀ
⟦ of xs ⟧ᵀ           ρ = ofᵀ xs
⟦ map f s ⟧ᵀ         ρ = mapᵀ f (⟦ s ⟧ᵀ ρ)
⟦ scan f z s ⟧ᵀ      ρ = scanᵀ f z (⟦ s ⟧ᵀ ρ)
⟦ takeWhile i p s ⟧ᵀ ρ = takeWhileᵀ i p (⟦ s ⟧ᵀ ρ)
⟦ flatMap op f s ⟧ᵀ  ρ = flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
⟦ connect s b ⟧ᵀ     ρ = connectᵀ (⟦ s ⟧ᵀ ρ) λ h → ⟦ b ⟧ᵀ (h ∷ ρ)
⟦ connected i ⟧ᵀ     ρ = lookup ρ i
⟦ defer l ⟧ᵀ         ρ = cold λ p → Lim λ n → enter (approxᵀ n (defer l) ρ) p
