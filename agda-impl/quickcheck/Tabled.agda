{-# OPTIONS --guardedness #-}

-- THE EMISSION SET, LISTED: the rows `denotation.EmissionSet` gives a program, as a
-- list, up to a horizon — what the oracle checks the emission set against rxjs
-- by.  A development tool: no proof reads it.  Each clause mirrors one of
-- the emission set's.
module quickcheck.Tabled where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr; length; null; deduplicate) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_; _<ᵇ_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.Events as E
open import denotation.Events using (Pos; Time; Timeline; timelineAt; _<ᵖ_; _≟ᵖ_; inside; ix; sub; last; root)
open import denotation.Events using (start; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end)
open import Relation.Nullary using (does)
open import quickcheck.Trace using (Event; val; _▸_; Trace; completed; silent; cut; depth; showTrace)
open import quickcheck.Code using (Prog; toObs; timeline)
open import Data.String using (String)
import Data.String as S
open import Data.Nat.Show using () renaming (show to showℕ)
import quickcheck.Trace as O

------------------------------------------------------------------------
-- Listings

Row : Set → Set
Row A = Pos × Ev A

-- The rows, and whether a budget cut them short anywhere.  An uncut
-- listing holds exactly its emission set's rows (`quickcheck.Tabled.Exact`), so
-- each decision below is its emission set predicate, read off the rows.
record Listed (A : Set) : Set where
  constructor _⊣_
  field
    rows  : List (Row A)
    short : Bool
open Listed public

bind : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bind nothing  k = nothing
bind (just x) k = k x

-- `concatMap`, `anyᵇ` and `allᵇ` recurse rather than fold, so a proof
-- (`quickcheck.Tabled.Exact`) can read the function back off a stuck call.
concatMap : ∀ {X Y : Set} → (X → List Y) → List X → List Y
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

mapM : ∀ {X Y : Set} → (X → Maybe Y) → List X → Maybe (List Y)
mapM f []       = just []
mapM f (x ∷ xs) = bind (f x) λ y → bind (mapM f xs) λ ys → just (y ∷ ys)

concatMapM : ∀ {X Y : Set} → (X → Maybe (List Y)) → List X → Maybe (List Y)
concatMapM f []       = just []
concatMapM f (x ∷ xs) = bind (f x) λ ys → bind (concatMapM f xs) λ zs → just (ys ++ zs)

when : ∀ {X : Set} → Bool → X → List X
when b x = if b then [ x ] else []

anyᵇ : ∀ {X : Set} → (X → Bool) → List X → Bool
anyᵇ p []       = false
anyᵇ p (x ∷ xs) = p x ∨ anyᵇ p xs

allᵇ : ∀ {X : Set} → (X → Bool) → List X → Bool
allᵇ p []       = true
allᵇ p (x ∷ xs) = p x ∧ allᵇ p xs

_≼ᵇ_ : Pos → Pos → Bool
p ≼ᵇ q = not (q <ᵖ p)

isEnd : ∀ {A} → Ev A → Bool
isEnd end = true
isEnd _   = false

-- An end row at or before `c`.
endBy : ∀ {A} → List (Row A) → Pos → Bool
endBy rs c = anyᵇ (λ { (k , e) → isEnd e ∧ (k ≼ᵇ c) }) rs

-- An end row strictly before `c`.
endBefore : ∀ {A} → List (Row A) → Pos → Bool
endBefore rs c = anyᵇ (λ { (k , e) → isEnd e ∧ (k <ᵖ c) }) rs

-- The positions of the end rows.
ends : ∀ {A} → List (Row A) → List Pos
ends = concatMap λ { (k , e) → when (isEnd e) k }

-- `EmissionSet.Proper`: at or before every end.
properᵇ : ∀ {A} → List (Row A) → Pos → Bool
properᵇ rs q = allᵇ (λ { (c , e) → not (isEnd e) ∨ (q ≼ᵇ c) }) rs

proper : ∀ {A} → List (Row A) → List (Row A)
proper rs = concatMap (λ { (q , e) → when (properᵇ rs q) (q , e) }) rs

values : ∀ {A} → List (Row A) → List (Pos × A)
values []                  = []
values ((q , out a) ∷ rs)  = (q , a) ∷ values rs
values (_ ∷ rs)            = values rs

-- `EmissionSet.Values`, over an input's listed values.  A position may
-- hold several, and each is followed.
module Order {A : Set} (vs : List (Pos × A)) where
  -- No value before `q`.
  minᵇ : Pos → Bool
  minᵇ q = allᵇ (λ { (k , _) → q ≼ᵇ k }) vs

  -- `q′` is the first value after `q`.
  nextᵇ : Pos → Pos → Bool
  nextᵇ q q′ = (q <ᵖ q′) ∧ allᵇ (λ { (k , _) → not (q <ᵖ k) ∨ (q′ ≼ᵇ k) }) vs

  -- The values first after one of `prev`.
  after : List (Pos × A) → List (Pos × A)
  after prev = concatMap (λ { (q′ , a′) → when (anyᵇ (λ { (q , _) → nextᵇ q q′ }) prev) (q′ , a′) }) vs

  -- `Values.Nth`.
  nths : ℕ → List (Pos × A)
  nths zero    = concatMap (λ { (q , a) → when (minᵇ q) (q , a) }) vs
  nths (suc i) = after (nths i)

private
  cons : ∀ {A} → Row A → Listed A → Listed A
  cons x (rs ⊣ b) = (x ∷ rs) ⊣ b

-- How far a leaf is walked, and the tick it is read up to.
fuel : ℕ
fuel = 10000

horizon : Time
horizon = 100

-- A stream's rows, up to the horizon.
walk : ∀ {A} → ℕ → E.Events A → Listed A
walk zero    _             = [] ⊣ true
walk (suc n) (E.out k a r) = if E.tick k ≤ᵇ horizon then cons (k , out a) (walk n (E.Events∞.force r)) else [] ⊣ true
walk (suc n) (E.skip k r)  = if E.tick k ≤ᵇ horizon then cons (k , skip) (walk n (E.Events∞.force r)) else [] ⊣ true
walk (suc n) (E.end k)     = if E.tick k ≤ᵇ horizon then ((k , end) ∷ []) ⊣ false else [] ⊣ true
walk (suc n) E.hush        = [] ⊣ false

private
  insert : ∀ {A} → Row A → List (Row A) → List (Row A)
  insert x []       = [ x ]
  insert (q , e) ((k , d) ∷ ys) = if q <ᵖ k then (q , e) ∷ (k , d) ∷ ys else (k , d) ∷ insert (q , e) ys

  sort : ∀ {A} → List (Row A) → List (Row A)
  sort = foldr insert []

------------------------------------------------------------------------
-- The operators

mapRow : ∀ {A B} → (A → B) → Row A → Row B
mapRow f (q , out a) = q , out (f a)
mapRow f (q , skip)  = q , skip
mapRow f (q , end)   = q , end

mapRows : ∀ {A B} → (A → B) → Listed A → Listed B
mapRows f (rs ⊣ b) = mapL (mapRow f) rs ⊣ b

-- `EmissionSet.Rejoin`, over a hot's rows.
rejoinRow : ∀ {A} → Pos → Row A → List (Row A)
rejoinRow p (q , end) = if p <ᵖ q then [ q ++ [ sub p ] , end ] else [ p ++ [ last ] , end ]
rejoinRow p (q , e)   = when (p <ᵖ q) (q ++ [ sub p ] , e)

rejoin : ∀ {A} → Pos → Listed A → Listed A
rejoin p (rs ⊣ b) = concatMap (rejoinRow p) rs ⊣ b

-- `EmissionSet.Proper`.
hotOf : ∀ {A} → Listed A → Listed A
hotOf (rs ⊣ b) = proper rs ⊣ b

-- An outer's row at a flattening frame, given whether an end there ends
-- the whole.
outerRow : ∀ {A B : Set} → (Pos → Bool) → Row A → List (Row B)
outerRow d (q , out _) = [ q ++ [ ix 0 ] , skip ]
outerRow d (q , skip)  = [ q , skip ]
outerRow d (c , end)   = [ c , (if d c then end else skip) ]

-- `EmissionSet.After`: the rows past `s`.
pastRows : ∀ {A} → Pos → List (Row A) → List (Row A)
pastRows s []             = []
pastRows s ((k , e) ∷ rs) = if s <ᵖ k then (k , e) ∷ pastRows s rs else pastRows s rs

past : ∀ {A} → Pos → Listed A → Listed A
past s (rs ⊣ b) = pastRows s rs ⊣ b

-- A lane listing, read past its subscription.
afterL : ∀ {A B : Set} → (A → Pos → Maybe (Listed B)) → A → Pos → Maybe (Listed B)
afterL ln a s = bind (ln a s) λ l → just (past s l)

-- Each value's lane, listed at its subscription.
lanes : ∀ {A B : Set} → (A → Pos → Maybe (Listed B)) → List (Pos × A) → Maybe (List (Pos × A × Listed B))
lanes ln = mapM λ qa → bind (ln (proj₂ qa) (proj₁ qa ++ [ ix 1 ])) λ l → just (proj₁ qa , proj₂ qa , l)

-- `EmissionSet.Merge.MergeT`, each value's lane listed at its subscription.
module MergeL {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) where
  done : Pos → Bool
  done c = endBy (rows o) c ∧ allᵇ (λ { (q , _ , l) → not (q <ᵖ c) ∨ endBy (rows l) c }) ls

  laneRow : Row B → Row B
  laneRow (c , end) = c , (if done c then end else skip)
  laneRow r         = r

  mergeRows : Listed B
  mergeRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (_ , _ , l) → mapL laneRow (rows l) }) ls)
            ⊣ (short o ∨ anyᵇ (λ { (_ , _ , l) → short l }) ls)
open MergeL public using (mergeRows)

-- `EmissionSet.Scan.ScanT`: level by level, as `Values.Nth` counts, each
-- value with the folds ending at it, read off the level before.
module ScanL {A B : Set} (f : B → A → B) (z : B) (o : Listed A) where
  vals : List (Pos × A)
  vals = values (rows o)
  open Order vals using (nextᵇ; after; nths)

  opening : Pos × A → Pos × A × List B
  opening (q , a) = q , a , [ f z a ]

  -- The folds ending at the value `a` at `q`, from the level before.
  step : List (Pos × A × List B) → Pos × A → Pos × A × List B
  step cur (q , a) = q , a , concatMap (λ { (q₀ , _ , bs) → if nextᵇ q₀ q then mapL (λ b → f b a) bs else [] }) cur

  -- Levels up to `k` on, from level `cur` holding the values `vs`; the
  -- next level's values are passed on rather than recomputed.
  mutual
    levels : ℕ → List (Pos × A) → List (Pos × A × List B) → List (Pos × A × List B)
    levels zero    vs cur = []
    levels (suc k) vs cur = cur ++ onward k (after vs) cur

    onward : ℕ → List (Pos × A) → List (Pos × A × List B) → List (Pos × A × List B)
    onward k vs cur = levels k vs (mapL (step cur) vs)

  table : List (Pos × A × List B)
  table = levels (length vals) (nths 0) (mapL opening (nths 0))

  folds : Pos × A × List B → List (Row B)
  folds (q , _ , bs) = mapL (λ b → q , out b) bs

  others : Row A → List (Row B)
  others (q , out _) = []
  others (q , skip)  = [ q , skip ]
  others (q , end)   = [ q , end ]

  scanRows : Listed B
  scanRows = (concatMap folds table ++ concatMap others (rows o)) ⊣ short o
open ScanL public using (scanRows)

-- `EmissionSet.TakeWhile.TakeT`, subscribed at `p`.
module TakeL {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) (o : Listed A) where
  failed : Pos → Bool
  failed k = anyᵇ (λ { (q , a) → not (keep a) ∧ (q <ᵖ k) }) (values (rows o))

  kept : Row A → List (Row A)
  kept (q , out a) = if keep a then [ q , out a ] else when incl (q ++ [ ix 0 ] , out a) ++ [ q ++ [ last ] , end ]
  kept r           = [ r ]

  takeRow : Row A → List (Row A)
  takeRow (q , e) = if failed q then when (inside p q) (q , skip) else kept (q , e)

  takeRows : Listed A
  takeRows = concatMap takeRow (rows o) ⊣ short o
open TakeL public using (takeRows)

-- `EmissionSet.Switch.SwitchT`, each value's lane listed at its subscription.
module SwitchL {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) where
  vals : List (Pos × A)
  vals = values (rows o)

  cutᵇ : Pos → Pos → Bool
  cutᵇ q k = anyᵇ (λ { (q′ , _) → (q <ᵖ q′) ∧ (q′ <ᵖ k) }) vals

  latest : Pos → Pos → Bool
  latest q c = allᵇ (λ { (q′ , _) → not (q′ <ᵖ c) ∨ (q′ ≼ᵇ q) }) vals

  done : Pos → Bool
  done c = endBy (rows o) c ∧ allᵇ (λ { (q , _ , l) → not (q <ᵖ c) ∨ (not (latest q c) ∨ endBy (rows l) c) }) ls

  live : Row B → Row B
  live (c , end) = c , (if done c then end else skip)
  live r         = r

  laneRow : Pos → Row B → List (Row B)
  laneRow q (k , e) = if cutᵇ q k then when (inside (q ++ [ ix 1 ]) k) (k , skip) else [ live (k , e) ]

  switchRows : Listed B
  switchRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (q , _ , l) → concatMap (laneRow q) (rows l) }) ls)
             ⊣ (short o ∨ anyᵇ (λ { (_ , _ , l) → short l }) ls)
open SwitchL public using (switchRows)

-- `EmissionSet.Exhaust.ExhaustT`, each value's lane listed at its
-- subscription: a merge of the lanes run.
module ExhaustL {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) where
  vals : List (Pos × A)
  vals = values (rows o)
  open Order vals using (minᵇ; nextᵇ)

  -- `Exhaust.Cur`'s step at the value at `q₂`, from a lane of the last
  -- run at `q`: ended before it, `q₂` runs; ended nowhere before it, `q`
  -- stays the last run.
  moves : Pos → Pos → Pos × A × Listed B → List Pos
  moves q₂ q (q′ , _ , l) =
    if does (q′ ≟ᵖ q) then when (endBefore (rows l) q₂) q₂ ++ when (properᵇ (rows l) q₂) q else []

  -- `Exhaust.Cur`: the last runs at the value at `q₂`, through at most `n`
  -- values.
  mutual
    curs : ℕ → Pos → List Pos
    curs zero    q₂ = []
    curs (suc n) q₂ = when (minᵇ q₂) q₂ ++ concatMap (prior n q₂) vals

    prior : ℕ → Pos → Pos × A → List Pos
    prior n q₂ (q₁ , _) = if nextᵇ q₁ q₂ then concatMap (λ q → concatMap (moves q₂ q) ls) (curs n q₁) else []

  -- `Exhaust.Run`.
  runᵇ : Pos → Bool
  runᵇ q = anyᵇ (λ q′ → does (q′ ≟ᵖ q)) (curs (suc (length vals)) q)

  -- The lanes that run, found once and passed on.
  runs : List Pos
  runs = concatMap (λ { (q , _ , _) → when (runᵇ q) q }) ls

  module Ran (rs : List Pos) where
    ranᵇ : Pos → Bool
    ranᵇ q = anyᵇ (λ q′ → does (q′ ≟ᵖ q)) rs

    done : Pos → Bool
    done c = endBy (rows o) c ∧ allᵇ (λ { (q , _ , l) → not (q <ᵖ c) ∨ (not (ranᵇ q) ∨ endBy (rows l) c) }) ls

    laneRow : Row B → Row B
    laneRow (c , end) = c , (if done c then end else skip)
    laneRow r         = r

    ranRows : Listed B
    ranRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (q , _ , l) → if ranᵇ q then mapL laneRow (rows l) else [] }) ls)
            ⊣ (short o ∨ anyᵇ (λ { (_ , _ , l) → short l }) ls)

  exhaustRows : Listed B
  exhaustRows = Ran.ranRows runs
open ExhaustL public using (exhaustRows)

-- `EmissionSet.Bounded.BoundedT`: level by level, each value's lane at
-- every start `Starts` allows, and each level's ends passed on to the
-- next.
module BoundedL {A B : Set} (n : ℕ) (lane : A → Pos → Maybe (Listed B)) (o : Listed A) where
  vals : List (Pos × A)
  vals = values (rows o)
  open Order vals using (after; nths)

  -- How many of the lanes, each by its ends, end where `p` holds:
  -- `Bounded.Kth` holds at k when this is past k.
  count : (Pos → Bool) → List (List Pos) → ℕ
  count p []         = 0
  count p (es ∷ ess) = if anyᵇ p es then suc (count p ess) else count p ess

  -- `Bounded.Starts`, given the lanes before.
  queuedAt : ℕ → Pos → List (List Pos) → Pos → List Pos
  queuedAt i q ess c =
    when ((q <ᵖ c) ∧ ((suc (i ∸ n) ≤ᵇ count (λ k → k ≼ᵇ c) ess) ∧ not (suc (i ∸ n) ≤ᵇ count (λ k → k <ᵖ c) ess))) (c ++ [ ix 1 ])

  starts : ℕ → Pos → List (List Pos) → List Pos
  starts i q ess =
    if i <ᵇ n then [ q ++ [ ix 1 ] ]
    else (if suc (i ∸ n) ≤ᵇ count (λ k → k <ᵖ q) ess then [ q ++ [ ix 1 ] ]
    else concatMap (concatMap (queuedAt i q ess)) ess)

  -- A value, and its lane at each start.
  Entry : Set
  Entry = Pos × A × List (Pos × Listed B)

  laneAt : A → Pos → Maybe (Pos × Listed B)
  laneAt a s = bind (lane a s) λ l → just (s , l)

  entry : ℕ → List (List Pos) → Pos × A → Maybe Entry
  entry i ess (q , a) = bind (mapM (laneAt a) (starts i q ess)) λ ss → just (q , a , ss)

  -- A level's lane ends.
  laneEnds : Pos × Listed B → List Pos
  laneEnds (_ , l) = ends (rows l)

  entryEnds : Entry → List Pos
  entryEnds (_ , _ , ss) = concatMap laneEnds ss

  endsOf : List Entry → List Pos
  endsOf = concatMap entryEnds

  -- Levels `i` up to `i + k`, from the lanes `ess` before level `i` and
  -- its values `vs` (`nths i`).
  levels : ℕ → ℕ → List (List Pos) → List (Pos × A) → Maybe (List (ℕ × Entry))
  levels zero    i ess vs = just []
  levels (suc k) i ess vs =
    bind (mapM (entry i ess) vs) λ gs →
    bind (levels k (suc i) (endsOf gs ∷ ess) (after vs)) λ rest → just (mapL (i ,_) gs ++ rest)

  module _ (gs : List (ℕ × Entry)) where
    queued : Pos → Bool
    queued c = anyᵇ (λ { (_ , _ , _ , ss) → anyᵇ (λ { (s , _) → does (s ≟ᵖ (c ++ [ ix 1 ])) }) ss }) gs

    done : Pos → Bool
    done c = endBy (rows o) c ∧ allᵇ (λ { (_ , q , _ , ss) → not (q <ᵖ c) ∨ anyᵇ (λ { (_ , l) → endBy (rows l) c }) ss }) gs

    laneRow : Row B → Row B
    laneRow (c , end) = if queued c then (c ++ [ ix 0 ] , skip) else (c , (if done c then end else skip))
    laneRow r         = r

    boundedRows : Listed B
    boundedRows = (concatMap (outerRow done) (rows o)
                    ++ concatMap (λ { (_ , _ , _ , ss) → concatMap (λ { (_ , l) → mapL laneRow (rows l) }) ss }) gs)
                ⊣ (short o ∨ anyᵇ (λ { (_ , _ , _ , ss) → anyᵇ (λ { (_ , l) → short l }) ss }) gs)

  listB : Maybe (Listed B)
  listB = bind (levels (length vals) 0 [] (nths 0)) λ gs → just (boundedRows gs)

-- `EmissionSet.Connect.ConnT`.
module ConnL {A B : Set} (r : Pos) (σ : Listed A) (β : Listed B) where
  alive : Pos → Bool
  alive q = allᵇ (λ { (c , e) → not (isEnd e) ∨ (q <ᵖ c) }) (rows β)

  shown : Row A → List (Row B)
  shown (k , _) =
    if alive k then [ k ++ [ ix 0 ] , skip ]
    else when (inside r k) (k , skip)

  connRows : Listed B
  connRows = (rows β ++ concatMap shown (rows σ)) ⊣ (short σ ∨ short β)
open ConnL public using (connRows)

------------------------------------------------------------------------
-- A program tree, listed

-- `EmissionSet.approx`'s clauses, approximant n, subscribed at `p`.
listT : ∀ {Γ A} → ℕ → Obs Timeline Γ A → All Listed Γ → Pos → Maybe (Listed A)
listT n       (cold c)          ρ p = just (walk fuel (start p (timelineAt c p)))
listT n       empty             ρ p = just ([ p ++ [ last ] , end ] ⊣ false)
listT n       (of xs)           ρ p = just (walk fuel (ofᴱ p 0 xs))
listT n       (map f s)         ρ p = bind (listT n s ρ p) λ l → just (mapRows f l)
listT n       (scan f z s)      ρ p = bind (listT n s ρ p) λ l → just (scanRows f z l)
listT n       (takeWhile i q s) ρ p = bind (listT n s ρ p) λ l → just (takeRows i q p l)
listT n       (flatMap (mergeᶠ nothing) f s) ρ p =
  bind (listT n s ρ p) λ o → bind (lanes (afterL (λ a → listT n (f a) ρ)) (values (rows o))) λ ls → just (mergeRows o ls)
listT n       (flatMap (mergeᶠ (just k)) f s) ρ p =
  bind (listT n s ρ p) λ o → BoundedL.listB k (afterL (λ a → listT n (f a) ρ)) o
listT n       (flatMap switchᶠ f s) ρ p =
  bind (listT n s ρ p) λ o → bind (lanes (afterL (λ a → listT n (f a) ρ)) (values (rows o))) λ ls → just (switchRows o ls)
listT n       (flatMap exhaustᶠ f s) ρ p =
  bind (listT n s ρ p) λ o → bind (lanes (afterL (λ a → listT n (f a) ρ)) (values (rows o))) λ ls → just (exhaustRows o ls)
listT n       (connect s b)     ρ p =
  bind (listT n s ρ (p ++ [ ix 1 ])) λ σ →
  bind (listT n b (hotOf σ ∷ ρ) (p ++ [ ix 0 ])) λ β →
  just (connRows (p ++ [ ix 1 ]) σ β)
listT n       (connected i)     ρ p = just (rejoin p (lookup ρ i))
listT zero    (defer l)         ρ p = just ([] ⊣ true)
listT (suc n) (defer l)         ρ p =
  bind (listT n (Later.force l) ρ (p ++ [ ix 1 ])) λ b → just (cons (p ++ [ ix 0 ] , skip) b)

------------------------------------------------------------------------
-- The trace

-- Values in position order, a tick opening each frame; completed if the
-- emission set ends, cut if a budget cut it short, silent otherwise.
traceT : ∀ {A} → Listed A → Trace A
traceT {A} (rs ⊣ b) = go nothing (sort (proper rs)) ▸ finish
  where
    go : Maybe Time → List (Row A) → List (Event A)
    go t []                   = []
    go t ((q , out a) ∷ xs) with t
    ... | just s = if s ≡ᵇ E.tick q then val a ∷ go t xs else O.tick (E.tick q) ∷ val a ∷ go (just (E.tick q)) xs
    ... | nothing = O.tick (E.tick q) ∷ val a ∷ go (just (E.tick q)) xs
    go t (_ ∷ xs)             = go t xs

    finish : O.End
    finish = if anyᵇ (λ { (_ , e) → isEnd e }) rs then completed else if b then cut else silent

-- A generated program's emission set, as the oracle reads it, unfolded as the
-- denotation's trace is; `null` if it lists nothing.
tableJSON : ∀ {t} → ℕ → Prog t → String
tableJSON {t} u p with listT (depth u p) (toObs timeline u p [] [] []) [] root
... | just l  = showTrace t (traceT l)
... | nothing = "null"

------------------------------------------------------------------------
-- Where the listing spends its time

private
  nodeName : ∀ {Γ A} → Obs Timeline Γ A → String
  nodeName (cold _)                    = "cold"
  nodeName empty                       = "empty"
  nodeName (of _)                      = "of"
  nodeName (map _ _)                   = "map"
  nodeName (scan _ _ _)                = "scan"
  nodeName (takeWhile _ _ _)           = "takeWhile"
  nodeName (flatMap (mergeᶠ nothing) _ _)  = "merge"
  nodeName (flatMap (mergeᶠ (just k)) _ _) = "merge " S.++ showℕ k
  nodeName (flatMap switchᶠ _ _)       = "switch"
  nodeName (flatMap exhaustᶠ _ _)      = "exhaust"
  nodeName (connect _ _)               = "connect"
  nodeName (connected _)               = "connected"
  nodeName (defer _)                   = "defer"

  size : ∀ {A} → Maybe (Listed A) → String
  size (just l) = showℕ (length (rows l)) S.++ " rows"
  size nothing  = "nothing"

  laneSize : ∀ {A B : Set} → Maybe (List (Pos × A × Listed B)) → String
  laneSize (just ls) = showℕ (length ls) S.++ " lanes, " S.++ showℕ (foldr (λ { (_ , _ , l) k → length (rows l) + k }) 0 ls) S.++ " rows"
  laneSize nothing   = "nothing"

  lanesOf : ∀ {Γ A B} → ℕ → (A → Obs Timeline Γ B) → Obs Timeline Γ A → All Listed Γ → Pos → List String
  lanesOf n f s ρ p = [ "lanes: " S.++ laneSize (bind (listT n s ρ p) λ o → lanes (afterL (λ a → listT n (f a) ρ)) (values (rows o))) ]

-- Each node of `listT`'s walk: a line opening it, its parts' lines, and a
-- line closing it with its rows; a flatMap's lanes get a line of their own.
mutual
  traceL : ∀ {Γ A} → ℕ → Obs Timeline Γ A → All Listed Γ → Pos → List String
  traceL n o ρ p = ("open " S.++ nodeName o) ∷ (parts n o ρ p ++ [ "close " S.++ nodeName o S.++ ": " S.++ size (listT n o ρ p) ])

  parts : ∀ {Γ A} → ℕ → Obs Timeline Γ A → All Listed Γ → Pos → List String
  parts n (map _ s)                       ρ p = traceL n s ρ p
  parts n (scan _ _ s)                    ρ p = traceL n s ρ p
  parts n (takeWhile _ _ s)               ρ p = traceL n s ρ p
  parts n (flatMap (mergeᶠ (just _)) _ s) ρ p = traceL n s ρ p
  parts n (flatMap k f s)                 ρ p = traceL n s ρ p ++ lanesOf n f s ρ p
  parts n (connect s b)                   ρ p with listT n s ρ (p ++ [ ix 1 ])
  ... | just σ  = traceL n s ρ (p ++ [ ix 1 ]) ++ traceL n b (hotOf σ ∷ ρ) (p ++ [ ix 0 ])
  ... | nothing = traceL n s ρ (p ++ [ ix 1 ])
  parts (suc n) (defer l)                 ρ p = traceL n (Later.force l) ρ (p ++ [ ix 1 ])
  parts _ _                               ρ p = []

-- A generated program's listing, traced node by node.
tableTrace : ∀ {t} → ℕ → Prog t → List String
tableTrace u p = traceL (depth u p) (toObs timeline u p [] [] []) [] root
