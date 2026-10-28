{-# OPTIONS --guardedness #-}

-- THE EMISSION SET, LISTED: the rows `denotation.EmissionSet` gives a program, as a
-- list, up to a horizon — what the oracle checks the emission set against rxjs
-- by.  A development tool: no proof reads it.  Each clause mirrors one of
-- the emission set's.
module quickcheck.Tabled where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr; length) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _≡ᵇ_; _<ᵇ_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Time; Timeline; timelineAt; _<ᵖ_; _≟ᵖ_; inside; ix; sub; last; root)
open import denotation.MonotonicList using (start; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; below)
open import Relation.Nullary using (does)
open import quickcheck.Oracle using (Event; val; _▸_; Trace; completed; silent; cut; depth; showTrace)
open import quickcheck.Code using (Prog; toObs; timeline)
open import Data.String using (String)
import quickcheck.Oracle as O

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

-- `EmissionSet.Merge.MergeT`, each value's lane listed at its subscription.
module MergeL {A B : Set} (o : Listed A) (ls : List (Pos × A × Listed B)) where
  done : Pos → Bool
  done c = endBy (rows o) c ∧ allᵇ (λ { (_ , _ , l) → endBy (rows l) c }) ls

  laneRow : Row B → Row B
  laneRow (c , end) = c , (if done c then end else skip)
  laneRow r         = r

  mergeRows : Listed B
  mergeRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (_ , _ , l) → mapL laneRow (rows l) }) ls)
            ⊣ (short o ∨ anyᵇ (λ { (_ , _ , l) → short l }) ls)
open MergeL public using (mergeRows)

-- `EmissionSet.Scan.ScanT`: each value with the fold up to it.
module ScanL {A B : Set} (f : B → A → B) (z : B) (o : Listed A) where
  vals : List (Pos × A)
  vals = values (sort (rows o))

  foldTo : Pos → B → List (Pos × A) → B
  foldTo q b []             = b
  foldTo q b ((k , a) ∷ vs) = foldTo q (if k ≼ᵇ q then f b a else b) vs

  scanRow : Row A → Row B
  scanRow (q , out a) = q , out (foldTo q z vals)
  scanRow (q , skip)  = q , skip
  scanRow (q , end)   = q , end

  scanRows : Listed B
  scanRows = mapL scanRow (rows o) ⊣ short o
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

  latest : Pos → Bool
  latest q = allᵇ (λ { (q′ , _) → q′ ≼ᵇ q }) vals

  done : Pos → Bool
  done c = endBy (rows o) c ∧ allᵇ (λ { (q , _ , l) → not (latest q) ∨ endBy (rows l) c }) ls

  live : Row B → Row B
  live (c , end) = c , (if done c then end else skip)
  live r         = r

  laneRow : Pos → Row B → List (Row B)
  laneRow q (k , e) = if cutᵇ q k then when (inside (q ++ [ ix 1 ]) k) (k , skip) else [ live (k , e) ]

  switchRows : Listed B
  switchRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (q , _ , l) → concatMap (laneRow q) (rows l) }) ls)
             ⊣ (short o ∨ anyᵇ (λ { (_ , _ , l) → short l }) ls)
open SwitchL public using (switchRows)

-- `EmissionSet.Exhaust.ExhaustT`: a merge of the lanes run, in value order,
-- each run if the last lane run has ended before its value.
module ExhaustL {A B : Set} (lane : A → Pos → Maybe (Listed B)) (o : Listed A) where
  free : Maybe (List Pos) → Pos → Bool
  free nothing   q = true
  free (just es) q = anyᵇ (λ c → c <ᵖ q) es

  runL : Maybe (List Pos) → List (Pos × A) → Maybe (List (Pos × A × Listed B))
  runL st []             = just []
  runL st ((q , a) ∷ vs) =
    if free st q
    then bind (lane a (q ++ [ ix 1 ])) (λ l → bind (runL (just (ends (rows l))) vs) λ rs → just ((q , a , l) ∷ rs))
    else runL st vs

  listE : Maybe (Listed B)
  listE = bind (runL nothing (values (sort (rows o)))) λ rs → just (mergeRows o rs)

-- `EmissionSet.Bounded.BoundedT`: lanes placed in value order, each where
-- `EmissionSet.Bounded.Starts` puts it; one held holds every later one.
module BoundedL {A B : Set} (n : ℕ) (lane : A → Pos → Maybe (Listed B)) (o : Listed A) where
  vals : List (Pos × A)
  vals = values (sort (rows o))

  -- `es`'s k-th in position order, from 0, among `cs`.
  kth : ℕ → List Pos → List Pos → Maybe Pos
  kth k es []       = nothing
  kth k es (c ∷ cs) = if below c es ≡ᵇ k then just c else kth k es cs

  -- Where lane i starts; `nothing` if held.
  startAt : ℕ → Pos → List Pos → Maybe Pos
  startAt i q es =
    if i <ᵇ n then just (q ++ [ ix 1 ])
    else bind (kth (i ∸ n) es es) λ c → just (if c <ᵖ q then q ++ [ ix 1 ] else c ++ [ ix 1 ])

  mutual
    schedL : ℕ → List Pos → List (Pos × A) → Maybe (List (Pos × Listed B))
    schedL i es []             = just []
    schedL i es ((q , a) ∷ vs) = placed i es a vs (startAt i q es)

    placed : ℕ → List Pos → A → List (Pos × A) → Maybe Pos → Maybe (List (Pos × Listed B))
    placed i es a vs nothing  = just []
    placed i es a vs (just s) =
      bind (lane a s) λ l → bind (schedL (suc i) (ends (rows l) ++ es) vs) λ rs → just ((s , l) ∷ rs)

  module _ (sc : List (Pos × Listed B)) where
    queued : Pos → Bool
    queued c = anyᵇ (λ { (s , _) → does (s ≟ᵖ (c ++ [ ix 1 ])) }) sc

    done : Pos → Bool
    done c = endBy (rows o) c ∧ (length sc ≡ᵇ length vals) ∧ allᵇ (λ { (_ , l) → endBy (rows l) c }) sc

    laneRow : Row B → Row B
    laneRow (c , end) = if queued c then (c ++ [ ix 0 ] , skip) else (c , (if done c then end else skip))
    laneRow r         = r

    boundedRows : Listed B
    boundedRows = (concatMap (outerRow done) (rows o) ++ concatMap (λ { (_ , l) → mapL laneRow (rows l) }) sc)
                ⊣ (short o ∨ anyᵇ (λ { (_ , l) → short l }) sc)

  listB : Maybe (Listed B)
  listB = bind (schedL 0 [] vals) λ sc → just (boundedRows sc)

-- `EmissionSet.Connect.ConnT`.
module ConnL {A B : Set} (r : Pos) (σ : Listed A) (β : Listed B) where
  alive : Pos → Bool
  alive q = allᵇ (λ { (c , e) → not (isEnd e) ∨ (q <ᵖ c) }) (rows β)

  shown : Row A → List (Row B)
  shown (k , _) =
    if alive (k ++ [ ix 0 ]) then [ k ++ [ ix 0 ] , skip ]
    else when (inside r k) (k , skip)

  connRows : Listed B
  connRows = (rows β ++ concatMap shown (rows σ)) ⊣ (short σ ∨ short β)
open ConnL public using (connRows)

------------------------------------------------------------------------
-- A program tree, listed

-- `EmissionSet.approxᵀ`'s clauses, approximant n, subscribed at `p`.
listT : ∀ {Γ A} → ℕ → Obs Timeline Γ A → All Listed Γ → Pos → Maybe (Listed A)
listT n       (cold c)          ρ p = just (walk fuel (start p (timelineAt c p)))
listT n       empty             ρ p = just ([ p ++ [ last ] , end ] ⊣ false)
listT n       (of xs)           ρ p = just (walk fuel (ofᴱ p 0 xs))
listT n       (map f s)         ρ p = bind (listT n s ρ p) λ l → just (mapRows f l)
listT n       (scan f z s)      ρ p = bind (listT n s ρ p) λ l → just (scanRows f z l)
listT n       (takeWhile i q s) ρ p = bind (listT n s ρ p) λ l → just (takeRows i q p l)
listT n       (flatMap (mergeᶠ nothing) f s) ρ p =
  bind (listT n s ρ p) λ o →
  bind (mapM (λ qa → bind (listT n (f (proj₂ qa)) ρ (proj₁ qa ++ [ ix 1 ])) λ l → just (proj₁ qa , proj₂ qa , l)) (values (rows o))) λ ls →
  just (mergeRows o ls)
listT n       (flatMap (mergeᶠ (just k)) f s) ρ p =
  bind (listT n s ρ p) λ o → BoundedL.listB k (λ a → listT n (f a) ρ) o
listT n       (flatMap switchᶠ f s) ρ p =
  bind (listT n s ρ p) λ o →
  bind (mapM (λ qa → bind (listT n (f (proj₂ qa)) ρ (proj₁ qa ++ [ ix 1 ])) λ l → just (proj₁ qa , proj₂ qa , l)) (values (rows o))) λ ls →
  just (switchRows o ls)
listT n       (flatMap exhaustᶠ f s) ρ p =
  bind (listT n s ρ p) λ o → ExhaustL.listE (λ a → listT n (f a) ρ) o
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
