{-# OPTIONS --guardedness #-}

-- THE TABLE, LISTED: the rows `denotation.Table` gives a program, as a
-- list, up to a horizon — what the oracle checks the table against rxjs
-- by.  A development tool: no proof reads it.  Each clause mirrors one of
-- the table's; an operator the table leaves out lists nothing.
module quickcheck.Tabled where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; foldr; null) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Tree using (Obs; Later; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Time; Timeline; timelineAt; _<ᵖ_; inside; ix; sub; last; root)
open import denotation.MonotonicList using (start; ofᴱ)
open import denotation.Table using (Ev; out; skip; end)
open import quickcheck.Oracle using (Event; val; _▸_; Trace; completed; silent; cut; depth; showTrace)
open import quickcheck.Code using (Prog; toObs; timeline)
open import Data.String using (String)
import quickcheck.Oracle as O

------------------------------------------------------------------------
-- Listings

Row : Set → Set
Row A = Pos × Ev A

-- The rows, and whether a budget cut them short anywhere.  An uncut
-- listing holds exactly its table's rows (`quickcheck.Tabled.Exact`), so
-- each decision below is its table predicate, read off the rows.
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

-- An end row at or before `c`; strictly before `c`.
endBy endBefore : ∀ {A} → List (Row A) → Pos → Bool
endBy     rs c = anyᵇ (λ { (k , e) → isEnd e ∧ (k ≼ᵇ c) }) rs
endBefore rs c = anyᵇ (λ { (k , e) → isEnd e ∧ (k <ᵖ c) }) rs

-- The positions of the end rows.
ends : ∀ {A} → List (Row A) → List Pos
ends = concatMap λ { (k , e) → when (isEnd e) k }

-- `Table.Proper`: at or before every end.
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

-- `Table.Rejoin`, over a hot's rows.
rejoinRow : ∀ {A} → Pos → Row A → List (Row A)
rejoinRow p (q , end) = if p <ᵖ q then [ q ++ [ sub p ] , end ] else [ p ++ [ last ] , end ]
rejoinRow p (q , e)   = when (p <ᵖ q) (q ++ [ sub p ] , e)

rejoin : ∀ {A} → Pos → Listed A → Listed A
rejoin p (rs ⊣ b) = concatMap (rejoinRow p) rs ⊣ b

-- `Table.Proper`.
hotOf : ∀ {A} → Listed A → Listed A
hotOf (rs ⊣ b) = proper rs ⊣ b

-- An outer's row at a flattening frame, given whether an end there ends
-- the whole.
outerRow : ∀ {A B : Set} → (Pos → Bool) → Row A → List (Row B)
outerRow d (q , out _) = [ q ++ [ ix 0 ] , skip ]
outerRow d (q , skip)  = [ q , skip ]
outerRow d (c , end)   = [ c , (if d c then end else skip) ]

-- `Table.Merge.MergeT`, each value's lane listed at its subscription.
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

-- `Table.Concat`, level by level: lane i is for the outer's i-th value,
-- `nthL i`; a level's group lists, for each such value, its lanes, one
-- per place lane i-1 ended.  Values stand in position order, so there
-- are no more levels than values; one past that is a budget's cut.
module ConcatL {A B : Set} (lane : A → Pos → Maybe (Listed B)) (o : Listed A) where
  vals : List (Pos × A)
  vals = values (rows o)

  -- The value after `q`, if no value lies between.
  after : Pos → Pos × A → List (Pos × A)
  after q (q′ , a′) = when ((q <ᵖ q′) ∧ allᵇ (λ { (k , _) → not (q <ᵖ k) ∨ (q′ ≼ᵇ k) }) vals) (q′ , a′)

  nthL : ℕ → List (Pos × A)
  nthL zero    = concatMap (λ { (q , a) → when (allᵇ (λ { (k , _) → q ≼ᵇ k }) vals) (q , a) }) vals
  nthL (suc i) = concatMap (λ { (q , _) → concatMap (after q) vals }) (nthL i)

  Group : Set
  Group = Pos × A × List (Pos × Listed B)

  -- Where lane i+1, for the value at `q`, may start: past each end of a
  -- lane i, or where its value arrives.
  starts : List Group → Pos → List Pos
  starts gs q = concatMap (λ { (_ , _ , ls) → concatMap (λ { (_ , l) → concatMap (λ c →
                  when (c <ᵖ q) (q ++ [ ix 1 ]) ++ when (q <ᵖ c) (c ++ [ ix 1 ])) (ends (rows l)) }) ls }) gs

  group : List Pos → Pos × A → Maybe Group
  group ss (q , a) = bind (mapM (λ s → bind (lane a s) λ l → just (s , l)) ss) λ ls → just (q , a , ls)

  levelL : ℕ → Maybe (List Group)
  levelL zero    = mapM (λ { (q , a) → group [ q ++ [ ix 1 ] ] (q , a) }) (nthL zero)
  levelL (suc i) = bind (levelL i) λ gs → mapM (λ { (q , a) → group (starts gs q) (q , a) }) (nthL (suc i))

  upto : ℕ → List ℕ
  upto zero    = []
  upto (suc n) = upto n ++ [ n ]

  count : ∀ {X : Set} → List X → ℕ
  count = foldr (λ _ → suc) 0

  lanesOf : List (ℕ × List Group) → List (ℕ × Listed B)
  lanesOf = concatMap λ { (i , gs) → concatMap (λ { (_ , _ , ls) → mapL (λ { (_ , l) → i , l }) ls }) gs }

  module _ (lv : List (ℕ × List Group)) where
    over : Pos → Bool
    over c = endBefore (rows o) c

    waiting : ℕ → Pos → Bool
    waiting i c = anyᵇ (λ { (q , _) → q <ᵖ c }) (nthL (suc i))

    drained : Pos → Bool
    drained c = allᵇ (λ { (_ , gs) → allᵇ (λ { (_ , _ , ls) → anyᵇ (λ { (_ , l) → endBefore (rows l) c }) ls }) gs }) lv

    laneRow : ℕ → Row B → Row B
    laneRow i (c , end) = if waiting i c then (c ++ [ ix 0 ] , skip) else (c , (if over c then end else skip))
    laneRow i r         = r

    concatRows : Listed B
    concatRows = (concatMap (outerRow drained) (rows o) ++ concatMap (λ { (i , l) → mapL (laneRow i) (rows l) }) (lanesOf lv))
               ⊣ (short o ∨ not (null (nthL (suc (count vals)))) ∨ anyᵇ (λ { (_ , l) → short l }) (lanesOf lv))

  listC : Maybe (Listed B)
  listC = bind (mapM (λ i → bind (levelL i) λ gs → just (i , gs)) (upto (suc (count vals)))) λ lv → just (concatRows lv)

-- `Table.Connect.ConnT`.
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

-- `Table.approxᵀ`'s clauses, approximant n, subscribed at `p`.
listT : ∀ {Γ A} → ℕ → Obs Timeline Γ A → All Listed Γ → Pos → Maybe (Listed A)
listT n       (cold c)          ρ p = just (walk fuel (start p (timelineAt c p)))
listT n       empty             ρ p = just ([ p ++ [ last ] , end ] ⊣ false)
listT n       (of xs)           ρ p = just (walk fuel (ofᴱ p 0 xs))
listT n       (map f s)         ρ p = bind (listT n s ρ p) λ l → just (mapRows f l)
listT n       (scan f z s)      ρ p = nothing
listT n       (takeWhile i q s) ρ p = nothing
listT n       (flatMap (mergeᶠ nothing) f s) ρ p =
  bind (listT n s ρ p) λ o →
  bind (mapM (λ qa → bind (listT n (f (proj₂ qa)) ρ (proj₁ qa ++ [ ix 1 ])) λ l → just (proj₁ qa , proj₂ qa , l)) (values (rows o))) λ ls →
  just (mergeRows o ls)
listT n       (flatMap (mergeᶠ (just (suc zero))) f s) ρ p =
  bind (listT n s ρ p) λ o → ConcatL.listC (λ a → listT n (f a) ρ) o
listT n       (flatMap op f s)  ρ p = nothing
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
-- table ends, cut if a budget cut it short, silent otherwise.
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

-- A generated program's table, as the oracle reads it, unfolded as the
-- denotation's trace is; `null` where the table leaves an operator out.
tableJSON : ∀ {t} → ℕ → Prog t → String
tableJSON {t} u p with listT (depth u p) (toObs timeline u p [] [] []) [] root
... | just l  = showTrace t (traceT l)
... | nothing = "null"
