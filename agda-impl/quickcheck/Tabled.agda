{-# OPTIONS --guardedness #-}

-- THE TABLE, LISTED: the rows `denotation.Table` gives a program, as a
-- list, up to a horizon — what the oracle checks the table against rxjs
-- by.  A development tool: no proof reads it.  Each clause mirrors one of
-- the table's; an operator the table leaves out lists nothing.
module quickcheck.Tabled where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; concatMap; foldr; filterᵇ) renaming (map to mapL)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Time; Timeline; timelineAt; _<ᵖ_; inside; ix; sub; last; root)
open import denotation.MonotonicList using (start; ofᴱ)
open import denotation.Table using (Ev; out; skip; end)
open import quickcheck.Oracle using (Event; val; _▸_; Trace; completed; silent; cut; depth; showTrace)
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (⟦_⟧ᵀ)
open import Data.String using (String)
import quickcheck.Oracle as O

------------------------------------------------------------------------
-- Listings

Row : Set → Set
Row A = Pos × Ev A

-- The rows, and whether a budget cut them short anywhere.
record Listed (A : Set) : Set where
  constructor _⊣_
  field
    rows  : List (Row A)
    short : Bool
open Listed

private
  bind : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  bind nothing  k = nothing
  bind (just x) k = k x

  cons : ∀ {A} → Row A → Listed A → Listed A
  cons x (rs ⊣ b) = (x ∷ rs) ⊣ b

  _≼ᵇ_ : Pos → Pos → Bool
  p ≼ᵇ q = not (q <ᵖ p)

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
  isEnd : ∀ {A} → Ev A → Bool
  isEnd end = true
  isEnd _   = false

  -- The table's end: the least end row's position.
  endOf : ∀ {A} → List (Row A) → Maybe Pos
  endOf []                  = nothing
  endOf ((q , e) ∷ rs) with isEnd e | endOf rs
  ... | false | m        = m
  ... | true  | nothing  = just q
  ... | true  | just c   = just (if q <ᵖ c then q else c)

  proper : ∀ {A} → List (Row A) → List (Row A)
  proper rs with endOf rs
  ... | nothing = rs
  ... | just c  = filterᵇ (λ { (q , _) → q ≼ᵇ c }) rs

  ended : Maybe Pos → Pos → Bool
  ended nothing  c = false
  ended (just c′) c = c′ ≼ᵇ c

  insert : ∀ {A} → Row A → List (Row A) → List (Row A)
  insert x []       = [ x ]
  insert (q , e) ((k , d) ∷ ys) = if q <ᵖ k then (q , e) ∷ (k , d) ∷ ys else (k , d) ∷ insert (q , e) ys

  sort : ∀ {A} → List (Row A) → List (Row A)
  sort = foldr insert []

  values : ∀ {A} → List (Row A) → List (Pos × A)
  values []                  = []
  values ((q , out a) ∷ rs)  = (q , a) ∷ values rs
  values (_ ∷ rs)            = values rs

  anyᵇ : ∀ {X : Set} → (X → Bool) → List X → Bool
  anyᵇ p = foldr (λ x b → p x ∨ b) false

  allᵇ : ∀ {X : Set} → (X → Bool) → List X → Bool
  allᵇ p = foldr (λ x b → p x ∧ b) true

------------------------------------------------------------------------
-- The operators

mapRows : ∀ {A B} → (A → B) → Listed A → Listed B
mapRows f (rs ⊣ b) = mapL one rs ⊣ b
  where
    one : _ → _
    one (q , out a) = q , out (f a)
    one (q , skip)  = q , skip
    one (q , end)   = q , end

-- `Table.Rejoin`, over a hot's proper rows.
rejoin : ∀ {A} → Pos → Listed A → Listed A
rejoin p (rs ⊣ b) = concatMap one rs ⊣ b
  where
    one : _ → _
    one (q , end) = if p <ᵖ q then [ q ++ [ sub p ] , end ] else [ p ++ [ last ] , end ]
    one (q , e)   = if p <ᵖ q then [ q ++ [ sub p ] , e ] else []

hotOf : ∀ {A} → Listed A → Listed A
hotOf (rs ⊣ b) = proper rs ⊣ b

-- `Table.Merge.MergeT`, each value's lane listed at its subscription.
mergeRows : ∀ {A B} → Listed A → List (Pos × Listed B) → Listed B
mergeRows {B = B} o ls = (concatMap outer (rows o) ++ concatMap lane ls) ⊣ (short o ∨ anyᵇ (λ { (_ , l) → short l }) ls)
  where
    done : Pos → Bool
    done c = ended (endOf (rows o)) c ∧ allᵇ (λ { (_ , l) → ended (endOf (rows l)) c }) ls

    closing : Pos → Row B
    closing c = c , (if done c then end else skip)

    outer : _ → List (Row B)
    outer (q , out _) = [ q ++ [ ix 0 ] , skip ]
    outer (q , skip)  = [ q , skip ]
    outer (c , end)   = [ closing c ]

    lane : Pos × Listed B → List (Row B)
    lane (_ , l) = mapL one (rows l)
      where
        one : Row B → Row B
        one (c , end) = closing c
        one r         = r

-- `Table.Concat`: lane i+1 subscribed where its value arrives, or where
-- lane i ends if that is later.  Each lane comes with the next value's
-- position, if any.
module _ {A B : Set} (lane : A → Pos → Maybe (Listed B)) where
  lanesC : Maybe Pos → List (Pos × A) → Maybe (List (Listed B × Maybe Pos))
  lanesC prev []                   = just []
  lanesC prev ((q , a) ∷ vs) =
    bind (lane a (at prev)) λ l →
    bind (more (endOf (rows l)) vs) λ ls →
    just ((l , nextOf vs) ∷ ls)
    where
      at : Maybe Pos → Pos
      at nothing  = q ++ [ ix 1 ]
      at (just c) = if c <ᵖ q then q ++ [ ix 1 ] else c ++ [ ix 1 ]

      nextOf : List (Pos × A) → Maybe Pos
      nextOf []            = nothing
      nextOf ((q′ , _) ∷ _) = just q′

      -- a lane that never ends holds back every later one
      more : Maybe Pos → List (Pos × A) → Maybe (List (Listed B × Maybe Pos))
      more nothing  _  = just []
      more (just c) vs = lanesC (just c) vs

concatRows : ∀ {A B} → Listed A → List (Listed B × Maybe Pos) → ℕ → Listed B
concatRows {B = B} o ls nvals =
  (concatMap outer (rows o) ++ concatMap lane ls) ⊣ (short o ∨ anyᵇ (λ { (l , _) → short l }) ls)
  where
    over : Pos → Bool
    over c with endOf (rows o)
    ... | nothing = false
    ... | just c₀ = c₀ <ᵖ c

    count : ∀ {X : Set} → List X → ℕ
    count = foldr (λ _ → suc) 0

    drained : Pos → Bool
    drained c = (count ls ≡ᵇ nvals) ∧ allᵇ (λ { (l , _) → lt (endOf (rows l)) }) ls
      where
        lt : Maybe Pos → Bool
        lt nothing   = false
        lt (just c′) = c′ <ᵖ c

    outer : _ → List (Row B)
    outer (q , out _) = [ q ++ [ ix 0 ] , skip ]
    outer (q , skip)  = [ q , skip ]
    outer (c , end)   = [ c , (if drained c then end else skip) ]

    lane : Listed B × Maybe Pos → List (Row B)
    lane (l , nx) = mapL one (rows l)
      where
        before : Maybe Pos → Pos → Bool
        before nothing  c = false
        before (just q) c = q <ᵖ c

        waiting : Pos → Bool
        waiting = before nx

        one : Row B → Row B
        one (c , end) = if waiting c then (c ++ [ ix 0 ] , skip) else (c , (if over c then end else skip))
        one r         = r

-- `Table.Connect.ConnT`.
connRows : ∀ {A B} → Pos → Listed A → Listed B → Listed B
connRows {A} {B} r σ β = (rows β ++ concatMap shown (rows σ)) ⊣ (short σ ∨ short β)
  where
    alive : Pos → Bool
    alive q with endOf (rows β)
    ... | nothing = true
    ... | just c  = q <ᵖ c

    shown : Row A → List (Row B)
    shown (k , _) =
      if alive (k ++ [ ix 0 ]) then [ k ++ [ ix 0 ] , skip ]
      else if inside r k then [ k , skip ] else []

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
  bind (each (values (rows o))) λ ls →
  just (mergeRows o ls)
  where
    each : List (Pos × _) → Maybe (List (Pos × Listed _))
    each []             = just []
    each ((q , a) ∷ vs) = bind (listT n (f a) ρ (q ++ [ ix 1 ])) λ l → bind (each vs) λ ls → just ((q , l) ∷ ls)
listT n       (flatMap (mergeᶠ (just (suc zero))) f s) ρ p =
  bind (listT n s ρ p) λ o →
  bind (lanesC (λ a → listT n (f a) ρ) nothing (values (sort (rows o)))) λ ls →
  just (concatRows o ls (len (values (rows o))))
  where
    len : ∀ {X : Set} → List X → ℕ
    len = foldr (λ _ → suc) 0
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
    finish with endOf rs
    ... | just _  = completed
    ... | nothing = if b then cut else silent

-- A generated program's table, as the oracle reads it, unfolded as the
-- denotation's trace is; `null` where the table leaves an operator out.
tableJSON : ∀ {t} → ℕ → Prog t → String
tableJSON {t} u p with listT (depth u p) (toObs timeline u p [] [] []) [] root
... | just l  = showTrace t (traceT l)
... | nothing = "null"
