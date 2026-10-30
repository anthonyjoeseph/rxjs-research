{-# OPTIONS --guardedness #-}

-- THE ROWS OF A STATE: what the engine's state still owes, read off as
-- emission-set rows.
-- Every configuration owes the rows its tree still owes the root (`RT`),
-- read node by node off the state: a pending subscription its meaning
-- entered where it will be made, an of its values left, a merge the
-- union of what its outer and its lanes owe, a connect its body's rows
-- under an environment binding its source.  A step either keeps the
-- visible rows or shows the least of them and drops it.
module adequacy.Rows where

open import Data.Bool using (Bool; T; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.List using (List; []; _∷_; [_]; _ʳ++_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ofᴱ; Events; burst; hush) renaming (end to endᴱ)
open import denotation.Events using (Pos; Timeline; ix; last; inside)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; _≺_; _≼_; InE; enter; Truncate; MapT; ⟦_⟧; Ended; module Joining; module Values; module Scan; module TakeWhile; Den; hot; Proper; DenEnv; module Connecting)
open import operation.PureObservable using (module Machine; module Driver; Tape; play; ending; over)
open Machine using (St; Ctx; CS; Owe; free; cpAt; cutAt; overAt; takeS; connS; joinS; coldS; scanS; Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; load; moved; quiet; pend; ofS; mapS; cutS; lnS; flatS; alive; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; nx; cp) renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)

------------------------------------------------------------------------
-- Rows

∅ : ∀ {A} → EmissionSet A
∅ q e = ⊥

toEv : ∀ {A} → Evᴹ A → Ev A
toEv (nx a) = out a
toEv cp     = end

-- A row the root is told of: a value or the end.
Visible : ∀ {A} → Ev A → Set
Visible (out _) = ⊤
Visible skip    = ⊥
Visible (pin _) = ⊥
Visible end     = ⊤

Vis : ∀ {A} → EmissionSet A → EmissionSet A
Vis t q e = t q e × Visible e

Past : ∀ {A} → Pos → EmissionSet A → EmissionSet A
Past p t q e = t q e × p ≺ q

-- One more row.
data Plus {A : Set} (t : EmissionSet A) (p : Pos) (v : Ev A) : EmissionSet A where
  old : ∀ {q e} → t q e → Plus t p v q e
  new : Plus t p v p v

record _≃_ {A : Set} (t u : EmissionSet A) : Set where
  constructor _⇄_
  field
    to   : ∀ {q e} → t q e → u q e
    from : ∀ {q e} → u q e → t q e
open _≃_

-- Rows of any lane of a list.
Lanes : ∀ {B} → List (EmissionSet B) → EmissionSet B
Lanes []       k e = ⊥
Lanes (t ∷ Ls) k e = t k e ⊎ Lanes Ls k e

-- A fact of every lane of a list.
Each : ∀ {B} → (EmissionSet B → Set) → List (EmissionSet B) → Set
Each P []       = ⊤
Each P (t ∷ Ls) = P t × Each P Ls

-- Lanes given by their ends: the k-th of their ends in position order,
-- from 0, is where `P` holds, for `P` closed downward.
Kth : (Pos → Set) → List (Pos → Set) → ℕ → Set
Kth P []       k       = ⊥
Kth P (l ∷ ls) zero    = (Σ Pos λ c → l c × P c) ⊎ Kth P ls zero
Kth P (l ∷ ls) (suc k) = ((Σ Pos λ c → l c × P c) × Kth P ls k) ⊎ Kth P ls (suc k)

-- Every one of `k` running lanes among `ls` has ended where `P` holds:
-- read off a joiner's count, not its lanes, since a lane that never ends
-- owes nothing and would read over.
AllEnd : (Pos → Set) → ℕ → List (Pos → Set) → Set
AllEnd P zero    ls = ⊤
AllEnd P (suc k) ls = Kth P ls k

-- Each lane by its ends.
EndsOf : ∀ {B} → List (EmissionSet B) → List (Pos → Set)
EndsOf []       = []
EndsOf (t ∷ Ls) = (λ c → t c end) ∷ EndsOf Ls

-- A lane begun at a value at `q`, past where it subscribed.
-- `At L`, as a record: Agda reads `L` back off it, which it cannot off
-- `At`'s product.
record Lane {A B : Set} (L : A → Pos → EmissionSet B) (q : Pos) (a : A) (k : Pos) (e : Ev B) : Set where
  constructor reads
  field
    lane : L a (q ++ [ ix 1 ]) k e
    past : (q ++ [ ix 1 ]) ≺ k

-- A MERGE PART WAY THROUGH: `Merge`'s joiner at what is left of its outer,
-- `O`, done already where `d`, with the lanes it has begun, `Ls`, `n` of
-- them still running, over once each running one has ended (`AllEnd`).
--
-- What it owes is the joiner's rows with finitely many before, as entered
-- (`RowT`): a lane that never stops leaves every row past it unreached.
--
-- `Over` is a record so that Agda reads `n` back off it, which it cannot
-- off `AllEnd`.
module Flat {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) where
  record Over (c : Pos) : Set where
    constructor over-at
    field
      o-over : T d ⊎ Ended O c
      l-over : AllEnd (_≼ c) n (EndsOf Ls)

  open Joining (Lane L) O (Lanes Ls) Over (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) public

  RowT : EmissionSet B
  RowT = Truncate JoinT

-- A lane begun at `s`, past its subscription.
record From {A B : Set} (L : A → Pos → EmissionSet B) (a : A) (s k : Pos) (e : Ev B) : Set where
  constructor sub
  field
    rd   : L a s k e
    past : s ≺ k

-- A SWITCH PART WAY THROUGH, its `n` begun lanes `Ls`: every outer value
-- cuts what runs.
module SwitchF {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) where

  -- An outer value arrived before `k`.
  Kill : Pos → Set
  Kill k = Σ Pos λ q′ → Σ A λ a′ → O q′ (out a′) × q′ ≺ k

  -- A value after `q` arrived before `k`.
  Cut : Pos → Pos → Set
  Cut q k = Σ Pos λ q′ → Σ A λ a′ → O q′ (out a′) × q ≺ q′ × q′ ≺ k

  -- The begun lanes until the first value; their pins whose connect they
  -- had subscribed by it.
  data Bg : EmissionSet B where
    bg   : ∀ {k e} → Lanes Ls k e → ¬ Kill k → Bg k e
    bpin : ∀ {k r} → Lanes Ls k (pin r) → ¬ Kill r → T (inside r k) → Bg k (pin r)

  Over : Pos → Set
  Over c = (T d ⊎ Ended O c) × (AllEnd (_≼ c) n (EndsOf Ls) ⊎ Kill c)

  open Joining (Lane L) O Bg Over (λ _ → ⊤) Cut (λ _ → ⊥) public

  RowT : EmissionSet B
  RowT = Truncate JoinT

-- AN EXHAUST PART WAY THROUGH, its `n` begun lanes `Ls`: a value runs only
-- if every lane run before it, begun or its own, has ended.
module ExhaustF {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Ls : List (EmissionSet B)) where
  open Values O using (Next)

  -- The begun lanes have ended before `q`.
  Free : Pos → Set
  Free q = AllEnd (_≺ q) n (EndsOf Ls)

  -- At the value at `q′`, the last lane run is the value at `q`'s
  -- (`just q`), or a begun one (`nothing`).
  data Cur : Pos → Maybe Pos → Set where
    cur₀  : ∀ {q a} → O q (out a) → (∀ {k b} → O k (out b) → q ≼ k) → Free q → Cur q (just q)
    bg₀   : ∀ {q a} → O q (out a) → (∀ {k b} → O k (out b) → q ≼ k) → ¬ Free q → Cur q nothing
    run   : ∀ {q₁ q a c q₂ a₂} → Cur q₁ (just q) → O q (out a) → Lane L q a c end → c ≺ q₂
          → O q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ (just q₂)
    drop  : ∀ {q₁ q a q₂ a₂} → Cur q₁ (just q) → O q (out a) → (∀ {c} → Lane L q a c end → q₂ ≼ c)
          → O q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ (just q)
    brun  : ∀ {q₁ q₂ a₂} → Cur q₁ nothing → Free q₂ → O q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ (just q₂)
    bdrop : ∀ {q₁ q₂ a₂} → Cur q₁ nothing → ¬ Free q₂ → O q₂ (out a₂) → q₁ ≺ q₂ → Next q₁ q₂ → Cur q₂ nothing

  -- The value at `q` runs its lane.
  Run : Pos → Set
  Run q = Cur q (just q)

  Over : Pos → Set
  Over c = (T d ⊎ Ended O c) × AllEnd (_≼ c) n (EndsOf Ls)

  open Joining (Lane L) O (Lanes Ls) Over Run (λ _ _ → ⊥) (λ _ → ⊥) public

  RowT : EmissionSet B
  RowT = Truncate JoinT

-- The i-th of a list.
data Nthᴸ {A : Set} : List A → ℕ → A → Set where
  hd : ∀ {a as} → Nthᴸ (a ∷ as) 0 a
  tl : ∀ {a b as i} → Nthᴸ as i a → Nthᴸ (b ∷ as) (suc i) a

-- A MERGE BOUNDED BY m PART WAY THROUGH, its `n` begun lanes `Ls` and the
-- values `Qu` queued: `Bounded`'s schedule, its lanes counted from the
-- begun ones, the queued values first.  A queued value has no position:
-- it starts where a lane's end frees it.
module BoundedF {A B : Set} (m : ℕ) (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (n : ℕ) (Qu : List A) (Ls : List (EmissionSet B)) where
  open Values O using (Nth)

  -- The i-th value to run: queued, or the outer's, arrived at `q`.
  data Item : ℕ → Maybe Pos → A → Set where
    queued : ∀ {i a} → Nthᴸ Qu i a → Item i nothing a
    outer  : ∀ {i q a} → Nth i q a → Item (length Qu + i) (just q) a

  -- Arrived before `c`: a queued value always.
  Arr : Maybe Pos → Pos → Set
  Arr nothing  c = ⊤
  Arr (just q) c = q ≺ c

  -- Where the i-th starts, given the lanes `ls` before it, the begun ones
  -- among them: at once, or at the end that frees it.
  data Starts (i : ℕ) (ls : List (Pos → Set)) : Maybe Pos → Pos → Set where
    room   : ∀ {q} → n + i < m → Starts i ls (just q) (q ++ [ ix 1 ])
    freed  : ∀ {q} → m ≤ n + i → Kth (_≺ q) ls (n + i ∸ m) → Starts i ls (just q) (q ++ [ ix 1 ])
    queued : ∀ {w c} → m ≤ n + i → Arr w c → Kth (_≡ c) ls 0 → Kth (_≼ c) ls (n + i ∸ m)
           → ¬ Kth (_≺ c) ls (n + i ∸ m) → Starts i ls w (c ++ [ ix 1 ])

  -- The i-th's ends, given the lanes before it.
  Ends : ℕ → List (Pos → Set) → Pos → Set
  Ends i ls c = Σ (Maybe Pos) λ w → Σ A λ a → Σ Pos λ s → Item i w a × Starts i ls w s × From L a s c end

  -- The lanes before the i-th, the latest first, the begun ones last.
  Sched : ℕ → List (Pos → Set)
  Sched zero    = EndsOf Ls
  Sched (suc i) = Ends i (Sched i) ∷ Sched i

  Sub : ℕ → Maybe Pos → Pos → A → Set
  Sub i w s a = Item i w a × Starts i (Sched i) w s

  -- A queued lane starts past `c`.
  Queued : Pos → Set
  Queued c = Σ ℕ λ i → Σ (Maybe Pos) λ w → Σ A λ a → Sub i w (c ++ [ ix 1 ]) a

  -- The outer's value at `q`'s lane.
  LaneB : Pos → A → EmissionSet B
  LaneB q a k e = Σ ℕ λ i → Σ Pos λ s → Sub i (just q) s a × From L a s k e

  -- The begun lanes, and each queued value's.
  data Bg : EmissionSet B where
    begun : ∀ {k e} → Lanes Ls k e → Bg k e
    waits : ∀ {i a s k e} → Sub i nothing s a → From L a s k e → Bg k e

  Indexed : Pos → Set
  Indexed q = Σ ℕ λ i → Σ A λ a → Item i (just q) a

  Over : Pos → Set
  Over c = (T d ⊎ Ended O c) × AllEnd (_≼ c) (n + length Qu) (Sched (length Qu))

  open Joining LaneB O Bg Over Indexed (λ _ _ → ⊥) Queued public

  RowT : EmissionSet B
  RowT = Truncate JoinT

-- What a subscription pending at `p` owes: its meaning under `ρ`,
-- entered there.
pendRows : ∀ {Γ A} → DenEnv Γ → Obs Timeline Γ A → Pos → EmissionSet A
pendRows ρ o p = enter (⟦ o ⟧ ρ) p

-- A source's end once it has shown it, kept for joiners still to come.
data Closed {A : Set} (k : CS) : EmissionSet A where
  shut : T (CS.closed k) → Closed k (CS.endAt k) end

-- A BINDER'S MEANING: what its source still owes, and its end once
-- closed, up to that end, made hot.  A joiner rejoins what is past where
-- it joined, or the end at once.
Hot : ∀ {A} → EmissionSet A → CS → Den A
Hot t k = hot (Proper (λ q e → t q e ⊎ Closed k q e))

-- What a joiner has been fed and not shown.
data Inbox {A : Set} : List (Pos × Evᴹ A) → EmissionSet A where
  this : ∀ {q e ib} → Inbox ((q , e) ∷ ib) q (toEv e)
  that : ∀ {x ib q e} → Inbox ib q e → Inbox (x ∷ ib) q e

-- A started cold's events: the frame it plays from its next index, its
-- completion owed, or nothing more.
tapeE : ∀ {A} → Tape A → Events A
tapeE (play τ u i t fr) = burst τ u i fr
tapeE (ending e)        = endᴱ e
tapeE over              = hush

-- Rows of either.
_∪_ : ∀ {A} → EmissionSet A → EmissionSet A → EmissionSet A
(t ∪ u) q e = t q e ⊎ u q e

-- A scan's fold at a position stands on a value of its source there.
acc-val : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {q b} → Scan.Acc f z t q b → Σ A λ a → t q (out a)
acc-val (Scan.acc₀ r _)    = _ , r
acc-val (Scan.acc _ r _ _) = _ , r

-- A take past its failing value at `p`: the source's pins whose connect
-- subscribed no later, and its end while still owed.
data Kept {A : Set} (p : Pos) (t : EmissionSet A) : EmissionSet A where
  kept : ∀ {k r} → t k (pin r) → ¬ (p ≺ r) → T (inside r k) → Kept p t k (pin r)

data Stops {A : Set} (p : Pos) (t : EmissionSet A) : EmissionSet A where
  stop : Stops p t (p ++ [ last ]) end
  left : ∀ {k e} → Kept p t k e → Stops p t k e

-- A take's rows, by what it owes: its source's taken, entered as a
-- subscription's; once its failing value is shown, its end and pins left.
TakeR : ∀ {A} → Bool → (A → Bool) → Owe → EmissionSet A → EmissionSet A
TakeR i q free       t = Truncate (TakeWhile.TakeT i q t)
TakeR i q (cpAt p)   t = Stops p t
TakeR i q (cutAt p)  t = Kept p t
TakeR i q (overAt p) t = Kept p t

-- What a node still owes its parent, under `ρ`, the meaning of every
-- binder in scope.
mutual
  rows : ∀ {Γ A} → DenEnv Γ → St Γ A → EmissionSet A
  rows ρ (pend o p)                             = pendRows ρ o p
  rows ρ (ofS i p xs)                           = InE (ofᴱ p i xs)
  rows ρ (coldS true l)                         = InE (tapeE l)
  rows ρ (mapS f s)                             = MapT f (rows ρ s)
  rows ρ (scanS f z s)                          = Scan.ScanT f z (rows ρ s)
  rows ρ (takeS i q w s)                        = TakeR i q w (rows ρ s)
  rows ρ (cutS true a s)                        = rows ρ s
  rows ρ (lnS true s)                           = rows ρ s
  rows ρ (flatS (mergeᶠ nothing) f d n q o ls)  = Flat.RowT (λ a → pendRows ρ (f a)) (rows ρ o) d n (rowsL ρ ls)
  rows ρ (flatS (mergeᶠ (just m)) f d n q o ls) = BoundedF.RowT m (λ a → pendRows ρ (f a)) (rows ρ o) d n q (rowsL ρ ls)
  rows ρ (flatS switchᶠ f d n q o ls)           = SwitchF.RowT (λ a → pendRows ρ (f a)) (rows ρ o) d n (rowsL ρ ls)
  rows ρ (flatS exhaustᶠ f d n q o ls)          = ExhaustF.RowT (λ a → pendRows ρ (f a)) (rows ρ o) d n (rowsL ρ ls)
  rows ρ (connS k o b)                          = Connecting.ConnT (CS.connAt k) (rows ρ o) (rows (Hot (rows ρ o) k ∷ ρ) b)
  rows ρ (joinS j true x ib)                    = Inbox ib ∪ enter (lookup ρ x) j
  rows ρ (joinS j false x ib)                   = Inbox ib
  rows ρ _                                      = ∅

  rowsL : ∀ {Γ A} → DenEnv Γ → List (St Γ A) → List (EmissionSet A)
  rowsL ρ []       = []
  rowsL ρ (s ∷ ls) = rows ρ s ∷ rowsL ρ ls

-- The meaning of every binder in scope at the hole.
env : ∀ {R Γ A} → Ctx R Γ A → DenEnv Γ
env top                                  = []
env (inMap f c)                          = env c
env (inScan f z c)                       = env c
env (inCut l a c)                        = env c
env (inLn b c)                           = env c
env (inTake i p w c)                     = env c
env (inOuter op f d n q ls c)            = env c
env (inLanes op f d n q o pre post c)    = env c
env (inSrc k b c)                        = env c
env (inBody k o c)                       = Hot (rows (env c) o) k ∷ env c

-- What the root still owes, given what the hole owes.
up : ∀ {R Γ A} → Ctx R Γ A → EmissionSet A → EmissionSet R
up top                                                H = H
up (inMap f c)                                        H = up c (MapT f H)
up (inScan f z c)                                     H = up c (Scan.ScanT f z H)
up (inCut true a c)                                   H = up c H
up (inCut false a c)                                  H = up c ∅
up (inLn true c)                                      H = up c H
up (inLn false c)                                     H = up c ∅
up (inTake i q w c)                                   H = up c (TakeR i q w H)
up (inOuter (mergeᶠ nothing) f d n q ls c)            H = up c (Flat.RowT (λ a → pendRows (env c) (f a)) H d n (rowsL (env c) ls))
up (inOuter (mergeᶠ (just m)) f d n q ls c)           H = up c (BoundedF.RowT m (λ a → pendRows (env c) (f a)) H d n q (rowsL (env c) ls))
up (inOuter switchᶠ f d n q ls c)                     H = up c (SwitchF.RowT (λ a → pendRows (env c) (f a)) H d n (rowsL (env c) ls))
up (inOuter exhaustᶠ f d n q ls c)                    H = up c (ExhaustF.RowT (λ a → pendRows (env c) (f a)) H d n (rowsL (env c) ls))
up (inLanes (mergeᶠ nothing) f d n q o pre post c)    H = up c (Flat.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
up (inLanes (mergeᶠ (just m)) f d n q o pre post c)   H = up c (BoundedF.RowT m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n q (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
up (inLanes switchᶠ f d n q o pre post c)             H = up c (SwitchF.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
up (inLanes exhaustᶠ f d n q o pre post c)            H = up c (ExhaustF.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d n (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
up (inSrc k b c)                                      H = up c (Connecting.ConnT (CS.connAt k) H (rows (Hot H k ∷ env c) b))
up (inBody k o c)                                     H = up c (Connecting.ConnT (CS.connAt k) (rows (env c) o) H)

-- A rising event is owed only out of a live node: a lane out of its
-- list absorbs it.
Risen : ∀ {Γ A} → DenEnv Γ → St Γ A → Pos → Ev A → EmissionSet A
Risen ρ s p v = if alive s then Plus (rows ρ s) p v else rows ρ s

-- What the focus owes: a rising event its row too.
here : ∀ {Γ A} → DenEnv Γ → St Γ A → Mode A → Pos → EmissionSet A
here ρ s (rising e) p = Risen ρ s p (toEv e)
here ρ s _          p = rows ρ s

RT : ∀ {R} → Conf R → EmissionSet R
RT ⟨ c , s , m , p ⟩ = up c (here (env c) s m p)

------------------------------------------------------------------------
-- Runs

-- The pure semantics run from `k`, showing `rs`: the driver's steps, so
-- a cold begun and a cold's turn are steps too.
data Steps {R : Set} : Conf R → Shownᴹ R → Set₁ where
  []   : ∀ {k} → Steps k []
  tau  : ∀ {k k′ t rs} → Driver.step R k ≡ Driver.silent t k′ → Steps k′ rs → Steps k rs
  val  : ∀ {k k′ t p a rs} → Driver.step R k ≡ Driver.value t p a k′ → Steps k′ rs → Steps k ((p , nx a) ∷ rs)
  fin  : ∀ {k p} → Driver.step R k ≡ Driver.complete p → Steps k [ (p , cp) ]

conv : ∀ {R} → Shownᴹ R → List (Pos × Ev R)
conv []             = []
conv ((p , e) ∷ rs) = (p , toEv e) ∷ conv rs

-- A reader shown `rs` of `t`: each the least visible row left.
data Shows* {A : Set} (t : EmissionSet A) : List (Pos × Ev A) → Set₁ where
  []  : Shows* t []
  _∷_ : ∀ {p e rs} → Vis t p e × (∀ {q e′} → Vis t q e′ → p ≼ q) → Shows* (Past p t) rs → Shows* t ((p , e) ∷ rs)

-- One step: the visible rows kept, or the least shown and dropped.
data Moves {R : Set} (T : EmissionSet R) : Shownᴹ R → EmissionSet R → Set₁ where
  silent : ∀ {T′} → Vis T ≃ Vis T′ → Moves T [] T′
  shown  : ∀ {T′ p e} → Vis T p (toEv e) → (∀ {q e′} → Vis T q e′ → p ≼ q) → Vis (Past p T) ≃ Vis T′ → Moves T [ (p , e) ] T′

≃-sym : ∀ {A} {t u : EmissionSet A} → t ≃ u → u ≃ t
≃-sym eq = from eq ⇄ to eq

Shows*-≃ : ∀ {A} {t u : EmissionSet A} {rs} → Vis t ≃ Vis u → Shows* t rs → Shows* u rs
Shows*-≃ eq [] = []
Shows*-≃ eq ((v , lt) ∷ rest) =
  (to eq v , λ w → lt (from eq w))
  ∷ Shows*-≃ ((λ { ((x , pq) , vi) → let (y , vj) = to eq (x , vi) in (y , pq) , vj })
            ⇄ (λ { ((x , pq) , vi) → let (y , vj) = from eq (x , vi) in (y , pq) , vj })) rest
