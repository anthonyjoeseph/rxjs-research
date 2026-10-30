{-# OPTIONS --guardedness #-}

-- THE ROWS OF A STATE: what the engine's state still owes, read off as
-- emission-set rows.
-- Every configuration owes the rows its tree still owes the root (`RT`),
-- read node by node off the state: an of its values left, a merge the
-- union of what its outer and its lanes owe, a connect its body's rows
-- under an environment binding its source.  A step either keeps the
-- visible rows or shows the least of them and drops it.
module adequacy.Rows where

open import Data.Bool using (Bool; T; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _ʳ++_; _++_)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ofᴱ)
open import denotation.Events using (Pos; Timeline; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; pin; end; _≺_; _≼_; InE; enter; Truncate; MapT; ⟦_⟧; Ended; module Joining; Den; hot; Proper; DenEnv; module Connecting)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (St; Ctx; CS; connS; joinS; Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising; load; moved; quiet; pend; ofS; mapS; cutS; lnS; flatS; alive; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; nx; cp) renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)

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

-- A lane or an outer ended by `c`: every row it still owes, by `c`.
-- Exact only where every lane ends, as in the fragment: a lane that
-- never ends owes nothing and reads gone.
--
-- DEAD ROUTE: a lane finished as `Ended` in its rows, or as its node's
--   live-lane count: while a lane's end rises to its merge, the lane is
--   still in the list, owes nothing and holds no end, so the merge's bare
--   rows skip an end the denotation has.  Rows cannot tell an end in
--   flight from a lane that never ends; the hole's state can, and `up`
--   does not see it.
Gone : ∀ {X} → EmissionSet X → Pos → Set
Gone t c = ∀ {k e} → t k e → k ≼ c

-- Rows of any lane of a list.
Lanes : ∀ {B} → List (EmissionSet B) → EmissionSet B
Lanes []       k e = ⊥
Lanes (t ∷ Ls) k e = t k e ⊎ Lanes Ls k e

-- A fact of every lane of a list.
Each : ∀ {B} → (EmissionSet B → Set) → List (EmissionSet B) → Set
Each P []       = ⊤
Each P (t ∷ Ls) = P t × Each P Ls

-- A MERGE PART WAY THROUGH: `Merge`'s joiner at what is left of its outer,
-- `O`, done already where `d`, with the lanes it has begun, `Ls`.
-- `At L`, as a record: Agda reads `L` back off it, which it cannot off
-- `At`'s product.
record Lane {A B : Set} (L : A → Pos → EmissionSet B) (q : Pos) (a : A) (k : Pos) (e : Ev B) : Set where
  constructor reads
  field
    lane : L a (q ++ [ ix 1 ]) k e
    past : (q ++ [ ix 1 ]) ≺ k

--
-- What it owes is the joiner's rows with finitely many before, as entered
-- (`RowT`): a lane that never stops leaves every row past it unreached.
module Flat {A B : Set} (L : A → Pos → EmissionSet B) (O : EmissionSet A) (d : Bool) (Ls : List (EmissionSet B)) where
  open Joining (Lane L) O (Lanes Ls) (λ c → (T d ⊎ Ended O c) × Each (λ t → Gone t c) Ls) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) public

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

-- Rows of either.
_∪_ : ∀ {A} → EmissionSet A → EmissionSet A → EmissionSet A
(t ∪ u) q e = t q e ⊎ u q e

-- What a node still owes its parent, under `ρ`, the meaning of every
-- binder in scope.
mutual
  rows : ∀ {Γ A} → DenEnv Γ → St Γ A → EmissionSet A
  rows ρ (ofS i p xs)                           = InE (ofᴱ p i xs)
  rows ρ (mapS f s)                             = MapT f (rows ρ s)
  rows ρ (cutS true a s)                        = rows ρ s
  rows ρ (lnS true s)                           = rows ρ s
  rows ρ (flatS (mergeᶠ nothing) f d n q o ls)  = Flat.RowT (λ a → pendRows ρ (f a)) (rows ρ o) d (rowsL ρ ls)
  rows ρ (connS k o b)                          = Connecting.ConnT (CS.srcAt k) (src ρ k o) (rows (Hot (src ρ k o) k ∷ ρ) b)
  rows ρ (joinS j true x ib)                    = Inbox ib ∪ enter (lookup ρ x) j
  rows ρ (joinS j false x ib)                   = Inbox ib
  rows ρ _                                      = ∅

  rowsL : ∀ {Γ A} → DenEnv Γ → List (St Γ A) → List (EmissionSet A)
  rowsL ρ []       = []
  rowsL ρ (s ∷ ls) = rows ρ s ∷ rowsL ρ ls

  -- A connect's source: subscribed at its own position once pending.
  src : ∀ {Γ X} → DenEnv Γ → CS → St Γ X → EmissionSet X
  src ρ k (pend o) = pendRows ρ o (CS.srcAt k)
  src ρ k o        = rows ρ o

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
env (inBody k o c)                       = Hot (src (env c) k o) k ∷ env c

-- What the root still owes, given what the hole owes.
up : ∀ {R Γ A} → Ctx R Γ A → EmissionSet A → EmissionSet R
up top                                                H = H
up (inMap f c)                                        H = up c (MapT f H)
up (inScan f z c)                                     H = up c ∅
up (inCut true a c)                                   H = up c H
up (inCut false a c)                                  H = up c ∅
up (inLn true c)                                      H = up c H
up (inLn false c)                                     H = up c ∅
up (inTake i p w c)                                   H = up c ∅
up (inOuter (mergeᶠ nothing) f d n q ls c)            H = up c (Flat.RowT (λ a → pendRows (env c) (f a)) H d (rowsL (env c) ls))
up (inOuter (mergeᶠ (just _)) f d n q ls c)           H = up c ∅
up (inOuter switchᶠ f d n q ls c)                     H = up c ∅
up (inOuter exhaustᶠ f d n q ls c)                    H = up c ∅
up (inLanes (mergeᶠ nothing) f d n q o pre post c)    H = up c (Flat.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
up (inLanes (mergeᶠ (just _)) f d n q o pre post c)   H = up c ∅
up (inLanes switchᶠ f d n q o pre post c)             H = up c ∅
up (inLanes exhaustᶠ f d n q o pre post c)            H = up c ∅
up (inSrc k b c)                                      H = up c (Connecting.ConnT (CS.srcAt k) H (rows (Hot H k ∷ env c) b))
up (inBody k o c)                                     H = up c (Connecting.ConnT (CS.srcAt k) (src (env c) k o) H)

-- A rising event is owed only out of a live node: a lane out of its
-- list absorbs it.
Risen : ∀ {Γ A} → DenEnv Γ → St Γ A → Pos → Ev A → EmissionSet A
Risen ρ s p v = if alive s then Plus (rows ρ s) p v else rows ρ s

-- What the focus owes: a pending subscription its meaning, a rising
-- event its row.
here : ∀ {Γ A} → DenEnv Γ → St Γ A → Mode A → Pos → EmissionSet A
here ρ s        (rising e)  p = Risen ρ s p (toEv e)
here ρ s        absorbed    p = rows ρ s
here ρ (pend o) subscribing p = pendRows ρ o p
here ρ s        subscribing p = rows ρ s

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
