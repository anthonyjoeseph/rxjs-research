{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import operation.Key using (Key; at; after; _<ᴷ_)

-- THE ENGINE, shared by both runtimes.  A typed zipper over the
-- program's state tree, every continuation kept on the node that owns
-- it, as a MARK keyed by when it runs (`operation.Key`).  Once what runs
-- now is absorbed, the least-keyed mark in the tree runs next.
--
-- Positions are execution order (`denotation.Events`), so
-- the order is read off the tree, and nothing in the state names
-- anything else in it: no job stack, no joiner paths, no feed stack, no
-- timers, no depths.
--
-- A connect's feed is pushed into each joiner's own inbox when its source
-- rises; each joiner then runs its inbox at its own positions.  A cold
-- leaf's runtime state says when it is next due (`due`), so a runtime's
-- frames and timers are marks too, and what it shows then (`peek`: a
-- value, its end, or nothing).
--
-- ONE EVENT PER SEARCH.  No event is shown except by a mark keyed where
-- it sits: a subscribe shows nothing, and an end it owes (empty's, a
-- joiner's whose subject is over) is an of with nothing left, owed at
-- its `last`.  The least mark runs first: each candidate is keyed by
-- where its event sits as its parent sees it.
module operation.AbstractObservable (C L : Set → Set₁) (due : ∀ {A} → L A → Maybe Key) (peek : ∀ {A} → L A → Maybe (Maybe A)) where

open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; length; null; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; ix; last; root; _<ᵖ_) renaming (sub to subᴾ)

-- Two connects in scope, the same one or not.
same? : ∀ {Γ : List Set} {A B : Set} → A ∈ Γ → B ∈ Γ → Maybe (A ≡ B)
same? (here refl) (here refl) = just refl
same? (there i)   (there j)   = same? i j
same? _           _           = nothing

data Ev (A : Set) : Set where
  nx : A → Ev A
  cp : Ev A

mapEv : ∀ {A B} → (A → B) → Ev A → Ev B
mapEv f (nx a) = nx (f a)
mapEv f cp     = cp

_⊕_ : Pos → Pos → Pos
p ⊕ q = p ++ q

------------------------------------------------------------------------
-- States

-- A kill switch's attach: done, or owed to the subscription made at `p`.
data Att : Set where
  attached : Att
  attAt    : Pos → Att

-- A takeWhile running, its completion owed after the failing value at
-- `p`, its source's cut owed, or over, its source cut.
data Owe : Set where
  free   : Owe
  cpAt   : Pos → Owe
  cutAt  : Pos → Owe
  overAt : Pos → Owe

-- The binders in scope, each as its connect was given: its source, with
-- the binders in scope there, and where the connect was subscribed.
data Scope : List Set → Set₁ where
  unbound : Scope []
  binds   : ∀ {Γ X} → Obs C Γ X → Pos → Scope Γ → Scope (X ∷ Γ)

-- A connect's subject and its source's switch, and what it owes: the
-- source's subscription (the body subscribed at `p`), the source's
-- attach (subscribed at `p`), the source's teardown (the body completed
-- at `p`); where the connect is subscribed, and where its source ended,
-- once closed; and the source as it was given, with the binders in scope
-- where it was given, which the run never reads (the binder's frozen
-- entry, for a reader of the rows).
record CS (Γ : List Set) (X : Set) : Set₁ where
  constructor cs
  field
    closed  : Bool
    srcLive : Bool
    srcAtt  : Bool
    bodyAt  : Maybe Pos
    attSrc  : Maybe Pos
    owedAt  : Maybe Pos
    connAt  : Pos
    endAt   : Pos
    src     : Obs C Γ X
    scope   : Scope Γ

data St (Γ : List Set) : Set → Set₁ where
  -- a subscription owed, and where it will be made
  pend  : ∀ {A} → Obs C Γ A → Pos → St Γ A
  -- a started cold: live, and what the runtime keeps of it
  coldS : ∀ {A} → Bool → L A → St Γ A
  -- the next value's index, where the of was subscribed, the values left
  ofS   : ∀ {A} → ℕ → Pos → List A → St Γ A
  doneS : ∀ {A} → St Γ A
  mapS  : ∀ {A B} → (A → B) → St Γ A → St Γ B
  scanS : ∀ {A B} → (B → A → B) → B → St Γ A → St Γ B
  -- a kill switch: live, its attach
  cutS  : ∀ {A} → Bool → Att → St Γ A → St Γ A
  -- a lane, still in its flatMap's list
  lnS   : ∀ {A} → Bool → St Γ A → St Γ A
  -- the child is its source's switch
  takeS : ∀ {A} → Bool → (A → Bool) → Owe → St Γ A → St Γ A
  -- outer done, lanes running, the values waiting for a slot, the
  -- outer's switch, every lane begun (oldest first)
  flatS : ∀ {A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → St Γ B
  connS : ∀ {X B} → CS Γ X → St Γ X → St (X ∷ Γ) B → St Γ B
  -- joined at `p`, live, its binder, and what it has been fed and not
  -- yet shown, each at the position it is shown at, in order
  joinS : ∀ {A} → Pos → Bool → A ∈ Γ → List (Pos × Ev A) → St Γ A

-- Whether a node is a lane still in its flatMap's list.
alive : ∀ {Γ A} → St Γ A → Bool
alive (lnS b s) = b
alive s         = true

------------------------------------------------------------------------
-- Contexts: one hole, at scope Γ and type A, in a root at [] and R.  A
-- lane's context keeps the lanes before it nearest first, so a walk
-- along a flatMap's list moves each lane across in one step.

data Ctx (R : Set) : List Set → Set → Set₁ where
  top     : Ctx R [] R
  inMap   : ∀ {Γ A B} → (A → B) → Ctx R Γ B → Ctx R Γ A
  inScan  : ∀ {Γ A B} → (B → A → B) → B → Ctx R Γ B → Ctx R Γ A
  inCut   : ∀ {Γ A} → Bool → Att → Ctx R Γ A → Ctx R Γ A
  inLn    : ∀ {Γ A} → Bool → Ctx R Γ A → Ctx R Γ A
  inTake  : ∀ {Γ A} → Bool → (A → Bool) → Owe → Ctx R Γ A → Ctx R Γ A
  inOuter : ∀ {Γ A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → List (St Γ B) → Ctx R Γ B → Ctx R Γ A
  inLanes : ∀ {Γ A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Ctx R Γ B → Ctx R Γ B
  inSrc   : ∀ {Γ X B} → CS Γ X → St (X ∷ Γ) B → Ctx R Γ B → Ctx R Γ X
  inBody  : ∀ {Γ X B} → CS Γ X → St Γ X → Ctx R Γ B → Ctx R (X ∷ Γ) B

-- The binders in scope at the hole, as their connects were given.
scopeOf : ∀ {R Γ A} → Ctx R Γ A → Scope Γ
scopeOf top                               = unbound
scopeOf (inMap f c)                       = scopeOf c
scopeOf (inScan f z c)                    = scopeOf c
scopeOf (inCut l a c)                     = scopeOf c
scopeOf (inLn b c)                        = scopeOf c
scopeOf (inTake i p w c)                  = scopeOf c
scopeOf (inOuter op f d n q ls c)         = scopeOf c
scopeOf (inLanes op f d n q o pre post c) = scopeOf c
scopeOf (inSrc k b c)                     = scopeOf c
scopeOf (inBody k o c)                    = binds (CS.src k) (CS.connAt k) (CS.scope k)

plug : ∀ {R Γ A} → Ctx R Γ A → St Γ A → St [] R
plug top                               s = s
plug (inMap f c)                       s = plug c (mapS f s)
plug (inScan f z c)                    s = plug c (scanS f z s)
plug (inCut l a c)                     s = plug c (cutS l a s)
plug (inLn b c)                        s = plug c (lnS b s)
plug (inTake i p w c)                  s = plug c (takeS i p w s)
plug (inOuter op f d n q ls c)         s = plug c (flatS op f d n q s ls)
plug (inLanes op f d n q o pre post c) s = plug c (flatS op f d n q o (pre ʳ++ s ∷ post))
plug (inSrc k b c)                     s = plug c (connS k s b)
plug (inBody k o c)                    s = plug c (connS k o s)

-- The child index of the hole in its parent.
dir : ∀ {R Γ A} → Ctx R Γ A → ℕ
dir (inLanes op f d n q o pre post c) = suc (length pre)
dir (inBody k o c)                    = 1
dir _                                 = 0

dirs : ∀ {R Γ A} → Ctx R Γ A → List ℕ
dirs top                                  = []
dirs c@(inMap f c′)                       = dirs c′ ++ [ dir c ]
dirs c@(inScan f z c′)                    = dirs c′ ++ [ dir c ]
dirs c@(inCut l a c′)                     = dirs c′ ++ [ dir c ]
dirs c@(inLn b c′)                        = dirs c′ ++ [ dir c ]
dirs c@(inTake i p w c′)                  = dirs c′ ++ [ dir c ]
dirs c@(inOuter op f d n q ls c′)         = dirs c′ ++ [ dir c ]
dirs c@(inLanes op f d n q o pre post c′) = dirs c′ ++ [ dir c ]
dirs c@(inSrc k b c′)                     = dirs c′ ++ [ dir c ]
dirs c@(inBody k o c′)                    = dirs c′ ++ [ dir c ]

-- What the hole's observer answers when polled: rxjs's `closed`.  A
-- switch off answers true; a connect's source asks its subject, and
-- answers true too once the connect itself is torn down.
closed : ∀ {R Γ A} → Ctx R Γ A → Bool
closed top                               = false
closed (inMap f c)                       = closed c
closed (inScan f z c)                    = closed c
closed (inCut l a c)                     = not l ∨ closed c
closed (inLn b c)                        = closed c
closed (inTake i p w c)                  = closed c
closed (inOuter op f d n q ls c)         = closed c
closed (inLanes op f d n q o pre post c) = closed c
closed (inSrc k b c)                     = CS.closed k ∨ closed c
closed (inBody k o c)                    = closed c

-- Whether a joiner's binder, up its own context, has completed.
closedUp : ∀ {R Γ A X} → Ctx R Γ A → X ∈ Γ → Bool
closedUp top                               ()
closedUp (inMap f c)                       x = closedUp c x
closedUp (inScan f z c)                    x = closedUp c x
closedUp (inCut l a c)                     x = closedUp c x
closedUp (inLn b c)                        x = closedUp c x
closedUp (inTake i p w c)                  x = closedUp c x
closedUp (inOuter op f d n q ls c)         x = closedUp c x
closedUp (inLanes op f d n q o pre post c) x = closedUp c x
closedUp (inSrc k b c)                     x = closedUp c x
closedUp (inBody k o c)            (here refl) = CS.closed k
closedUp (inBody k o c)            (there x)   = closedUp c x

------------------------------------------------------------------------
-- Unsubscribing, node by node, as each operator's subscription reads.  A
-- switch cut before its subscription is attached defers the unsubscribe
-- to the attach, as `Kit.attach` does.  Every started cold it reaches is
-- handed back, to be stopped.

Torn : Set₁
Torn = List (Σ Set L)

private
  wrap : ∀ {X Y : Set₁} → (X → Y) → X × Torn → Y × Torn
  wrap f (x , t) = f x , t

  both : ∀ {X Y Z : Set₁} → (X → Y → Z) → X × Torn → Y × Torn → Z × Torn
  both f (x , t) (y , u) = f x y , t ++ u

mutual
  unsub : ∀ {Γ A} → St Γ A → St Γ A × Torn
  unsub (coldS true l)          = coldS false l , [ (_ , l) ]
  unsub (mapS f s)              = wrap (mapS f) (unsub s)
  unsub (scanS f z s)           = wrap (scanS f z) (unsub s)
  unsub (takeS i p w s)         = wrap (takeS i p w) (cut s)
  unsub (flatS op f d n q o ls) = both (flatS op f d 0 q) (cut o) (killAll ls)
  unsub (connS k o b)           = both (connS k) (unsub o) (unsub b)
  unsub (joinS j g x ib)        = joinS j false x [] , []
  unsub s                       = s , []

  cut : ∀ {Γ A} → St Γ A → St Γ A × Torn
  cut (cutS l attached s)  = wrap (cutS false attached) (unsub s)
  cut (cutS l (attAt p) s) = cutS false (attAt p) s , []
  cut s                    = s , []

  killAll : ∀ {Γ B} → List (St Γ B) → List (St Γ B) × Torn
  killAll []                = [] , []
  killAll (lnS true s ∷ ls) = both (λ s′ ls′ → lnS false s′ ∷ ls′) (cut s) (killAll ls)
  killAll (l ∷ ls)          = wrap (l ∷_) (killAll ls)

unsubIf : ∀ {Γ A} → Bool → St Γ A → St Γ A × Torn
unsubIf true  s = unsub s
unsubIf false s = s , []

------------------------------------------------------------------------
-- A connect's feed, pushed into each of its live joiners

-- A step at `p` queued last for a joiner joined at `j`: under where it
-- joined if it joined before; else a value is not its, and an end is at
-- once.
queued : ∀ {A} → Pos → Pos → Ev A → List (Pos × Ev A) → List (Pos × Ev A)
queued j p (nx a) ib = if j <ᵖ p then ib ++ [ (p ⊕ [ subᴾ j ] , nx a) ] else ib
queued j p cp     ib = ib ++ [ (if j <ᵖ p then p ⊕ [ subᴾ j ] else j ⊕ [ last ]) , cp ]

-- Binder `i`'s step at `p`, fed to every joiner of it still live.
mutual
  feed : ∀ {Γ X A} → X ∈ Γ → Pos → Ev X → St Γ A → St Γ A
  feed i p e (joinS j true x ib) with same? i x
  ... | just refl = joinS j true x (queued j p e ib)
  ... | nothing   = joinS j true x ib
  feed i p e (mapS f s)              = mapS f (feed i p e s)
  feed i p e (scanS f z s)           = scanS f z (feed i p e s)
  feed i p e (cutS l a s)            = cutS l a (feed i p e s)
  feed i p e (lnS b s)               = lnS b (feed i p e s)
  feed i p e (takeS v q w s)         = takeS v q w (feed i p e s)
  feed i p e (flatS op f d n q o ls) = flatS op f d n q (feed i p e o) (feedL i p e ls)
  feed i p e (connS k o b)           = connS k (feed i p e o) (feed (there i) p e b)
  feed i p e s                       = s

  feedL : ∀ {Γ X A} → X ∈ Γ → Pos → Ev X → List (St Γ A) → List (St Γ A)
  feedL i p e []       = []
  feedL i p e (s ∷ ls) = feed i p e s ∷ feedL i p e ls

------------------------------------------------------------------------
-- Moving the focus

Focus : Set → Set₁
Focus R = Σ (List Set) λ Γ → Σ Set λ A → Ctx R Γ A × St Γ A

pickL : ∀ {Γ B} → ℕ → List (St Γ B) → List (St Γ B) → Maybe (List (St Γ B) × St Γ B × List (St Γ B))
pickL i       pre []         = nothing
pickL zero    pre (s ∷ post) = just (pre , s , post)
pickL (suc i) pre (s ∷ post) = pickL i (s ∷ pre) post

down : ∀ {R Γ A} → ℕ → Ctx R Γ A → St Γ A → Maybe (Focus R)
down zero          c (mapS f s)              = just (_ , _ , inMap f c , s)
down zero          c (scanS f z s)           = just (_ , _ , inScan f z c , s)
down zero          c (cutS l a s)            = just (_ , _ , inCut l a c , s)
down zero          c (lnS b s)               = just (_ , _ , inLn b c , s)
down zero          c (takeS i p w s)         = just (_ , _ , inTake i p w c , s)
down zero          c (flatS op f d n q o ls) = just (_ , _ , inOuter op f d n q ls c , o)
down zero          c (connS k o b)           = just (_ , _ , inSrc k b c , o)
down (suc zero)    c (connS k o b)           = just (_ , _ , inBody k o c , b)
down (suc i)       c (flatS op f d n q o ls) with pickL i [] ls
... | just (pre , s , post) = just (_ , _ , inLanes op f d n q o pre post c , s)
... | nothing               = nothing
down _             c _                       = nothing

downs : ∀ {R Γ A} → List ℕ → Ctx R Γ A → St Γ A → Maybe (Focus R)
downs []      c s = just (_ , _ , c , s)
downs (i ∷ p) c s with down i c s
... | just (_ , _ , c′ , s′) = downs p c′ s′
... | nothing                = nothing

------------------------------------------------------------------------
-- The marks, and the least of them

data Mark : Set where
  ofM attM bodyM srcAttM owedM cpM cutM joinM leafM : Mark

-- What a node itself owes, each keyed.
own : ∀ {Γ A} → St Γ A → List (Mark × Key)
own (coldS b l) with due l
... | just k  = [ (leafM , k) ]
... | nothing = []
own (ofS i p [])               = [ (ofM , at (p ⊕ [ last ])) ]
own (ofS i p (_ ∷ _))          = [ (ofM , at (p ⊕ [ ix i ])) ]
own (cutS l (attAt p) s)       = [ (attM , after p) ]
own (takeS i q (cpAt p) s)     = [ (cpM , at (p ⊕ [ last ])) ]
own (takeS i q (cutAt p) s)    = [ (cutM , after p) ]
own (connS k o b)              = body (CS.bodyAt k) ++ src (CS.attSrc k) ++ owed (CS.owedAt k)
  where
    body src owed : Maybe Pos → List (Mark × Key)
    body (just p) = [ (bodyM , at (p ⊕ [ ix 1 ])) ]
    body nothing  = []
    src (just p)  = [ (srcAttM , after p) ]
    src nothing   = []
    owed (just p) = [ (owedM , after p) ]
    owed nothing  = []
own (joinS j g x ((q , _) ∷ _)) = [ (joinM , at q) ]
own _                           = []

record Found (R : Set) : Set₁ where
  constructor found
  field
    focus : Focus R
    mark  : Mark
    key   : Key

-- What a mark run shows its parent: an event, or nothing.
data Out (A : Set) : Set where
  still : Out A
  shows : Ev A → Out A

-- A mark, with where its event sits as the node above sees it.
Cand : Set → Set → Set₁
Cand R A = Found R × Key × Out A

-- The earlier; the first on a tie.
first : ∀ {R A} → Maybe (Cand R A) → Maybe (Cand R A) → Maybe (Cand R A)
first nothing             y                     = y
first (just x)            nothing               = just x
first (just (f , h , o))  (just (g , h′ , o′))  = if h′ <ᴷ h then just (g , h′ , o′) else just (f , h , o)

retag : ∀ {R A B} → (Key → Out A → Key × Out B) → Maybe (Cand R A) → Maybe (Cand R B)
retag t nothing            = nothing
retag t (just (f , h , o)) = just (f , t h o)

-- What a node's own mark shows.
outOf : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Mark → Out A
outOf c (ofS i p xs) ofM with closed c | xs
... | true  | _     = still
... | false | []    = shows cp
... | false | x ∷ _ = shows (nx x)
outOf c (takeS i q (cpAt p) s) cpM = if not (closed c) then shows cp else still
outOf c (joinS j g x ((q , e) ∷ ib)) joinM = if g ∧ not (closed c) then shows e else still
outOf c (coldS b l) leafM with peek l
... | just nothing  = if b ∧ not (closed c) then shows cp else still
... | just (just a) = if b ∧ not (closed c) then shows (nx a) else still
... | nothing       = still
outOf c s m = still

ownBest : ∀ {R Γ A} → Ctx R Γ A → St Γ A → List (Mark × Key) → Maybe (Cand R A)
ownBest c s []             = nothing
ownBest c s ((m , k) ∷ ms) = first (just (found (_ , _ , c , s) m k , k , outOf c s m)) (ownBest c s ms)

-- Each node's rise, as its parent reads it.
mapT : ∀ {A B} → (A → B) → Key → Out A → Key × Out B
mapT f h still     = h , still
mapT f h (shows e) = h , shows (mapEv f e)

scanT : ∀ {A B} → (B → A → B) → B → Key → Out A → Key × Out B
scanT f z h (shows (nx a)) = h , shows (nx (f z a))
scanT f z h (shows cp)     = h , shows cp
scanT f z h still          = h , still

cutT : ∀ {A} → Bool → Key → Out A → Key × Out A
cutT l h o = h , (if l then o else still)

-- A failing value: inclusive, shown; else dropped, the end owed.
takeT : ∀ {A} → Bool → (A → Bool) → Owe → Key → Out A → Key × Out A
takeT i q free h (shows (nx a)) = h , (if q a ∨ i then shows (nx a) else still)
takeT i q free h o              = h , o
takeT i q w    h o              = h , still

-- The outer's value shows nothing; its end ends the flatMap only with
-- nothing running or waiting.
outerT : ∀ {A B : Set} → ℕ → List A → Key → Out A → Key × Out B
outerT n q h (shows cp) = h , (if (n ≡ᵇ 0) ∧ null q then shows cp else still)
outerT n q h (shows (nx a)) = h , still
outerT n q h still          = h , still

-- A lane's end: nothing when a value waits, else the flatMap's end once
-- nothing else runs.
laneT : ∀ {A B : Set} → Bool → ℕ → List A → Key → Out B → Key × Out B
laneT d n []      h (shows cp) = h , (if d ∧ (pred n ≡ᵇ 0) then shows cp else still)
laneT d n (_ ∷ _) h (shows cp) = h , still
laneT d n q       h o          = h , o

-- The outer only strictly before the earliest lane, each by its own
-- head; the winner's event then read as the flatMap's.
raceT : ∀ {R A B} → Bool → ℕ → List A → Maybe (Cand R A) → Maybe (Cand R B) → Maybe (Cand R B)
raceT d n q nothing            nothing              = nothing
raceT d n q nothing            (just (g , k , o′))  = just (g , laneT d n q k o′)
raceT d n q (just (f , h , o)) nothing              = just (f , outerT n q h o)
raceT d n q (just (f , h , o)) (just (g , k , o′))  = if h <ᴷ k then just (f , outerT n q h o) else just (g , laneT d n q k o′)

-- The source only strictly before the body, showing nothing; every key
-- raced as its own mark has it, so the least found is the least owned.
sourceT : ∀ {R A B} → Maybe (Cand R A) → Maybe (Cand R B) → Maybe (Cand R B)
sourceT nothing            b                    = b
sourceT (just (f , h , o)) nothing              = just (f , h , still)
sourceT (just (f , h , o)) (just (g , k , o′))  = if h <ᴷ k then just (f , h , still) else just (g , k , o′)

-- The mark the stepper races first under the hole, a node's own before
-- its children on a tie.
mutual
  seek : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Maybe (Cand R A)
  seek c s = first (ownBest c s (own s)) (kids c s)

  kids : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Maybe (Cand R A)
  kids c (mapS f s)              = retag (mapT f) (seek (inMap f c) s)
  kids c (scanS f z s)           = retag (scanT f z) (seek (inScan f z c) s)
  kids c (cutS l a s)            = retag (cutT l) (seek (inCut l a c) s)
  kids c (lnS b s)               = seek (inLn b c) s
  kids c (takeS i q w s)         = retag (takeT i q w) (seek (inTake i q w c) s)
  kids c (flatS op f d n q o ls) = raceT d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls)
  kids c (connS k o b)           = sourceT (seek (inSrc k b c) o) (seek (inBody k o c) b)
  kids c _                       = nothing

  lanes : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Maybe (Cand R B)
  lanes c op f d n q o pre []         = nothing
  lanes c op f d n q o pre (s ∷ post) =
    first (retag (cutT (alive s)) (seek (inLanes op f d n q o pre post c) s)) (lanes c op f d n q o (s ∷ pre) post)

search : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Maybe (Found R)
search c s = mapᴹ proj₁ (seek c s)

------------------------------------------------------------------------
-- The machine

data Mode (A : Set) : Set where
  subscribing absorbed : Mode A
  rising : Ev A → Mode A

record Conf (R : Set) : Set₁ where
  constructor ⟨_,_,_,_⟩
  field
    {Γ}  : List Set
    {A}  : Set
    ctx  : Ctx R Γ A
    foc  : St Γ A
    mode : Mode A
    pos  : Pos

-- What the root is shown, and where.
Shown : Set → Set
Shown R = List (Pos × Ev R)

-- A started cold, its turn come: whether it is live; its state; whether
-- its observer is closed; a delivery into it at a position, with its
-- state after; its state replaced, nothing delivered.
data Poke (R : Set) : Set₁ where
  gone : Poke R
  leaf : ∀ {A} → Bool → L A → Bool → (Ev A → L A → Bool → Pos → Conf R) → (L A → Conf R) → Poke R

-- A step taken, what it showed and the colds it tore down; a cold
-- subscribed, the run stopped until the runtime hands back its state; a
-- started cold's mark the least, for the runtime to play; nothing owed.
data Stepped (R : Set) : Set₁ where
  moved    : Conf R → Shown R → Torn → Stepped R
  starting : ∀ {A} → C A → Pos → (L A → Conf R) → Stepped R
  turn     : Poke R → Stepped R
  quiet    : Stepped R

private
  ok : ∀ {R} → Conf R → Stepped R
  ok k = moved k [] []

begin : ∀ {R Γ A} → Ctx R Γ A → Obs C Γ A → Pos → Stepped R
begin c (cold x)          p = starting x p λ l → ⟨ c , coldS true l , absorbed , p ⟩
begin c empty             p = ok ⟨ c , ofS 0 p [] , absorbed , p ⟩
begin c (of xs)           p = ok ⟨ c , ofS 0 p xs , absorbed , p ⟩
begin c (map f s)         p = ok ⟨ inMap f c , pend s p , subscribing , p ⟩
begin c (scan f z s)      p = ok ⟨ inScan f z c , pend s p , subscribing , p ⟩
begin c (takeWhile i q s) p = ok ⟨ inCut true (attAt p) (inTake i q free c) , pend s p , subscribing , p ⟩
begin c (flatMap op f s)  p = ok ⟨ inCut true (attAt p) (inOuter op f false 0 [] [] c) , pend s p , subscribing , p ⟩
-- the body under `ix 0`; its source, once the body's subscription
-- exists, under `ix 1`
begin c (connect s b)     p = ok ⟨ inBody (cs false true false (just p) nothing nothing p root s (scopeOf c)) (pend s (p ⊕ [ ix 1 ])) c , pend b (p ⊕ [ ix 0 ]) , subscribing , p ⊕ [ ix 0 ] ⟩
-- a joiner keeps where it joined; a completed subject owes it its end under `last`
begin c (connected x)     p with closedUp c x
... | true  = ok ⟨ c , ofS 0 p [] , absorbed , p ⟩
... | false = ok ⟨ c , joinS p true x [] , absorbed , p ⟩
-- a defer's body one level down
begin c (defer l)         p = ok ⟨ c , pend (Later.force l) (p ⊕ [ ix 1 ]) , subscribing , p ⊕ [ ix 1 ] ⟩

-- A lane begun under `ix 1`, unless the flatMap's own observer is closed.
start : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → A → Pos → Conf R
start c op f d n q o ls a p with closed c
... | true  = ⟨ c , flatS op f d n q o ls , absorbed , p ⟩
... | false = ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c)) , pend (f a) (p ⊕ [ ix 1 ]) , subscribing , p ⊕ [ ix 1 ] ⟩

-- The outer done, no lane running and, `e`, none waiting: complete.
settle : ∀ {B} → Bool → ℕ → Bool → Mode B
settle d n e = if d ∧ (n ≡ᵇ 0) ∧ e then rising cp else absorbed

-- A slot freed: the next waiting value's lane begun, else settle.
dequeue : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → Pos → Conf R
dequeue c op f d n []      o ls p = ⟨ c , flatS op f d n [] o ls , settle d n true , p ⟩
dequeue c op f d n (a ∷ q) o ls p = start c op f d n q o ls a p

admit : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → A → Pos → Stepped R
admit c (mergeᶠ nothing)  f d n q o ls a p = ok (start c (mergeᶠ nothing) f d n q o ls a p)
admit c (mergeᶠ (just m)) f d n q o ls a p =
  ok (if n <ᵇ m then start c (mergeᶠ (just m)) f d n q o ls a p
      else ⟨ c , flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls , absorbed , p ⟩)
admit c switchᶠ           f d n q o ls a p with killAll ls
... | ls′ , t = moved (start c switchᶠ f d 0 q o ls′ a p) [] t
admit c exhaustᶠ          f d n q o ls a p with n ≡ᵇ 0
... | true  = ok (start c exhaustᶠ f d n q o ls a p)
... | false = ok ⟨ c , flatS exhaustᶠ f d n q o ls , absorbed , p ⟩

ended : ∀ {Γ B} → St Γ B → St Γ B
ended (lnS b (cutS l a s)) = lnS false (cutS false a s)
ended s                    = s

-- A rise moves no position, except an inclusive takeWhile's failing
-- value, under `ix 0`; a non-inclusive one's end is owed under `last`.  A connect's source feeds every
-- live joiner of its subject at once, each to show it at its own turn.
rise : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Ev A → Pos → Stepped R
rise top s e p = moved ⟨ top , s , absorbed , p ⟩ [ (p , e) ] []
rise (inMap f c) s e p = ok ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
rise (inScan f z c) s (nx a) p = ok ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
rise (inScan f z c) s cp     p = ok ⟨ c , scanS f z s , rising cp , p ⟩
rise (inCut l a c) s e p = ok ⟨ c , cutS l a s , (if l then rising e else absorbed) , p ⟩
rise (inLn b c) s e p = ok ⟨ c , lnS b s , rising e , p ⟩
rise (inTake i q free c) s (nx a) p with q a | i
... | true  | _     = ok ⟨ c , takeS i q free s , rising (nx a) , p ⟩
... | false | true  = ok ⟨ c , takeS i q (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩
... | false | false = ok ⟨ c , takeS i q (cpAt p) s , absorbed , p ⟩
rise (inTake i q free c) s cp p = ok ⟨ c , takeS i q free s , rising cp , p ⟩
-- a takeWhile already over absorbs whatever still reaches it, as a
-- switch off does
rise (inTake i q (cpAt r) c)  s e p = ok ⟨ c , takeS i q (cpAt r) s , absorbed , p ⟩
rise (inTake i q (cutAt r) c) s e p = ok ⟨ c , takeS i q (cutAt r) s , absorbed , p ⟩
rise (inTake i q (overAt r) c) s e p = ok ⟨ c , takeS i q (overAt r) s , absorbed , p ⟩
rise (inOuter op f d n q ls c) o (nx a) p = admit c op f d n q o ls a p
-- A done outer's end is absorbed, as a stopped subscriber ignores it.
rise (inOuter op f d n q ls c) o cp     p = ok ⟨ c , flatS op f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
-- a lane out of its flatMap's list is over, and absorbs what still reaches it
rise (inLanes op f d n q o pre post c) s (nx b) p =
  ok (if alive s then ⟨ c , flatS op f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩ else ⟨ c , flatS op f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise (inLanes op f d n q o pre post c) s cp     p =
  ok (if alive s then dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p else ⟨ c , flatS op f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise (inSrc k b c) s (nx a) p = ok ⟨ c , connS k s (feed (here refl) p (nx a) b) , absorbed , p ⟩
rise (inSrc k b c) s cp     p = ok ⟨ c , connS (record k { closed = true ; endAt = p }) s (feed (here refl) p cp b) , absorbed , p ⟩
-- a body after its source's teardown has completed, and is stopped
rise (inBody k o c) s (nx b) p =
  ok (if CS.srcLive k then ⟨ c , connS k o s , rising (nx b) , p ⟩ else ⟨ c , connS k o s , absorbed , p ⟩)
rise (inBody k o c) s cp     p =
  ok (if CS.srcLive k then ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩ else ⟨ c , connS k o s , absorbed , p ⟩)

-- A mark run: the node's continuation, resumed where it was left.
run : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Mark → Pos → Stepped R
-- the i-th value under `ix i`, the completion under `last`, of where the of was subscribed
run c (ofS i p xs) ofM _ with closed c | xs
... | true  | _       = ok ⟨ c , doneS , absorbed , p ⟩
... | false | []      = ok ⟨ c , doneS , rising cp , p ⊕ [ last ] ⟩
... | false | x ∷ xs′ = ok ⟨ c , ofS (suc i) p xs′ , rising (nx x) , p ⊕ [ ix i ] ⟩
run c (cutS l (attAt p) s) attM _ with unsubIf (not l) s
... | s′ , t = moved ⟨ c , cutS l attached s′ , absorbed , p ⟩ [] t
run c (takeS i q (cpAt p) s) cpM _ = ok ⟨ c , takeS i q (cutAt p) s , (if not (closed c) then rising cp else absorbed) , p ⊕ [ last ] ⟩
run c (takeS i q (cutAt p) s) cutM _ with cut s
... | s′ , t = moved ⟨ c , takeS i q (overAt p) s′ , absorbed , p ⟩ [] t
run c (connS k o b) bodyM r with CS.bodyAt k
... | just p  = ok ⟨ inSrc (record k { bodyAt = nothing ; attSrc = just (p ⊕ [ ix 1 ]) }) b c , o , subscribing , p ⊕ [ ix 1 ] ⟩
... | nothing = ok ⟨ c , connS k o b , absorbed , r ⟩
run c (connS k o b) srcAttM r with CS.attSrc k | unsubIf (not (CS.srcLive k)) o
... | just p  | o′ , t = moved ⟨ c , connS (record k { srcAtt = true ; attSrc = nothing }) o′ b , absorbed , p ⟩ [] t
... | nothing | _      = ok ⟨ c , connS k o b , absorbed , r ⟩
run c (connS k o b) owedM r with CS.owedAt k | unsubIf (CS.srcAtt k) o
... | just p  | o′ , t = moved ⟨ c , connS (record k { srcLive = false ; owedAt = nothing }) o′ b , absorbed , p ⟩ [] t
... | nothing | _      = ok ⟨ c , connS k o b , absorbed , r ⟩
-- a joiner's completion leaves it off, as an unsubscribe does
run c (joinS j g x ((q , nx a) ∷ ib)) joinM _ = ok ⟨ c , joinS j g x ib , (if g ∧ not (closed c) then rising (nx a) else absorbed) , q ⟩
run c (joinS j g x ((q , cp) ∷ ib))   joinM _ = ok ⟨ c , joinS j false x ib , (if g ∧ not (closed c) then rising cp else absorbed) , q ⟩
run c (coldS b l) leafM r =
  turn (leaf b l (closed c) (λ e l′ b′ p′ → ⟨ c , coldS b′ l′ , (if not (closed c) then rising e else absorbed) , p′ ⟩) (λ l′ → ⟨ c , coldS b l′ , absorbed , r ⟩))
run c s m r = ok ⟨ c , s , absorbed , r ⟩

-- By the mode first, so a fact about a step splits on the mode alone.
stepAt : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Mode A → Pos → Stepped R
stepAt c s (rising e)   p = rise c s e p
stepAt c (pend o q) subscribing _ = begin c o q
stepAt c s subscribing p = ok ⟨ c , s , subscribing , p ⟩
-- the least mark run
stepAt c s absorbed p with search top (plug c s)
... | just (found (_ , _ , c′ , s′) m k) = run c′ s′ m p
... | nothing                            = quiet

step : ∀ {R} → Conf R → Stepped R
step ⟨ c , s , m , p ⟩ = stepAt c s m p

-- The root subscribed.
load : ∀ {R} → Obs C [] R → Conf R
load o = ⟨ top , pend o root , subscribing , root ⟩

------------------------------------------------------------------------
-- What a runtime reads and does

-- Where the focus is, from the root.
spot : ∀ {R} → Conf R → List ℕ
spot k = dirs (Conf.ctx k)

-- Everything running now absorbed.
calm : ∀ {R} → Conf R → Bool
calm k with Conf.mode k
... | absorbed = true
... | _        = false

-- When the next mark is due, if any is.
next : ∀ {R} → Conf R → Maybe Key
next ⟨ c , s , m , p ⟩ with search top (plug c s)
... | just f  = just (Found.key f)
... | nothing = nothing

-- A started cold, found by its path.
poke : ∀ {R} → List ℕ → Conf R → Poke R
poke π ⟨ c , s , m , p ⟩ with downs π top (plug c s)
... | just (_ , _ , c′ , coldS b l) =
  leaf b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩) (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p ⟩)
... | _ = gone
