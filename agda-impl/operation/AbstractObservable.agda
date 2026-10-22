{-# OPTIONS --guardedness #-}

-- THE ABSTRACT OBSERVABLE: the engine both runtimes are.  `Tree.Obs` run
-- as a typed zipper over a tree of operator states, one node per
-- subscribed operator.  No heap, no worlds, no names: a node is addressed by its PATH from the root, and
-- every path stays valid, because the tree only grows — a lane, once
-- begun, keeps its slot in its flatMap's list after it ends.
--
-- Control is the zipper's focus.  A subscription begins by moving the
-- focus down; a value rises by moving it up; a job owed later (an `of`'s
-- next value, a subscription's attach, a takeWhile's completion, a
-- connect's feed) is a path, a tag and the position it was suspended at,
-- resumed once what runs now is absorbed.  A join is reached from its
-- subject by a path relative to the binder, and reads the value it is fed
-- from the binder above it in its own context, where the types line up by
-- the de Bruijn index.
--
-- SHARED BY BOTH RUNTIMES.  Parametric in the cold leaf `C` and in `L`,
-- what a runtime keeps at a started cold, so it can neither look inside a
-- cold nor perform IO.  The machine never runs a cold: subscribing one
-- STOPS the step (`starting`) and hands the runtime a continuation typed
-- at the cold's element, which the runtime resumes with the leaf's state.
-- A runtime then drives a leaf by its path (`poke`): it reads the leaf's
-- state, asks whether its observer is closed, and delivers into it.  An
-- unsubscribe reaching a started cold hands its state back (`Torn`), for
-- the runtime to stop.
--
-- POSITIONS are a ghost nothing branches on: the run's position, carried
-- so that each value is shown where `denotation.MonotonicList.Events`
-- places it.
module operation.AbstractObservable (C L : Set → Set₁) where

open import Data.List using (List; []; _∷_; _++_; [_]; length; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; ix; last; root) renaming (sub to subᴾ)

data Ev (A : Set) : Set where
  nx : A → Ev A
  cp : Ev A

mapEv : ∀ {A B} → (A → B) → Ev A → Ev B
mapEv f (nx a) = nx (f a)
mapEv f cp     = cp

------------------------------------------------------------------------
-- States

-- A connect's subject and its source's switch.  `feeds` is a STACK: a
-- value fed while another feed is under way is fed first, as the
-- kernel's nested `each` would; who is still to be fed rides on the
-- feed's own job, as on `each`'s continuation.
record CS (X : Set) : Set where
  constructor cs
  field
    closed  : Bool
    subs    : List (List ℕ × Pos)               -- each joiner, by its path from the binder, and where it joined
    feeds   : List (Ev X)                       -- what is being fed
    bodyAtt : Bool
    srcLive : Bool
    srcAtt  : Bool

data St (Γ : List Set) : Set → Set₁ where
  pend  : ∀ {A} → Obs C Γ A → St Γ A
  -- a started cold: live, and what the runtime keeps of it
  coldS : ∀ {A} → Bool → L A → St Γ A
  -- the values still to come
  ofS   : ∀ {A} → List A → St Γ A
  doneS : ∀ {A} → St Γ A
  mapS  : ∀ {A B} → (A → B) → St Γ A → St Γ B
  scanS : ∀ {A B} → (B → A → B) → B → St Γ A → St Γ B
  -- a kill switch: live, attached
  cutS  : ∀ {A} → Bool → Bool → St Γ A → St Γ A
  -- a lane, still in its flatMap's list
  lnS   : ∀ {A} → Bool → St Γ A → St Γ A
  -- the child is its source's switch
  takeS : ∀ {A} → Bool → (A → Bool) → St Γ A → St Γ A
  -- outer done, lanes running, the values waiting for a slot, the
  -- outer's switch, every lane begun (oldest first)
  flatS : ∀ {A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → St Γ B
  connS : ∀ {X B} → CS X → St Γ X → St (X ∷ Γ) B → St Γ B
  joinS : ∀ {A} → Pos → Bool → A ∈ Γ → St Γ A

------------------------------------------------------------------------
-- Contexts: one hole, at scope Γ and type A, in a root at [] and R.

data Ctx (R : Set) : List Set → Set → Set₁ where
  top     : Ctx R [] R
  inMap   : ∀ {Γ A B} → (A → B) → Ctx R Γ B → Ctx R Γ A
  inScan  : ∀ {Γ A B} → (B → A → B) → B → Ctx R Γ B → Ctx R Γ A
  inCut   : ∀ {Γ A} → Bool → Bool → Ctx R Γ A → Ctx R Γ A
  inLn    : ∀ {Γ A} → Bool → Ctx R Γ A → Ctx R Γ A
  inTake  : ∀ {Γ A} → Bool → (A → Bool) → Ctx R Γ A → Ctx R Γ A
  inOuter : ∀ {Γ A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → List (St Γ B) → Ctx R Γ B → Ctx R Γ A
  inLanes : ∀ {Γ A B} → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → List (St Γ B) → Ctx R Γ B → Ctx R Γ B
  inSrc   : ∀ {Γ X B} → CS X → St (X ∷ Γ) B → Ctx R Γ B → Ctx R Γ X
  inBody  : ∀ {Γ X B} → CS X → St Γ X → Ctx R Γ B → Ctx R (X ∷ Γ) B

plug : ∀ {R Γ A} → Ctx R Γ A → St Γ A → St [] R
plug top                               s = s
plug (inMap f c)                       s = plug c (mapS f s)
plug (inScan f z c)                    s = plug c (scanS f z s)
plug (inCut l a c)                     s = plug c (cutS l a s)
plug (inLn b c)                        s = plug c (lnS b s)
plug (inTake i p c)                    s = plug c (takeS i p s)
plug (inOuter op f d n q ls c)         s = plug c (flatS op f d n q s ls)
plug (inLanes op f d n q o pre post c) s = plug c (flatS op f d n q o (pre ++ s ∷ post))
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
dirs c@(inTake i p c′)                    = dirs c′ ++ [ dir c ]
dirs c@(inOuter op f d n q ls c′)         = dirs c′ ++ [ dir c ]
dirs c@(inLanes op f d n q o pre post c′) = dirs c′ ++ [ dir c ]
dirs c@(inSrc k b c′)                     = dirs c′ ++ [ dir c ]
dirs c@(inBody k o c′)                    = dirs c′ ++ [ dir c ]

-- What the hole's observer answers when polled: rxjs's `closed`.  A
-- switch off answers true; a connect's source asks its subject.
closed : ∀ {R Γ A} → Ctx R Γ A → Bool
closed top                               = false
closed (inMap f c)                       = closed c
closed (inScan f z c)                    = closed c
closed (inCut l a c)                     = not l ∨ closed c
closed (inLn b c)                        = closed c
closed (inTake i p c)                    = closed c
closed (inOuter op f d n q ls c)         = closed c
closed (inLanes op f d n q o pre post c) = closed c
closed (inSrc k b c)                     = CS.closed k
closed (inBody k o c)                    = closed c

------------------------------------------------------------------------
-- Unsubscribing, node by node, as each operator's subscription reads.  A switch cut before its subscription is
-- attached defers the unsubscribe to the attach, as `Kit.attach` does.
-- Every started cold it reaches is handed back, to be stopped.

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
  unsub (takeS i p s)           = wrap (takeS i p) (cut s)
  unsub (flatS op f d n q o ls) = both (flatS op f d 0 q) (cut o) (killAll ls)
  unsub (connS k o b)           = both (connS k) (unsub o) (unsub b)
  unsub (joinS j g x)           = joinS j false x , []
  unsub s                       = s , []

  cut : ∀ {Γ A} → St Γ A → St Γ A × Torn
  cut (cutS l true s)  = wrap (cutS false true) (unsub s)
  cut (cutS l false s) = cutS false false s , []
  cut s                = s , []

  killAll : ∀ {Γ B} → List (St Γ B) → List (St Γ B) × Torn
  killAll []                = [] , []
  killAll (lnS true s ∷ ls) = both (λ s′ ls′ → lnS false s′ ∷ ls′) (cut s) (killAll ls)
  killAll (l ∷ ls)          = wrap (l ∷_) (killAll ls)

------------------------------------------------------------------------
-- Moving the focus

Focus : Set → Set₁
Focus R = Σ (List Set) λ Γ → Σ Set λ A → Ctx R Γ A × St Γ A

pickL : ∀ {Γ B} → ℕ → List (St Γ B) → List (St Γ B) → Maybe (List (St Γ B) × St Γ B × List (St Γ B))
pickL i       pre []         = nothing
pickL zero    pre (s ∷ post) = just (pre , s , post)
pickL (suc i) pre (s ∷ post) = pickL i (pre ++ [ s ]) post

down : ∀ {R Γ A} → ℕ → Ctx R Γ A → St Γ A → Maybe (Focus R)
down zero          c (mapS f s)              = just (_ , _ , inMap f c , s)
down zero          c (scanS f z s)           = just (_ , _ , inScan f z c , s)
down zero          c (cutS l a s)            = just (_ , _ , inCut l a c , s)
down zero          c (lnS b s)               = just (_ , _ , inLn b c , s)
down zero          c (takeS i p s)           = just (_ , _ , inTake i p c , s)
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
-- A join and its binder, found up the join's own context

-- Joining: the binder's subject closed, or the joiner's path appended.
-- `acc` is the path from the frame reached down to the joiner.
joinUp : ∀ {R Γ A X} → Pos → Ctx R Γ A → X ∈ Γ → List ℕ → Bool × Ctx R Γ A
joinUp j top                           ()        acc
joinUp j c@(inMap f c′)                x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inMap f c″
joinUp j c@(inScan f z c′)             x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inScan f z c″
joinUp j c@(inCut l a c′)              x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inCut l a c″
joinUp j c@(inLn l c′)                 x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inLn l c″
joinUp j c@(inTake i p c′)             x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inTake i p c″
joinUp j c@(inOuter op f d n q ls c′)  x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inOuter op f d n q ls c″
joinUp j c@(inLanes op f d n q o pre post c′) x  acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inLanes op f d n q o pre post c″
joinUp j c@(inSrc k b′ c′)             x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inSrc k b′ c″
joinUp j (inBody k o c′)               (here refl) acc with CS.closed k
... | true  = true , inBody k o c′
... | false = false , inBody (record k { subs = CS.subs k ++ [ (1 ∷ acc , j) ] }) o c′
joinUp j c@(inBody k o c′)             (there x) acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inBody k o c″

-- What the binder is feeding now.
fedUp : ∀ {R Γ A X} → Ctx R Γ A → X ∈ Γ → Maybe (Ev X)
fedUp top                               ()
fedUp (inMap f c)                       x = fedUp c x
fedUp (inScan f z c)                    x = fedUp c x
fedUp (inCut l a c)                     x = fedUp c x
fedUp (inLn b c)                        x = fedUp c x
fedUp (inTake i p c)                    x = fedUp c x
fedUp (inOuter op f d n q ls c)         x = fedUp c x
fedUp (inLanes op f d n q o pre post c) x = fedUp c x
fedUp (inSrc k b c)                     x = fedUp c x
fedUp (inBody k o c)            (here refl) with CS.feeds k
... | e ∷ _ = just e
... | []    = nothing
fedUp (inBody k o c)            (there x) = fedUp c x

------------------------------------------------------------------------
-- The machine

-- What a resumed job is: a joiner's feed; the attach of its child's
-- subscription (a connect's body, then its source); what a body's
-- completion left owed.
data Tag : Set where
  go att attBody owed : Tag
  -- an of's i-th value
  next : ℕ → Tag
  -- a takeWhile's completion owed, then its cut
  owedCp owedCut : Tag
  -- a feed under way: the joiners still to feed, by path from the root,
  -- and where each joined
  feeding : List (List ℕ × Pos) → Tag

-- A job: the node, by its path; what it owes; where the run resumes it.
Job : Set
Job = List ℕ × Tag × Pos

data Mode (A : Set) : Set where
  subscribing absorbed : Mode A
  resuming : Tag → Mode A
  rising   : Ev A → Mode A

record Conf (R : Set) : Set₁ where
  constructor ⟨_,_,_,_,_⟩
  field
    {Γ}  : List Set
    {A}  : Set
    ctx  : Ctx R Γ A
    foc  : St Γ A
    mode : Mode A
    pos  : Pos
    rets : List Job

-- What the root is shown, and where.
Shown : Set → Set
Shown R = List (Pos × Ev R)

-- A step taken, what it showed and the colds it tore down; or a cold
-- subscribed, the run stopped until the runtime hands back its state.
data Stepped (R : Set) : Set₁ where
  moved    : Conf R → Shown R → Torn → Stepped R
  starting : ∀ {A} → C A → Pos → (L A → Conf R) → Stepped R

private
  ok : ∀ {R} → Conf R → Stepped R
  ok k = moved k [] []

_⊕_ : Pos → Pos → Pos
p ⊕ q = p ++ q

-- The joiners, by path from the root, at the binder in `c`.
rooted : ∀ {R Γ A} → Ctx R Γ A → List (List ℕ × Pos) → List (List ℕ × Pos)
rooted c []             = []
rooted c ((q , j) ∷ js) = (dirs c ++ q , j) ∷ rooted c js

drop₁ : ∀ {X : Set} → List X → List X
drop₁ []       = []
drop₁ (_ ∷ xs) = xs

begin : ∀ {R Γ A} → Ctx R Γ A → Obs C Γ A → Pos → List Job → Stepped R
begin c (cold x)          p rs = starting x p λ l → ⟨ c , coldS true l , absorbed , p , rs ⟩
begin c empty             p rs = ok ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩
begin c (of xs)           p rs = ok ⟨ c , ofS xs , resuming (next 0) , p , rs ⟩
begin c (map f s)         p rs = ok ⟨ inMap f c , pend s , subscribing , p , rs ⟩
begin c (scan f z s)      p rs = ok ⟨ inScan f z c , pend s , subscribing , p , rs ⟩
begin c (takeWhile i q s) p rs = let c′ = inTake i q c in
  ok ⟨ inCut true false c′ , pend s , subscribing , p , (dirs c′ ++ [ 0 ] , att , p) ∷ rs ⟩
begin c (flatMap op f s)  p rs = let c′ = inOuter op f false 0 [] [] c in
  ok ⟨ inCut true false c′ , pend s , subscribing , p , (dirs c′ ++ [ 0 ] , att , p) ∷ rs ⟩
-- the body under `ix 0`; its source, once the body's subscription
-- exists, under `ix 1`
begin c (connect s b)     p rs =
  ok ⟨ inBody (cs false [] [] false true false) (pend s) c , pend b , subscribing , p ⊕ [ ix 0 ] , (dirs c , attBody , p) ∷ rs ⟩
-- a joiner keeps where it joined; a completed subject completes it under `last`
begin c (connected x)     p rs with joinUp p c x []
... | true  , c′ = ok ⟨ c′ , doneS , rising cp , p ⊕ [ last ] , rs ⟩
... | false , c′ = ok ⟨ c′ , joinS p true x , absorbed , p , rs ⟩
-- a defer's body one level down
begin c (defer l)         p rs = ok ⟨ c , pend (Later.force l) , subscribing , p ⊕ [ ix 1 ] , rs ⟩

-- A lane begun under `ix 1`, unless the flatMap's own observer is closed.
start : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → A → Pos → List Job → Conf R
start c op f d n q o ls a p rs with closed c
... | true  = ⟨ c , flatS op f d n q o ls , absorbed , p , rs ⟩
... | false = let c′ = inLn true (inLanes op f d (suc n) q o ls [] c) in
  ⟨ inCut true false c′ , pend (f a) , subscribing , p ⊕ [ ix 1 ] , (dirs c′ ++ [ 0 ] , att , p ⊕ [ ix 1 ]) ∷ rs ⟩

-- The outer done, no lane running and, `e`, none waiting: complete.
settle : ∀ {B} → Bool → ℕ → Bool → Mode B
settle d n e = if d ∧ (n ≡ᵇ 0) ∧ e then rising cp else absorbed

-- A slot freed: the next waiting value's lane begun, else settle.
dequeue : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → Pos → List Job → Conf R
dequeue c op f d n []      o ls p rs = ⟨ c , flatS op f d n [] o ls , settle d n true , p , rs ⟩
dequeue c op f d n (a ∷ q) o ls p rs = start c op f d n q o ls a p rs

admit : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs C Γ B) → Bool → ℕ → List A → St Γ A → List (St Γ B) → A → Pos → List Job → Stepped R
admit c (mergeᶠ nothing)  f d n q o ls a p rs = ok (start c (mergeᶠ nothing) f d n q o ls a p rs)
admit c (mergeᶠ (just m)) f d n q o ls a p rs =
  ok (if n <ᵇ m then start c (mergeᶠ (just m)) f d n q o ls a p rs
      else ⟨ c , flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls , absorbed , p , rs ⟩)
admit c switchᶠ           f d n q o ls a p rs with killAll ls
... | ls′ , t = moved (start c switchᶠ f d 0 q o ls′ a p rs) [] t
admit c exhaustᶠ          f d n q o ls a p rs with n ≡ᵇ 0
... | true  = ok (start c exhaustᶠ f d n q o ls a p rs)
... | false = ok ⟨ c , flatS exhaustᶠ f d n q o ls , absorbed , p , rs ⟩

ended : ∀ {Γ B} → St Γ B → St Γ B
ended (lnS b (cutS l a s)) = lnS b (cutS false a s)
ended s                    = s

-- A rise moves no position, except a takeWhile's own failing value and
-- completion, under `ix 0` and `last`.
rise : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Ev A → Pos → List Job → Stepped R
rise top s e p rs = moved ⟨ top , s , absorbed , p , rs ⟩ [ (p , e) ] []
rise (inMap f c) s e p rs = ok ⟨ c , mapS f s , rising (mapEv f e) , p , rs ⟩
rise (inScan f z c) s (nx a) p rs = ok ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p , rs ⟩
rise (inScan f z c) s cp     p rs = ok ⟨ c , scanS f z s , rising cp , p , rs ⟩
rise (inCut l a c) s e p rs = ok ⟨ c , cutS l a s , (if l then rising e else absorbed) , p , rs ⟩
rise (inLn b c) s e p rs = ok ⟨ c , lnS b s , rising e , p , rs ⟩
rise (inTake i q c) s (nx a) p rs with q a | i
... | true  | _     = ok ⟨ c , takeS i q s , rising (nx a) , p , rs ⟩
... | false | true  = ok ⟨ c , takeS i q s , rising (nx a) , p ⊕ [ ix 0 ] , (dirs c , owedCp , p) ∷ rs ⟩
... | false | false = ok ⟨ c , takeS i q s , rising cp , p ⊕ [ last ] , (dirs c , owedCut , p) ∷ rs ⟩
rise (inTake i q c) s cp p rs = ok ⟨ c , takeS i q s , rising cp , p , rs ⟩
rise (inOuter op f d n q ls c) o (nx a) p rs = admit c op f d n q o ls a p rs
rise (inOuter op f d n q ls c) o cp     p rs = ok ⟨ c , flatS op f true n q o ls , settle true n (null q) , p , rs ⟩
rise (inLanes op f d n q o pre post c) s (nx b) p rs = ok ⟨ c , flatS op f d n q o (pre ++ s ∷ post) , rising (nx b) , p , rs ⟩
rise (inLanes op f d n q o pre post c) s cp     p rs = ok (dequeue c op f d (pred n) q o (pre ++ ended s ∷ post) p rs)
rise (inSrc k b c) s (nx a) p rs = ok ⟨ c , connS (record k { feeds = nx a ∷ CS.feeds k }) s b , resuming (feeding (rooted c (CS.subs k))) , p , rs ⟩
rise (inSrc k b c) s cp     p rs = ok ⟨ c , connS (record k { closed = true ; feeds = cp ∷ CS.feeds k }) s b , resuming (feeding (rooted c (CS.subs k))) , p , rs ⟩
rise (inBody k o c) s (nx b) p rs = ok ⟨ c , connS k o s , rising (nx b) , p , rs ⟩
rise (inBody k o c) s cp     p rs = ok ⟨ c , connS k o s , rising cp , p , (dirs c , owed , p) ∷ rs ⟩

-- A connect's next feed: each joiner fed under `sub` of where it joined;
-- the last fed, the value is done.
feedOn : ∀ {R Γ X B} → Ctx R Γ B → CS X → St Γ X → St (X ∷ Γ) B → List (List ℕ × Pos) → Pos → List Job → Conf R
feedOn c k o b [] p rs = ⟨ c , connS (record k { feeds = drop₁ (CS.feeds k) }) o b , absorbed , p , rs ⟩
feedOn c k o b ((q , j) ∷ js) p rs with downs q top (plug c (connS k o b))
... | just (_ , _ , c′ , s′) = ⟨ c′ , s′ , resuming go , p ⊕ [ subᴾ j ] , (dirs c , feeding js , p) ∷ rs ⟩
... | nothing                = ⟨ c , connS k o b , absorbed , p , rs ⟩

-- Which job a node and a tag make: every pairing the machine resumes,
-- and the rest idle.
data Res {Γ : List Set} {A : Set} : St Γ A → Tag → Set₁ where
  ofR   : ∀ xs i → Res (ofS xs) (next i)
  attR  : ∀ l a s → Res (cutS l a s) att
  cpR   : ∀ i q s → Res (takeS i q s) owedCp
  cutR  : ∀ i q s → Res (takeS i q s) owedCut
  feedR : ∀ {X} k (o : St Γ X) b js → Res (connS k o b) (feeding js)
  bodyR : ∀ {X} k (o : St Γ X) b → Res (connS k o b) attBody
  srcR  : ∀ {X} k (o : St Γ X) b → Res (connS k o b) att
  endR  : ∀ {X} k (o : St Γ X) b → Res (connS k o b) owed
  joinR : ∀ j x → Res (joinS j true x) go
  idle  : ∀ {s t} → Res s t

res : ∀ {Γ A} (s : St Γ A) t → Res s t
res (ofS xs)         (next i)     = ofR xs i
res (cutS l a s)     att          = attR l a s
res (takeS i q s)    owedCp       = cpR i q s
res (takeS i q s)    owedCut      = cutR i q s
res (connS k o b)    (feeding js) = feedR k o b js
res (connS k o b)    attBody      = bodyR k o b
res (connS k o b)    att          = srcR k o b
res (connS k o b)    owed         = endR k o b
res (joinS j true x) go           = joinR j x
res s                t            = idle

-- Unsubscribed or left as it is.
unsubIf : ∀ {Γ A} → Bool → St Γ A → St Γ A × Torn
unsubIf true  s = unsub s
unsubIf false s = s , []

resumeR : ∀ {R Γ A} {s : St Γ A} {t} → Ctx R Γ A → Res s t → Pos → List Job → Stepped R
-- the i-th value under `ix i`, the completion under `last`, of where the of was subscribed
resumeR c (ofR xs i) p rs with closed c | xs
... | true  | _       = ok ⟨ c , doneS , absorbed , p , rs ⟩
... | false | []      = ok ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩
... | false | x ∷ xs′ = ok ⟨ c , ofS xs′ , rising (nx x) , p ⊕ [ ix i ] , (dirs c , next (suc i) , p) ∷ rs ⟩
resumeR c (attR l a s) p rs with unsubIf (not l) s
... | s′ , t = moved ⟨ c , cutS l true s′ , absorbed , p , rs ⟩ [] t
resumeR c (cpR i q s)  p rs = ok ⟨ c , takeS i q s , rising cp , p ⊕ [ last ] , (dirs c , owedCut , p) ∷ rs ⟩
resumeR c (cutR i q s) p rs with cut s
... | s′ , t = moved ⟨ c , takeS i q s′ , absorbed , p , rs ⟩ [] t
resumeR c (feedR k o b js) p rs = ok (feedOn c k o b js p rs)
resumeR c (bodyR k o b) p rs =
  ok ⟨ inSrc (record k { bodyAtt = true }) b c , o , subscribing , p ⊕ [ ix 1 ] , (dirs c , att , p ⊕ [ ix 1 ]) ∷ rs ⟩
resumeR c (srcR k o b) p rs with unsubIf (not (CS.srcLive k)) o
... | o′ , t = moved ⟨ c , connS (record k { srcAtt = true }) o′ b , absorbed , p , rs ⟩ [] t
resumeR c (endR k o b) p rs with unsubIf (CS.srcAtt k) o
... | o′ , t = moved ⟨ c , connS (record k { srcLive = false }) o′ b , absorbed , p , rs ⟩ [] t
resumeR c (joinR j x) p rs with fedUp c x
... | just e  = ok ⟨ c , joinS j true x , rising e , p , rs ⟩
... | nothing = ok ⟨ c , joinS j true x , absorbed , p , rs ⟩
resumeR {s = s} c idle p rs = ok ⟨ c , s , absorbed , p , rs ⟩

resume : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Tag → Pos → List Job → Stepped R
resume c s t = resumeR c (res s t)

-- By the mode first, so a fact about a step splits on the mode alone.
stepAt : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Mode A → Pos → List Job → Stepped R
stepAt c s (resuming t) p rs = resume c s t p rs
stepAt c s (rising e)   p rs = rise c s e p rs
stepAt c (pend o) subscribing p rs = begin c o p rs
stepAt c s subscribing p rs = ok ⟨ c , s , subscribing , p , rs ⟩
-- a job resumed where it was suspended
stepAt c s absorbed p ((q , t , p′) ∷ rs) with downs q top (plug c s)
... | just (_ , _ , c′ , s′) = ok ⟨ c′ , s′ , resuming t , p′ , rs ⟩
... | nothing                = ok ⟨ c , s , absorbed , p , rs ⟩
stepAt c s absorbed p [] = ok ⟨ c , s , absorbed , p , [] ⟩

step : ∀ {R} → Conf R → Stepped R
step ⟨ c , s , m , p , rs ⟩ = stepAt c s m p rs

-- The root subscribed.
load : ∀ {R} → Obs C [] R → Conf R
load o = ⟨ top , pend o , subscribing , root , [] ⟩

------------------------------------------------------------------------
-- What a runtime reads and does

-- Where the focus is, from the root.
spot : ∀ {R} → Conf R → List ℕ
spot k = dirs (Conf.ctx k)

-- Everything running now absorbed: the runtime's turn, once the jobs
-- owed above what it is playing are done.
calm : ∀ {R} → Conf R → Bool
calm k with Conf.mode k
... | absorbed = true
... | _        = false

-- How many jobs are owed.
depth : ∀ {R} → Conf R → ℕ
depth k = length (Conf.rets k)

-- A started cold, found by its path: whether it is live; its state;
-- whether its observer is closed; a delivery into it at a position,
-- with its state after; its state replaced, nothing delivered.
data Poke (R : Set) : Set₁ where
  gone : Poke R
  leaf : ∀ {A} → Bool → L A → Bool → (Ev A → L A → Bool → Pos → Conf R) → (L A → Conf R) → Poke R

poke : ∀ {R} → List ℕ → Conf R → Poke R
poke π ⟨ c , s , m , p , rs ⟩ with downs π top (plug c s)
... | just (_ , _ , c′ , coldS b l) =
  leaf b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , rising e , p′ , rs ⟩) (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p , rs ⟩)
... | _ = gone
