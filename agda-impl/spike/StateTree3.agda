{-# OPTIONS --guardedness #-}

-- SPIKE 3: spike 2's machine with the POSITION GHOST.  Today's kernels
-- place by scope (`under l m k`); here a job saves the position it was
-- suspended at and gets it back when resumed, and a node that places its
-- own emissions (an `of`, a joiner) keeps where it was subscribed, as
-- `adequacy.Strong`'s `Sub` already does.
--
-- SPIKE 2: the state-tree machine over the real `Tree.Obs`, for every
-- former but `cold` and a bounded merge: of, empty, map, scan,
-- takeWhile, flatMap (unbounded merge, switch, exhaust), connect,
-- connected, defer.  Each kernel of `operation.AbstractObservable`
-- mirrored node for node; no heap, no worlds, no names.
--
-- Control is a typed zipper.  A subscription begins by moving the focus
-- down; a value rises by moving it up; a job owed later (an `of`'s next
-- value, a subscription's attach, a takeWhile's completion, a connect's
-- feed) is a PATH from the root and a tag, resumed once what runs now is
-- absorbed.  A join is reached from its subject by a path RELATIVE to
-- the binder, and reads the value it is fed from the binder above it in
-- its own context, where the types line up by the de Bruijn index.
module spike.StateTree3 where

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline; Pos; ix; last; root) renaming (sub to subᴾ)

PObs : List Set → Set → Set₁
PObs = Obs Timeline

data Ev (A : Set) : Set where
  nx : A → Ev A
  cp : Ev A

mapEv : ∀ {A B} → (A → B) → Ev A → Ev B
mapEv f (nx a) = nx (f a)
mapEv f cp     = cp

------------------------------------------------------------------------
-- States

-- A takeWhile's own progress: running; its failing value out, its
-- completion owed; its completion out, its cut owed.
data Ph : Set where
  running oweCp oweCut : Ph

-- A connect's subject and its source's switch.  `feeds` is a STACK: a
-- value fed while another feed is under way is fed first, as the
-- kernel's nested `each` would.
record CS (X : Set) : Set where
  constructor cs
  field
    closed  : Bool
    subs    : List (List ℕ × Pos)               -- each joiner, by its path from the binder, and where it joined
    feeds   : List (Ev X × List (List ℕ × Pos)) -- what is being fed, to whom still
    bodyAtt : Bool
    srcLive : Bool
    srcAtt  : Bool

data St (Γ : List Set) : Set → Set₁ where
  pend  : ∀ {A} → PObs Γ A → St Γ A
  -- subscribed at p, i emitted
  ofS   : ∀ {A} → Pos → ℕ → List A → St Γ A
  doneS : ∀ {A} → St Γ A
  mapS  : ∀ {A B} → (A → B) → St Γ A → St Γ B
  scanS : ∀ {A B} → (B → A → B) → B → St Γ A → St Γ B
  -- a kill switch: live, attached
  cutS  : ∀ {A} → Bool → Bool → St Γ A → St Γ A
  -- a lane, still in its flatMap's list
  lnS   : ∀ {A} → Bool → St Γ A → St Γ A
  -- the child is its source's switch
  takeS : ∀ {A} → Bool → (A → Bool) → Ph → St Γ A → St Γ A
  -- outer done, lanes running, the outer's switch, every lane begun (oldest first)
  flatS : ∀ {A B} → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → St Γ B
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
  inTake  : ∀ {Γ A} → Bool → (A → Bool) → Ph → Ctx R Γ A → Ctx R Γ A
  inOuter : ∀ {Γ A B} → FlatOp → (A → PObs Γ B) → Bool → ℕ → List (St Γ B) → Ctx R Γ B → Ctx R Γ A
  inLanes : ∀ {Γ A B} → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → List (St Γ B) → Ctx R Γ B → Ctx R Γ B
  inSrc   : ∀ {Γ X B} → CS X → St (X ∷ Γ) B → Ctx R Γ B → Ctx R Γ X
  inBody  : ∀ {Γ X B} → CS X → St Γ X → Ctx R Γ B → Ctx R (X ∷ Γ) B

plug : ∀ {R Γ A} → Ctx R Γ A → St Γ A → St [] R
plug top                             s = s
plug (inMap f c)                     s = plug c (mapS f s)
plug (inScan f z c)                  s = plug c (scanS f z s)
plug (inCut l a c)                   s = plug c (cutS l a s)
plug (inLn b c)                      s = plug c (lnS b s)
plug (inTake i p ph c)               s = plug c (takeS i p ph s)
plug (inOuter op f d n ls c)         s = plug c (flatS op f d n s ls)
plug (inLanes op f d n o pre post c) s = plug c (flatS op f d n o (pre ++ s ∷ post))
plug (inSrc k b c)                   s = plug c (connS k s b)
plug (inBody k o c)                  s = plug c (connS k o s)

-- The child index of the hole in its parent.
dir : ∀ {R Γ A} → Ctx R Γ A → ℕ
dir (inLanes op f d n o pre post c) = suc (length pre)
dir (inBody k o c)                  = 1
dir _                               = 0

dirs : ∀ {R Γ A} → Ctx R Γ A → List ℕ
dirs top                             = []
dirs c@(inMap f c′)                  = dirs c′ ++ [ dir c ]
dirs c@(inScan f z c′)               = dirs c′ ++ [ dir c ]
dirs c@(inCut l a c′)                = dirs c′ ++ [ dir c ]
dirs c@(inLn b c′)                   = dirs c′ ++ [ dir c ]
dirs c@(inTake i p ph c′)            = dirs c′ ++ [ dir c ]
dirs c@(inOuter op f d n ls c′)      = dirs c′ ++ [ dir c ]
dirs c@(inLanes op f d n o pre post c′) = dirs c′ ++ [ dir c ]
dirs c@(inSrc k b c′)                = dirs c′ ++ [ dir c ]
dirs c@(inBody k o c′)               = dirs c′ ++ [ dir c ]

-- What the hole's observer answers when polled: rxjs's `closed`.  A
-- switch off answers true; a connect's source asks its subject.
closed : ∀ {R Γ A} → Ctx R Γ A → Bool
closed top                             = false
closed (inMap f c)                     = closed c
closed (inScan f z c)                  = closed c
closed (inCut l a c)                   = not l ∨ closed c
closed (inLn b c)                      = closed c
closed (inTake i p ph c)               = closed c
closed (inOuter op f d n ls c)         = closed c
closed (inLanes op f d n o pre post c) = closed c
closed (inSrc k b c)                   = CS.closed k
closed (inBody k o c)                  = closed c

------------------------------------------------------------------------
-- Unsubscribing, node by node, as `adequacy.Strong`'s `unsub` reads
-- each kernel's subscription.  A switch cut before its subscription is
-- attached defers the unsubscribe to the attach, as `Kit.attach` does.

mutual
  unsub : ∀ {Γ A} → St Γ A → St Γ A
  unsub (mapS f s)             = mapS f (unsub s)
  unsub (scanS f z s)          = scanS f z (unsub s)
  unsub (takeS i p ph s)       = takeS i p ph (cut s)
  unsub (flatS op f d n o ls)  = flatS op f d 0 (cut o) (killAll ls)
  unsub (connS k o b)          = connS k (unsub o) (unsub b)
  unsub (joinS j g x)          = joinS j false x
  unsub s                      = s

  cut : ∀ {Γ A} → St Γ A → St Γ A
  cut (cutS l true s)  = cutS false true (unsub s)
  cut (cutS l false s) = cutS false false s
  cut s                = s

  killAll : ∀ {Γ B} → List (St Γ B) → List (St Γ B)
  killAll []                = []
  killAll (lnS true s ∷ ls) = lnS false (cut s) ∷ killAll ls
  killAll (l ∷ ls)          = l ∷ killAll ls

------------------------------------------------------------------------
-- Moving the focus

Focus : Set → Set₁
Focus R = Σ (List Set) λ Γ → Σ Set λ A → Ctx R Γ A × St Γ A

pickL : ∀ {Γ B} → ℕ → List (St Γ B) → List (St Γ B) → Maybe (List (St Γ B) × St Γ B × List (St Γ B))
pickL i       pre []         = nothing
pickL zero    pre (s ∷ post) = just (pre , s , post)
pickL (suc i) pre (s ∷ post) = pickL i (pre ++ [ s ]) post

down : ∀ {R Γ A} → ℕ → Ctx R Γ A → St Γ A → Maybe (Focus R)
down zero          c (mapS f s)            = just (_ , _ , inMap f c , s)
down zero          c (scanS f z s)         = just (_ , _ , inScan f z c , s)
down zero          c (cutS l a s)          = just (_ , _ , inCut l a c , s)
down zero          c (lnS b s)             = just (_ , _ , inLn b c , s)
down zero          c (takeS i p ph s)      = just (_ , _ , inTake i p ph c , s)
down zero          c (flatS op f d n o ls) = just (_ , _ , inOuter op f d n ls c , o)
down zero          c (connS k o b)         = just (_ , _ , inSrc k b c , o)
down (suc zero)    c (connS k o b)         = just (_ , _ , inBody k o c , b)
down (suc i)       c (flatS op f d n o ls) with pickL i [] ls
... | just (pre , s , post) = just (_ , _ , inLanes op f d n o pre post c , s)
... | nothing               = nothing
down _             c _                     = nothing

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
joinUp j c@(inTake i p ph c′)          x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inTake i p ph c″
joinUp j c@(inOuter op f d n ls c′)    x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inOuter op f d n ls c″
joinUp j c@(inLanes op f d n o pre post c′) x    acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inLanes op f d n o pre post c″
joinUp j c@(inSrc k b′ c′)             x         acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inSrc k b′ c″
joinUp j (inBody k o c′)               (here refl) acc with CS.closed k
... | true  = true , inBody k o c′
... | false = false , inBody (record k { subs = CS.subs k ++ [ (1 ∷ acc , j) ] }) o c′
joinUp j c@(inBody k o c′)             (there x) acc with joinUp j c′ x (dir c ∷ acc)
... | b , c″ = b , inBody k o c″

-- What the binder is feeding now.
fedUp : ∀ {R Γ A X} → Ctx R Γ A → X ∈ Γ → Maybe (Ev X)
fedUp top                             ()
fedUp (inMap f c)                     x = fedUp c x
fedUp (inScan f z c)                  x = fedUp c x
fedUp (inCut l a c)                   x = fedUp c x
fedUp (inLn b c)                      x = fedUp c x
fedUp (inTake i p ph c)               x = fedUp c x
fedUp (inOuter op f d n ls c)         x = fedUp c x
fedUp (inLanes op f d n o pre post c) x = fedUp c x
fedUp (inSrc k b c)                   x = fedUp c x
fedUp (inBody k o c)          (here refl) with CS.feeds k
... | (e , _) ∷ _ = just e
... | []          = nothing
fedUp (inBody k o c)          (there x) = fedUp c x

------------------------------------------------------------------------
-- The machine

-- What a resumed job is: the node's own burst or feed; the attach of
-- its child's subscription (a connect's body, then its source); what a
-- completion left owed.
data Tag : Set where
  go att attBody owed : Tag

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
    pos  : Pos          -- where the run is: a ghost nothing branches on
    rets : List Job

-- What the root is shown, and where.
Shown : Set → Set
Shown R = List (Pos × Ev R)

_⊕_ : Pos → Pos → Pos
p ⊕ q = p ++ q

begin : ∀ {R Γ A} → Ctx R Γ A → PObs Γ A → Pos → List Job → Conf R
begin c (cold _)          p rs = ⟨ c , doneS , absorbed , p , rs ⟩      -- not in the spike
begin c empty             p rs = ⟨ c , doneS , rising cp , p ⊕ [ last ] , rs ⟩
begin c (of xs)           p rs = ⟨ c , ofS p 0 xs , resuming go , p , rs ⟩
begin c (map f s)         p rs = ⟨ inMap f c , pend s , subscribing , p , rs ⟩
begin c (scan f z s)      p rs = ⟨ inScan f z c , pend s , subscribing , p , rs ⟩
begin c (takeWhile i q s) p rs = let c′ = inTake i q running c in
  ⟨ inCut true false c′ , pend s , subscribing , p , (dirs c′ ++ [ 0 ] , att , p) ∷ rs ⟩
begin c (flatMap op f s)  p rs = let c′ = inOuter op f false 0 [] c in
  ⟨ inCut true false c′ , pend s , subscribing , p , (dirs c′ ++ [ 0 ] , att , p) ∷ rs ⟩
-- the body under `ix 0`; its source, once the body's subscription
-- exists, under `ix 1`
begin c (connect s b)     p rs =
  ⟨ inBody (cs false [] [] false true false) (pend s) c , pend b , subscribing , p ⊕ [ ix 0 ] , (dirs c , attBody , p) ∷ rs ⟩
-- a joiner keeps where it joined; a completed subject completes it under `last`
begin c (connected x)     p rs with joinUp p c x []
... | true  , c′ = ⟨ c′ , doneS , rising cp , p ⊕ [ last ] , rs ⟩
... | false , c′ = ⟨ c′ , joinS p true x , absorbed , p , rs ⟩
-- a defer's body one level down
begin c (defer l)         p rs = ⟨ c , pend (Later.force l) , subscribing , p ⊕ [ ix 1 ] , rs ⟩

-- A lane begun under `ix 1`, unless the flatMap's own observer is closed.
start : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → A → Pos → List Job → Conf R
start c op f d n o ls a p rs with closed c
... | true  = ⟨ c , flatS op f d n o ls , absorbed , p , rs ⟩
... | false = let c′ = inLn true (inLanes op f d (suc n) o ls [] c) in
  ⟨ inCut true false c′ , pend (f a) , subscribing , p ⊕ [ ix 1 ] , (dirs c′ ++ [ 0 ] , att , p ⊕ [ ix 1 ]) ∷ rs ⟩

settle : ∀ {B} → Bool → ℕ → Mode B
settle d n = if d ∧ (n ≡ᵇ 0) then rising cp else absorbed

admit : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → A → Pos → List Job → Conf R
admit c (mergeᶠ nothing)  f d n o ls a p rs = start c (mergeᶠ nothing) f d n o ls a p rs
admit c (mergeᶠ (just m)) f d n o ls a p rs = ⟨ c , flatS (mergeᶠ (just m)) f d n o ls , absorbed , p , rs ⟩
admit c switchᶠ           f d n o ls a p rs = start c switchᶠ f d 0 o (killAll ls) a p rs
admit c exhaustᶠ          f d n o ls a p rs with n ≡ᵇ 0
... | true  = start c exhaustᶠ f d n o ls a p rs
... | false = ⟨ c , flatS exhaustᶠ f d n o ls , absorbed , p , rs ⟩

ended : ∀ {Γ B} → St Γ B → St Γ B
ended (lnS b (cutS l a s)) = lnS b (cutS false a s)
ended s                    = s

-- A rise moves no position, except a takeWhile's own failing value and
-- completion, under `ix 0` and `last`.
rise : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Ev A → Pos → List Job → Conf R × Shown R
rise top s e p rs = ⟨ top , s , absorbed , p , rs ⟩ , [ (p , e) ]
rise (inMap f c) s e p rs = ⟨ c , mapS f s , rising (mapEv f e) , p , rs ⟩ , []
rise (inScan f z c) s (nx a) p rs = ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p , rs ⟩ , []
rise (inScan f z c) s cp     p rs = ⟨ c , scanS f z s , rising cp , p , rs ⟩ , []
rise (inCut l a c) s e p rs = ⟨ c , cutS l a s , (if l then rising e else absorbed) , p , rs ⟩ , []
rise (inLn b c) s e p rs = ⟨ c , lnS b s , rising e , p , rs ⟩ , []
rise (inTake i q ph c) s (nx a) p rs with q a | i
... | true  | _     = ⟨ c , takeS i q ph s , rising (nx a) , p , rs ⟩ , []
... | false | true  = ⟨ c , takeS i q oweCp s , rising (nx a) , p ⊕ [ ix 0 ] , (dirs c , owed , p) ∷ rs ⟩ , []
... | false | false = ⟨ c , takeS i q oweCut s , rising cp , p ⊕ [ last ] , (dirs c , owed , p) ∷ rs ⟩ , []
rise (inTake i q ph c) s cp p rs = ⟨ c , takeS i q ph s , rising cp , p , rs ⟩ , []
rise (inOuter op f d n ls c) o (nx a) p rs = admit c op f d n o ls a p rs , []
rise (inOuter op f d n ls c) o cp     p rs = ⟨ c , flatS op f true n o ls , settle true n , p , rs ⟩ , []
rise (inLanes op f d n o pre post c) s (nx b) p rs = ⟨ c , flatS op f d n o (pre ++ s ∷ post) , rising (nx b) , p , rs ⟩ , []
rise (inLanes op f d n o pre post c) s cp     p rs = ⟨ c , flatS op f d (pred n) o (pre ++ ended s ∷ post) , settle d (pred n) , p , rs ⟩ , []
rise (inSrc k b c) s (nx a) p rs = ⟨ c , connS (record k { feeds = (nx a , CS.subs k) ∷ CS.feeds k }) s b , resuming go , p , rs ⟩ , []
rise (inSrc k b c) s cp     p rs = ⟨ c , connS (record k { closed = true ; feeds = (cp , CS.subs k) ∷ CS.feeds k }) s b , resuming go , p , rs ⟩ , []
rise (inBody k o c) s (nx b) p rs = ⟨ c , connS k o s , rising (nx b) , p , rs ⟩ , []
rise (inBody k o c) s cp     p rs = ⟨ c , connS k o s , rising cp , p , (dirs c , owed , p) ∷ rs ⟩ , []

-- A connect's next feed: each joiner fed under `sub` of where it joined.
feedOn : ∀ {R Γ X B} → Ctx R Γ B → CS X → St Γ X → St (X ∷ Γ) B → Pos → List Job → Conf R
feedOn c k o b p rs with CS.feeds k
... | [] = ⟨ c , connS k o b , absorbed , p , rs ⟩
... | (e , []) ∷ fs = ⟨ c , connS (record k { feeds = fs }) o b , absorbed , p , rs ⟩
... | (e , (q , j) ∷ ps) ∷ fs with downs q c (connS (record k { feeds = (e , ps) ∷ fs }) o b)
...   | just (_ , _ , c′ , s′) = ⟨ c′ , s′ , resuming go , p ⊕ [ subᴾ j ] , (dirs c , go , p) ∷ rs ⟩
...   | nothing                = ⟨ c , connS (record k { feeds = (e , ps) ∷ fs }) o b , absorbed , p , rs ⟩

resume : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Tag → Pos → List Job → Conf R
-- the i-th value under `ix i`, the completion under `last`, of where the of was subscribed
resume c (ofS q i xs) go p rs with closed c | xs
... | true  | _       = ⟨ c , doneS , absorbed , p , rs ⟩
... | false | []      = ⟨ c , doneS , rising cp , q ⊕ [ last ] , rs ⟩
... | false | x ∷ xs′ = ⟨ c , ofS q (suc i) xs′ , rising (nx x) , q ⊕ [ ix i ] , (dirs c , go , p) ∷ rs ⟩
resume c (cutS l a s) att p rs = ⟨ c , cutS l true (if l then s else unsub s) , absorbed , p , rs ⟩
resume c (takeS i q oweCp s) owed p rs = ⟨ c , takeS i q oweCut s , rising cp , p ⊕ [ last ] , (dirs c , owed , p) ∷ rs ⟩
resume c (takeS i q oweCut s) owed p rs = ⟨ c , takeS i q running (cut s) , absorbed , p , rs ⟩
resume c (connS k o b) go p rs = feedOn c k o b p rs
resume c (connS k o b) attBody p rs =
  ⟨ inSrc (record k { bodyAtt = true }) b c , o , subscribing , p ⊕ [ ix 1 ] , (dirs c , att , p ⊕ [ ix 1 ]) ∷ rs ⟩
resume c (connS k o b) att p rs =
  ⟨ c , connS (record k { srcAtt = true }) (if CS.srcLive k then o else unsub o) b , absorbed , p , rs ⟩
resume c (connS k o b) owed p rs =
  ⟨ c , connS (record k { srcLive = false }) (if CS.srcAtt k then unsub o else o) b , absorbed , p , rs ⟩
resume c (joinS j true x) go p rs with fedUp c x
... | just e  = ⟨ c , joinS j true x , rising e , p , rs ⟩
... | nothing = ⟨ c , joinS j true x , absorbed , p , rs ⟩
resume c s _ p rs = ⟨ c , s , absorbed , p , rs ⟩

step : ∀ {R} → Conf R → Conf R × Shown R
step ⟨ c , pend o , subscribing , p , rs ⟩ = begin c o p rs , []
step ⟨ c , s , resuming t , p , rs ⟩       = resume c s t p rs , []
step ⟨ c , s , rising e , p , rs ⟩         = rise c s e p rs
-- a job resumed where it was suspended
step ⟨ c , s , absorbed , p , (q , t , p′) ∷ rs ⟩ with downs q top (plug c s)
... | just (_ , _ , c′ , s′) = ⟨ c′ , s′ , resuming t , p′ , rs ⟩ , []
... | nothing                = ⟨ c , s , absorbed , p , rs ⟩ , []
step k = k , []

load : ∀ {R} → PObs [] R → Conf R
load o = ⟨ top , pend o , subscribing , root , [] ⟩

-- The root's record, which ends at its completion.
runN : ∀ {R} → ℕ → Conf R → Shown R
runN zero    k = []
runN (suc n) k with step k
... | k′ , [] = runN n k′
... | k′ , (p , cp) ∷ _ = [ (p , cp) ]
... | k′ , (p , nx a) ∷ _ = (p , nx a) ∷ runN n k′
