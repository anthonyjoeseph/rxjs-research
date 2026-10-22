{-# OPTIONS --guardedness #-}

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
module spike.StateTree2 where

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline)

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
    subs    : List (List ℕ)                  -- each joiner, by its path from the binder
    feeds   : List (Ev X × List (List ℕ))    -- what is being fed, to whom still
    bodyAtt : Bool
    srcLive : Bool
    srcAtt  : Bool

data St (Γ : List Set) : Set → Set₁ where
  pend  : ∀ {A} → PObs Γ A → St Γ A
  ofS   : ∀ {A} → List A → St Γ A
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
  joinS : ∀ {A} → Bool → A ∈ Γ → St Γ A

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
  unsub (joinS g x)            = joinS false x
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
joinUp : ∀ {R Γ A X} → Ctx R Γ A → X ∈ Γ → List ℕ → Bool × Ctx R Γ A
joinUp top                           ()        acc
joinUp c@(inMap f c′)                x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inMap f c″
joinUp c@(inScan f z c′)             x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inScan f z c″
joinUp c@(inCut l a c′)              x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inCut l a c″
joinUp c@(inLn l c′)                 x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inLn l c″
joinUp c@(inTake i p ph c′)          x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inTake i p ph c″
joinUp c@(inOuter op f d n ls c′)    x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inOuter op f d n ls c″
joinUp c@(inLanes op f d n o pre post c′) x    acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inLanes op f d n o pre post c″
joinUp c@(inSrc k b′ c′)             x         acc with joinUp c′ x (dir c ∷ acc)
... | b , c″ = b , inSrc k b′ c″
joinUp (inBody k o c′)               (here refl) acc with CS.closed k
... | true  = true , inBody k o c′
... | false = false , inBody (record k { subs = CS.subs k ++ [ 1 ∷ acc ] }) o c′
joinUp c@(inBody k o c′)             (there x) acc with joinUp c′ x (dir c ∷ acc)
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

data Mode (A : Set) : Set where
  subscribing absorbed : Mode A
  resuming : Tag → Mode A
  rising   : Ev A → Mode A

record Conf (R : Set) : Set₁ where
  constructor ⟨_,_,_,_⟩
  field
    {Γ}  : List Set
    {A}  : Set
    ctx  : Ctx R Γ A
    foc  : St Γ A
    mode : Mode A
    rets : List (List ℕ × Tag)

begin : ∀ {R Γ A} → Ctx R Γ A → PObs Γ A → List (List ℕ × Tag) → Conf R
begin c (cold _)          rs = ⟨ c , doneS , absorbed , rs ⟩      -- not in the spike
begin c empty             rs = ⟨ c , doneS , rising cp , rs ⟩
begin c (of xs)           rs = ⟨ c , ofS xs , resuming go , rs ⟩
begin c (map f s)         rs = ⟨ inMap f c , pend s , subscribing , rs ⟩
begin c (scan f z s)      rs = ⟨ inScan f z c , pend s , subscribing , rs ⟩
begin c (takeWhile i p s) rs = let c′ = inTake i p running c in
  ⟨ inCut true false c′ , pend s , subscribing , (dirs c′ ++ [ 0 ] , att) ∷ rs ⟩
begin c (flatMap op f s)  rs = let c′ = inOuter op f false 0 [] c in
  ⟨ inCut true false c′ , pend s , subscribing , (dirs c′ ++ [ 0 ] , att) ∷ rs ⟩
-- the body first, its source once the body's subscription exists
begin c (connect s b)     rs = ⟨ inBody (cs false [] [] false true false) (pend s) c , pend b , subscribing , (dirs c , attBody) ∷ rs ⟩
begin c (connected x)     rs with joinUp c x []
... | true  , c′ = ⟨ c′ , doneS , rising cp , rs ⟩
... | false , c′ = ⟨ c′ , joinS true x , absorbed , rs ⟩
begin c (defer l)         rs = ⟨ c , pend (Later.force l) , subscribing , rs ⟩

-- A lane begun, unless the flatMap's own observer is closed.
start : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → A → List (List ℕ × Tag) → Conf R
start c op f d n o ls a rs with closed c
... | true  = ⟨ c , flatS op f d n o ls , absorbed , rs ⟩
... | false = let c′ = inLn true (inLanes op f d (suc n) o ls [] c) in
  ⟨ inCut true false c′ , pend (f a) , subscribing , (dirs c′ ++ [ 0 ] , att) ∷ rs ⟩

settle : ∀ {B} → Bool → ℕ → Mode B
settle d n = if d ∧ (n ≡ᵇ 0) then rising cp else absorbed

-- The outer's value, admitted as the op says (a bounded merge is not in
-- the spike: its value is dropped).
admit : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → PObs Γ B) → Bool → ℕ → St Γ A → List (St Γ B) → A → List (List ℕ × Tag) → Conf R
admit c (mergeᶠ nothing)  f d n o ls a rs = start c (mergeᶠ nothing) f d n o ls a rs
admit c (mergeᶠ (just m)) f d n o ls a rs = ⟨ c , flatS (mergeᶠ (just m)) f d n o ls , absorbed , rs ⟩
admit c switchᶠ           f d n o ls a rs = start c switchᶠ f d 0 o (killAll ls) a rs
admit c exhaustᶠ          f d n o ls a rs with n ≡ᵇ 0
... | true  = start c exhaustᶠ f d n o ls a rs
... | false = ⟨ c , flatS exhaustᶠ f d n o ls , absorbed , rs ⟩

-- A lane ended: its switch off, its slot freed.
ended : ∀ {Γ B} → St Γ B → St Γ B
ended (lnS b (cutS l a s)) = lnS b (cutS false a s)
ended s                    = s

rise : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Ev A → List (List ℕ × Tag) → Conf R × List (Ev R)
rise top s e rs = ⟨ top , s , absorbed , rs ⟩ , [ e ]
rise (inMap f c) s e rs = ⟨ c , mapS f s , rising (mapEv f e) , rs ⟩ , []
rise (inScan f z c) s (nx a) rs = ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , rs ⟩ , []
rise (inScan f z c) s cp     rs = ⟨ c , scanS f z s , rising cp , rs ⟩ , []
rise (inCut l a c) s e rs = ⟨ c , cutS l a s , (if l then rising e else absorbed) , rs ⟩ , []
rise (inLn b c) s e rs = ⟨ c , lnS b s , rising e , rs ⟩ , []
rise (inTake i p ph c) s (nx a) rs with p a | i
... | true  | _     = ⟨ c , takeS i p ph s , rising (nx a) , rs ⟩ , []
... | false | true  = ⟨ c , takeS i p oweCp s , rising (nx a) , (dirs c , owed) ∷ rs ⟩ , []
... | false | false = ⟨ c , takeS i p oweCut s , rising cp , (dirs c , owed) ∷ rs ⟩ , []
rise (inTake i p ph c) s cp rs = ⟨ c , takeS i p ph s , rising cp , rs ⟩ , []
rise (inOuter op f d n ls c) o (nx a) rs = admit c op f d n o ls a rs , []
rise (inOuter op f d n ls c) o cp     rs = ⟨ c , flatS op f true n o ls , settle true n , rs ⟩ , []
rise (inLanes op f d n o pre post c) s (nx b) rs = ⟨ c , flatS op f d n o (pre ++ s ∷ post) , rising (nx b) , rs ⟩ , []
rise (inLanes op f d n o pre post c) s cp     rs = ⟨ c , flatS op f d (pred n) o (pre ++ ended s ∷ post) , settle d (pred n) , rs ⟩ , []
-- the subject feeds a snapshot of its joiners
rise (inSrc k b c) s (nx a) rs = ⟨ c , connS (record k { feeds = (nx a , CS.subs k) ∷ CS.feeds k }) s b , resuming go , rs ⟩ , []
rise (inSrc k b c) s cp     rs = ⟨ c , connS (record k { closed = true ; feeds = (cp , CS.subs k) ∷ CS.feeds k }) s b , resuming go , rs ⟩ , []
-- the body's completion out, then the source cut
rise (inBody k o c) s (nx b) rs = ⟨ c , connS k o s , rising (nx b) , rs ⟩ , []
rise (inBody k o c) s cp     rs = ⟨ c , connS k o s , rising cp , (dirs c , owed) ∷ rs ⟩ , []

-- A connect's next feed: the next joiner, or the feed done.
feedOn : ∀ {R Γ X B} → Ctx R Γ B → CS X → St Γ X → St (X ∷ Γ) B → List (List ℕ × Tag) → Conf R
feedOn c k o b rs with CS.feeds k
... | [] = ⟨ c , connS k o b , absorbed , rs ⟩
... | (e , []) ∷ fs = ⟨ c , connS (record k { feeds = fs }) o b , absorbed , rs ⟩
... | (e , p ∷ ps) ∷ fs with downs p c (connS (record k { feeds = (e , ps) ∷ fs }) o b)
...   | just (_ , _ , c′ , s′) = ⟨ c′ , s′ , resuming go , (dirs c , go) ∷ rs ⟩
...   | nothing                = ⟨ c , connS (record k { feeds = (e , ps) ∷ fs }) o b , absorbed , rs ⟩

resume : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Tag → List (List ℕ × Tag) → Conf R
-- an of's burst, one value at a time, polling `closed`
resume c (ofS xs) go rs with closed c | xs
... | true  | _       = ⟨ c , doneS , absorbed , rs ⟩
... | false | []      = ⟨ c , doneS , rising cp , rs ⟩
... | false | x ∷ xs′ = ⟨ c , ofS xs′ , rising (nx x) , (dirs c , go) ∷ rs ⟩
-- an attach: a switch cut meanwhile unsubscribes now
resume c (cutS l a s) att rs = ⟨ c , cutS l true (if l then s else unsub s) , absorbed , rs ⟩
resume c (takeS i p oweCp s) owed rs = ⟨ c , takeS i p oweCut s , rising cp , (dirs c , owed) ∷ rs ⟩
resume c (takeS i p oweCut s) owed rs = ⟨ c , takeS i p running (cut s) , absorbed , rs ⟩
resume c (connS k o b) go rs = feedOn c k o b rs
resume c (connS k o b) attBody rs =
  ⟨ inSrc (record k { bodyAtt = true }) b c , o , subscribing , (dirs c , att) ∷ rs ⟩
resume c (connS k o b) att rs =
  ⟨ c , connS (record k { srcAtt = true }) (if CS.srcLive k then o else unsub o) b , absorbed , rs ⟩
resume c (connS k o b) owed rs =
  ⟨ c , connS (record k { srcLive = false }) (if CS.srcAtt k then unsub o else o) b , absorbed , rs ⟩
-- a joiner fed: what its binder feeds, through its switch
resume c (joinS true x) go rs with fedUp c x
... | just e  = ⟨ c , joinS true x , rising e , rs ⟩
... | nothing = ⟨ c , joinS true x , absorbed , rs ⟩
resume c s _ rs = ⟨ c , s , absorbed , rs ⟩

step : ∀ {R} → Conf R → Conf R × List (Ev R)
step ⟨ c , pend o , subscribing , rs ⟩ = begin c o rs , []
step ⟨ c , s , resuming t , rs ⟩       = resume c s t rs , []
step ⟨ c , s , rising e , rs ⟩         = rise c s e rs
step ⟨ c , s , absorbed , (p , t) ∷ rs ⟩ with downs p top (plug c s)
... | just (_ , _ , c′ , s′) = ⟨ c′ , s′ , resuming t , rs ⟩ , []
... | nothing                = ⟨ c , s , absorbed , rs ⟩ , []
step k = k , []

load : ∀ {R} → PObs [] R → Conf R
load o = ⟨ top , pend o , subscribing , [] ⟩

runN : ∀ {R} → ℕ → Conf R → List (Ev R)
runN zero    k = []
runN (suc n) k with step k
... | k′ , out = out ++ runN n k′
