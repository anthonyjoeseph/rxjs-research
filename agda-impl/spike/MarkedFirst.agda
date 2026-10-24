{-# OPTIONS --guardedness #-}

-- SPIKE: A LANE FIRST, FROM THE ORDER.  The order invariant (`Ord`) is a
-- predicate on the keys the whole tree owns and on its joiners, read at
-- the configuration's position; nothing in it names a frame.  From it,
-- every node in the tree runs AHEAD of the position: its next event, and
-- what it would leave running, strictly after (`ahead`).  That is one row
-- per node, read off the node's own keys and its children's rows; the
-- link to the meaning is one fact per stream function.
--
-- A lane rising at `p` then comes first among its flatMap's parts
-- (`lanes-first`), each part being a sibling of the hole in the tree.
module spike.MarkedFirst where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; [_]) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᴬ; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to all-++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Timeline; idle; pin; out; skip; end; hush; ix; _∪_; _<ᵖ_;
  <ᵖ-trans; <ᵖ-asym; <ᵖ-below; inside)
open import denotation.MonotonicList using (MonotonicList; head; headᴼ; cutᴼ; cuts; whole; go; beside; burstOn; runOn; pinned; tailᴱ; rejoin;
  mapᴱ; scanᴱ; takeWhileᴱ) renaming (cold to coldᴹ)
open import denotation.Denote using (flatOp)
open import denotation.Unfold using (Node; NEnv; meaning; cutᴺ; stateᴺ; states; outerᴺ; subscribe; restᶜ; restsᶜ; connectᶜ;
  Source; live; ended)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.MarkedPure using (Tape; module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  CS; cs; free; cpAt; cutAt; overAt; nx; cp; attached; attAt;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; own)
open import spike.MarkedGhost using (gh; tape; subOr; srcG; srcRun; srcState; envAt; lane; outerG; poolG; doneG; lanesL; liveL;
  deadL; deadOne; outerT; poolRuns; tailsOn; endOf)
open import spike.MarkedRace using (First; first; NotBefore; After; TailNotBefore)
open import adequacy.Stepper.Flat using (head-mapᴱ)

open Events∞

------------------------------------------------------------------------
-- The keys a tree owns

mutual
  keys : ∀ {Γ A} → St Γ A → List Key
  keys s = mapL proj₂ (own s) ++ kidKeys s

  kidKeys : ∀ {Γ A} → St Γ A → List Key
  kidKeys (mapS f s)              = keys s
  kidKeys (scanS f z s)           = keys s
  kidKeys (cutS l a s)            = keys s
  kidKeys (lnS b s)               = keys s
  kidKeys (takeS i q w s)         = keys s
  kidKeys (flatS op f d n q o ls) = keys o ++ keysL ls
  kidKeys (connS k o b)           = keys o ++ keys b
  kidKeys _                       = []

  keysL : ∀ {Γ A} → List (St Γ A) → List Key
  keysL []       = []
  keysL (s ∷ ls) = keys s ++ keysL ls

-- Every key beyond `p`'s whole subtree.
Beyond : Pos → List Key → Set
Beyond p = All (λ k → (k <ᴷ after p) ≡ false)

------------------------------------------------------------------------
-- What a joiner reads

-- A run an environment holds: an end, or next after `p`.
Settled : ∀ {A} → Pos → Events A → Set
Settled p (end c) = ⊤
Settled p e       = After p (head e)

EnvAfter : ∀ {Γ} → Pos → NEnv Γ → Set
EnvAfter p [] = ⊤
EnvAfter p (e ∷ ρ) = Settled p e × EnvAfter p ρ

-- An untold joiner reading an end reads one after `p`.
Told : ∀ {A} → Pos → Events A → Maybe Pos → Set
Told p (end c) nothing = After p (just c)
Told p _       _       = ⊤

mutual
  Live : ∀ {Γ A} → Pos → NEnv Γ → St Γ A → Set
  Live p ρ (mapS f s)              = Live p ρ s
  Live p ρ (scanS f z s)           = Live p ρ s
  Live p ρ (cutS l a s)            = Live p ρ s
  Live p ρ (lnS b s)               = Live p ρ s
  Live p ρ (takeS i q w s)         = Live p ρ s
  Live p ρ (flatS op f d n q o ls) = Live p ρ o × Lives p ρ ls
  Live p ρ (connS k o b)           = Live p ρ o × Live p (srcRun (srcG k o) ρ ∷ ρ) b
  Live p ρ (joinS j true x ib)     = Told p (lookupᴬ ρ x) (endOf ib)
  Live p ρ _                       = ⊤

  Lives : ∀ {Γ A} → Pos → NEnv Γ → List (St Γ A) → Set
  Lives p ρ []       = ⊤
  Lives p ρ (s ∷ ls) = Live p ρ s × Lives p ρ ls

------------------------------------------------------------------------
-- Ahead of a position

TailAfter : Pos → Tail → Set
TailAfter p idle      = ⊤
TailAfter p (pin k u) = p <ᵖ k ≡ true

Ahead : ∀ {A} → Pos → Events∞ A → Set
Ahead p h = After p (head (force h)) × TailAfter p (cut h)

AheadN : ∀ {Γ A} → Pos → NEnv Γ → Node Γ A → Set
AheadN p ρ n = Ahead p (stateᴺ n ρ)

------------------------------------------------------------------------
-- The order, as a configuration carries it

record Fresh {R} (p : Pos) (t : St [] R) : Set where
  constructor fresh
  field
    beyond : Beyond p (keys t)
    alive  : Live p [] t

record Past {R} (p : Pos) (t : St [] R) : Set where
  constructor past
  field
    after′ : All (λ k → (at p <ᴷ k) ≡ true) (keys t)
    alive  : Live p [] t

Ord : ∀ {R} → Conf R → Set
Ord ⟨ c , s , subscribing , p ⟩ = Fresh p (plug c s)
Ord ⟨ c , s , rising e , p ⟩    = Fresh p (plug c s)
Ord ⟨ c , s , absorbed , p ⟩    = Past p (plug c s)

------------------------------------------------------------------------
-- The leaves: one per stream function, and the key order

postulate
  -- A key beyond `p`'s subtree is a position after it.
  beyond-after : ∀ p k → (at k <ᴷ after p) ≡ false → p <ᵖ k ≡ true
  -- A started cold runs at or after when it is next due.
  ahead-cold : ∀ {Γ A} p (ρ : NEnv Γ) b (l : Tape A) → Beyond p (keys {Γ} (coldS b l)) → AheadN p ρ (tape b l)
  -- A takeWhile shows its source's next event at or under it.
  take-head : ∀ {A} p i (q : A → Bool) (e : Events A) → After p (head e) → After p (head (takeWhileᴱ i q e))
  -- A merge's next is at or under the next of one of its parts.
  go-ahead : ∀ {B} p op (o : Maybe (Events∞ (MonotonicList B))) ls qs t → After p (headᴼ o) → All (Ahead p) ls → TailAfter p t
           → After p (head (go op o ls qs t))
  -- A connect's next is at or under its body's or its source's.
  beside-ahead : ∀ {A B} p r (β : Events∞ B) (σ : Events∞ A) → Ahead p β → Ahead p σ → After p (head (beside r β σ))
  -- A joiner shows its source's next at or under it, or after its own.
  rejoin-after : ∀ {A} p j (e : Events A) → After p (head e) → After p (head (rejoin j e))
  -- A program subscribed after `p` runs after it.
  sub-after : ∀ {Γ A} p r (o : Obs Timeline Γ A) (ρ : NEnv Γ) → p <ᵖ r ≡ true → AheadN p ρ (subscribe o r)

------------------------------------------------------------------------
-- Tails

∪-after : ∀ p t u → TailAfter p t → TailAfter p u → TailAfter p (t ∪ u)
∪-after p idle      u          a b = b
∪-after p (pin k r) idle       a b = a
∪-after p (pin k r) (pin k′ v) a b with k <ᵖ k′
... | true  = a
... | false = b

tail-head : ∀ {A} p t → TailAfter p t → After p (head (tailᴱ {A} t))
tail-head p idle      a = tt
tail-head p (pin k u) a = a

runOn-after : ∀ {A} p r (e : Events A) t → After p (head e) → TailAfter p t → TailAfter p (runOn r e t)
runOn-after p r (out k a s) t h u with inside r k
... | true  = h
... | false = u
runOn-after p r (skip k s) t h u with inside r k
... | true  = h
... | false = u
runOn-after p r (end c) t h u = u
runOn-after p r hush    t h u = u

burstOn-after : ∀ {A} p r (σ : Events∞ A) → Ahead p σ → TailAfter p (burstOn r σ)
burstOn-after p r σ (h , t) = runOn-after p r (force σ) (cut σ) h t

cuts-after : ∀ {B} p (ls : List (Events∞ B)) → All (Ahead p) ls → TailAfter p (cuts ls)
cuts-after p []       []             = tt
cuts-after p (l ∷ ls) ((_ , t) ∷ as) = ∪-after p (cut l) (cuts ls) t (cuts-after p ls as)

-- Ahead of `p`, not before it.
not-before : ∀ p m → After p m → NotBefore p m
not-before p nothing  a = tt
not-before p (just k) a = <ᵖ-asym p k a

tail-not-before : ∀ p t → TailAfter p t → TailNotBefore p t
tail-not-before p idle      a = tt
tail-not-before p (pin k u) a = <ᵖ-asym p k a

------------------------------------------------------------------------
-- Nodes

rest-ahead : ∀ {Γ A} p (ρ : NEnv Γ) (n : Node Γ A) → AheadN p ρ n → AheadN p ρ (restᶜ {B = A} n)
rest-ahead p ρ n (h , t) = tail-head p (cutᴺ n ρ) t , t

doneG-ahead : ∀ {Γ A} p (ρ : NEnv Γ) mo l (n : Node Γ A) → AheadN p ρ n → AheadN p ρ (doneG mo l n)
doneG-ahead p ρ (just _) l     n a = rest-ahead p ρ n a
doneG-ahead p ρ nothing  false n a = rest-ahead p ρ n a
doneG-ahead p ρ nothing  true  n a = a

states-ahead : ∀ {Γ A} p (ρ : NEnv Γ) (ns : List (Node Γ A)) → All (AheadN p ρ) ns → All (Ahead p) (states ns ρ)
states-ahead p ρ []       []       = []
states-ahead p ρ (n ∷ ns) (a ∷ as) = a ∷ states-ahead p ρ ns as

rests-after : ∀ {Γ A B} p (ρ : NEnv Γ) (ds : List (Node Γ A)) → All (AheadN p ρ) ds → TailAfter p (cutᴺ (restsᶜ {B = B} ds) ρ)
rests-after p ρ []       []             = tt
rests-after p ρ (d ∷ ds) ((_ , t) ∷ as) = ∪-after p (cutᴺ d ρ) _ t (rests-after p ρ ds as)

tailsOn-after : ∀ {Γ B} p (ρ : NEnv Γ) (ds : List (Node Γ B)) t → All (AheadN p ρ) ds → TailAfter p t → TailAfter p (tailsOn ds ρ t)
tailsOn-after p ρ []       t []             a = a
tailsOn-after p ρ (d ∷ ds) t ((_ , u) ∷ as) a = ∪-after p (cutᴺ d ρ) _ u (tailsOn-after p ρ ds t as a)

-- A lane's ghost, in the list or in the pool.
liveL-ahead : ∀ {Γ B} p (ρ : NEnv Γ) (s : St Γ B) → AheadN p ρ (gh s) → All (AheadN p ρ) (liveL s)
liveL-ahead p ρ (lnS false s)   a = []
liveL-ahead p ρ (lnS true s)    a = a ∷ []
liveL-ahead p ρ (pend o)        a = a ∷ []
liveL-ahead p ρ (coldS b l)     a = a ∷ []
liveL-ahead p ρ (ofS i q xs)    a = a ∷ []
liveL-ahead p ρ doneS           a = a ∷ []
liveL-ahead p ρ (mapS f s)      a = a ∷ []
liveL-ahead p ρ (scanS f z s)   a = a ∷ []
liveL-ahead p ρ (cutS l w s)    a = a ∷ []
liveL-ahead p ρ (takeS i q w s) a = a ∷ []
liveL-ahead p ρ (flatS op f d n q o ls) a = a ∷ []
liveL-ahead p ρ (connS k o b)   a = a ∷ []
liveL-ahead p ρ (joinS j g x ib) a = a ∷ []

deadOne-ahead : ∀ {Γ B} p (ρ : NEnv Γ) (s : St Γ B) → AheadN p ρ (gh s) → All (AheadN p ρ) (deadOne s)
deadOne-ahead p ρ (lnS false s)   a = a ∷ []
deadOne-ahead p ρ (lnS true s)    a = []
deadOne-ahead p ρ (pend o)        a = []
deadOne-ahead p ρ (coldS b l)     a = []
deadOne-ahead p ρ (ofS i q xs)    a = []
deadOne-ahead p ρ doneS           a = []
deadOne-ahead p ρ (mapS f s)      a = []
deadOne-ahead p ρ (scanS f z s)   a = []
deadOne-ahead p ρ (cutS l w s)    a = []
deadOne-ahead p ρ (takeS i q w s) a = []
deadOne-ahead p ρ (flatS op f d n q o ls) a = []
deadOne-ahead p ρ (connS k o b)   a = []
deadOne-ahead p ρ (joinS j g x ib) a = []

LanesAhead : ∀ {Γ B} → Pos → NEnv Γ → List (St Γ B) → Set₁
LanesAhead p ρ = All (λ s → AheadN p ρ (gh s))

lanesL-ahead : ∀ {Γ B} p (ρ : NEnv Γ) (ls : List (St Γ B)) → LanesAhead p ρ ls → All (AheadN p ρ) (lanesL ls)
lanesL-ahead p ρ []       []       = []
lanesL-ahead p ρ (s ∷ ls) (a ∷ as) = all-++⁺ (lanesL-ahead p ρ ls as) (liveL-ahead p ρ s a)

deadL-ahead : ∀ {Γ B} p (ρ : NEnv Γ) (ls : List (St Γ B)) → LanesAhead p ρ ls → All (AheadN p ρ) (deadL ls)
deadL-ahead p ρ []       []       = []
deadL-ahead p ρ (s ∷ ls) (a ∷ as) = all-++⁺ (deadOne-ahead p ρ s a) (deadL-ahead p ρ ls as)

-- The outer a flatMap shows its lanes from.
outer-ahead : ∀ {Γ A B} p (ρ : NEnv Γ) (g : A → Pos → Node Γ B) d (n : Node Γ A) → AheadN p ρ n
            → After p (headᴼ (outerᴺ g (outerG d n) ρ)) × TailAfter p (cutᴼ (outerᴺ g (outerG d n) ρ))
outer-ahead p ρ g true  n a       = tt , tt
outer-ahead p ρ g false n (h , t) = subst (After p) (sym (head-mapᴱ _ (meaning n ρ))) h , t

pool-after : ∀ {Γ A B} p (ρ : NEnv Γ) d (n : Node Γ A) (ds : List (Node Γ B)) → AheadN p ρ n → All (AheadN p ρ) ds
           → TailAfter p (cutᴺ (poolG d n ds) ρ)
pool-after p ρ false n ds a as      = rests-after p ρ ds as
pool-after p ρ true  n ds (_ , t) as = ∪-after p (cutᴺ n ρ) _ t (rests-after p ρ ds as)

outerT-after : ∀ {Γ A} p (ρ : NEnv Γ) d (n : Node Γ A) t → AheadN p ρ n → TailAfter p t → TailAfter p (outerT d n ρ t)
outerT-after p ρ false n t a       u = u
outerT-after p ρ true  n t (_ , v) u = ∪-after p (cutᴺ n ρ) t v u

scan-head : ∀ {A B} (f : B → A → B) z (e : Events A) → head (scanᴱ f z e) ≡ head e
scan-head f z (out k a r) = refl
scan-head f z (skip k r)  = refl
scan-head f z (end k)     = refl
scan-head f z hush        = refl

after-ext : ∀ p k x → p <ᵖ k ≡ true → p <ᵖ (k ++ [ x ]) ≡ true
after-ext p k x a = <ᵖ-trans p k (k ++ [ x ]) a (<ᵖ-below k [])

env-lookup : ∀ {Γ A} p (ρ : NEnv Γ) (x : A ∈ Γ) → EnvAfter p ρ → Settled p (lookupᴬ ρ x)
env-lookup p (e ∷ ρ) (here refl) (s , _) = s
env-lookup p (e ∷ ρ) (there x)   (_ , v) = env-lookup p ρ x v

told-after : ∀ {A} p (e : Events A) → Settled p e → Told p e nothing → After p (head e)
told-after p (out k a r) s t = s
told-after p (skip k r)  s t = s
told-after p (end c)     s t = t
told-after p hush        s t = s

settled : ∀ {A} p (e : Events A) → After p (head e) → Settled p e
settled p (out k a r) h = h
settled p (skip k r)  h = h
settled p (end c)     h = tt
settled p hush        h = h

------------------------------------------------------------------------
-- EVERY NODE AHEAD

kids : ∀ {Γ A} p (s : St Γ A) → Beyond p (keys s) → Beyond p (kidKeys s)
kids p s = ++⁻ʳ (mapL proj₂ (own s))

-- A connect's source, as its body reads it and as it runs.
SrcAhead : ∀ {Γ X} → Pos → NEnv Γ → Source Γ X → Set
SrcAhead p ρ src = Ahead p (srcState src ρ)

conn-ahead : ∀ {Γ X B} p (ρ : NEnv Γ) r (b : Node (X ∷ Γ) B) (src : Source Γ X) → SrcAhead p ρ src
           → AheadN p (srcRun src ρ ∷ ρ) b → AheadN p ρ (connectᶜ r b src)
conn-ahead p ρ r b (live s) as ab =
  beside-ahead p r (stateᴺ b (meaning s ρ ∷ ρ)) (stateᴺ s ρ) ab as
  , ∪-after p (burstOn r (stateᴺ s ρ)) (cutᴺ b (meaning s ρ ∷ ρ)) (burstOn-after p r (stateᴺ s ρ) as) (proj₂ ab)
conn-ahead p ρ r b (ended c t) as ab =
  beside-ahead p r (stateᴺ b (end c ∷ ρ)) (stateᴺ t ρ) ab as
  , ∪-after p (burstOn r (stateᴺ t ρ)) (cutᴺ b (end c ∷ ρ)) (burstOn-after p r (stateᴺ t ρ) as) (proj₂ ab)

src-settled : ∀ {Γ X} p (ρ : NEnv Γ) (src : Source Γ X) → SrcAhead p ρ src → Settled p (srcRun src ρ)
src-settled p ρ (live s)    (h , _) = settled p (meaning s ρ) h
src-settled p ρ (ended c t) _       = tt

flat-ahead : ∀ {Γ A B} p (ρ : NEnv Γ) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls → AheadN p ρ (gh o) → LanesAhead p ρ ls
           → AheadN p ρ (gh (flatS op f d n q o ls))
flat-ahead p ρ op f d n q o ls ao als =
  go-ahead p (flatOp op) O L (mapL (λ a → coldᴹ λ r → stateᴺ (lane f a r) ρ) q) T (proj₁ oa) aL pl
  , ∪-after p (cutᴼ O) (cuts L ∪ T) (proj₂ oa) (∪-after p (cuts L) T (cuts-after p L aL) pl)
  where
    O  = outerᴺ (lane f) (outerG d (gh o)) ρ
    L  = states (lanesL ls) ρ
    T  = cutᴺ (poolG d (gh o) (deadL ls)) ρ
    oa = outer-ahead p ρ (lane f) d (gh o) ao
    aL = states-ahead p ρ (lanesL ls) (lanesL-ahead p ρ ls als)
    pl = pool-after p ρ d (gh o) (deadL ls) ao (deadL-ahead p ρ ls als)

-- A subscribe after `p`, or the node's ghost.
subOr-ahead : ∀ {Γ X} p (ρ : NEnv Γ) r (o : St Γ X) → p <ᵖ r ≡ true → AheadN p ρ (gh o) → AheadN p ρ (subOr r o)
subOr-ahead p ρ r (pend o)        a g = sub-after p r o ρ a
subOr-ahead p ρ r (coldS b l)     a g = g
subOr-ahead p ρ r (ofS i q xs)    a g = g
subOr-ahead p ρ r doneS           a g = g
subOr-ahead p ρ r (mapS f s)      a g = g
subOr-ahead p ρ r (scanS f z s)   a g = g
subOr-ahead p ρ r (cutS l w s)    a g = g
subOr-ahead p ρ r (lnS b s)       a g = g
subOr-ahead p ρ r (takeS i q w s) a g = g
subOr-ahead p ρ r (flatS op f d n q o ls) a g = g
subOr-ahead p ρ r (connS k o b)   a g = g
subOr-ahead p ρ r (joinS j g′ x ib) a g = g

-- What a connect's source runs: subscribed at the body's mark, its
-- ghost, or ended.
src-ahead : ∀ {Γ X B} p (ρ : NEnv Γ) k (o : St Γ X) (b : St (X ∷ Γ) B) → Beyond p (mapL proj₂ (own (connS k o b))) → AheadN p ρ (gh o)
          → SrcAhead p ρ (srcG k o)
src-ahead p ρ (cs cl sl sa (just r) as ow sr e) o b (y ∷ _) g = subOr-ahead p ρ (r ++ [ ix 1 ]) o (beyond-after p _ y) g
src-ahead p ρ (cs false sl sa nothing as ow sr e) o b y g = g
src-ahead p ρ (cs true  sl sa nothing as ow sr e) o b y g = rest-ahead p ρ (gh o) g

mutual
  ahead : ∀ {Γ A} p (ρ : NEnv Γ) (s : St Γ A) → EnvAfter p ρ → Beyond p (keys s) → Live p ρ s → AheadN p ρ (gh s)
  ahead p ρ (pend o)        v y l = tt , tt
  ahead p ρ (coldS b t)     v y l = ahead-cold p ρ b t y
  ahead p ρ (ofS i q [])    v (y ∷ _) l = beyond-after p _ y , tt
  ahead p ρ (ofS i q (x ∷ xs)) v (y ∷ _) l = beyond-after p _ y , tt
  ahead p ρ doneS           v y l = tt , tt
  ahead p ρ (mapS f s)      v y l with ahead p ρ s v y l
  ... | h , t = subst (After p) (sym (head-mapᴱ f (meaning (gh s) ρ))) h , t
  ahead p ρ (scanS f z s)   v y l with ahead p ρ s v y l
  ... | h , t = subst (After p) (sym (scan-head f z (meaning (gh s) ρ))) h , t
  ahead p ρ (cutS true a s) v y l = ahead p ρ s v (kids p (cutS true a s) y) l
  ahead p ρ (cutS false a s) v y l = rest-ahead p ρ (gh s) (ahead p ρ s v (kids p (cutS false a s) y) l)
  ahead p ρ (lnS b s)       v y l = ahead p ρ s v y l
  ahead p ρ (takeS i q free s) v y l with ahead p ρ s v y l
  ... | h , t = take-head p i q (meaning (gh s) ρ) h , t
  ahead p ρ (takeS i q (cpAt r) s) v (y ∷ ys) l = beyond-after p _ y , proj₂ (ahead p ρ s v ys l)
  ahead p ρ (takeS i q (cutAt r) s) v (_ ∷ ys) l = rest-ahead p ρ (gh s) (ahead p ρ s v ys l)
  ahead p ρ (takeS i q (overAt r) s) v y l = rest-ahead p ρ (gh s) (ahead p ρ s v y l)
  ahead p ρ (flatS op f d n q o ls) v y (lo , lls) = flat-ahead p ρ op f d n q o ls ao als
    where
      yk = kids p (flatS op f d n q o ls) y
      ao = ahead p ρ o v (++⁻ˡ (keys o) yk) lo
      als = aheadL p ρ ls v (++⁻ʳ (keys o) yk) lls
  ahead p ρ (connS k o b) v y (lo , lb) =
    doneG-ahead p ρ (CS.owedAt k) (CS.srcLive k) _
      (conn-ahead p ρ (CS.srcAt k) (gh b) (srcG k o) sa (ahead p _ b (src-settled p ρ (srcG k o) sa , v) (++⁻ʳ (keys o) yk) lb))
    where
      yk = kids p (connS k o b) y
      sa = src-ahead p ρ k o b (++⁻ˡ (mapL proj₂ (own (connS k o b))) y) (ahead p ρ o v (++⁻ˡ (keys o) yk) lo)
  ahead p ρ (joinS j false x ib) v y l = tt , tt
  ahead p ρ (joinS j true x []) v y l = rejoin-after p j _ (told-after p (lookupᴬ ρ x) (env-lookup p ρ x v) l) , tt
  ahead p ρ (joinS j true x ((q , nx a) ∷ ib)) v (y ∷ _) l = beyond-after p q y , tt
  ahead p ρ (joinS j true x ((q , cp) ∷ ib))   v (y ∷ _) l = beyond-after p q y , tt

  aheadL : ∀ {Γ A} p (ρ : NEnv Γ) (ls : List (St Γ A)) → EnvAfter p ρ → Beyond p (keysL ls) → Lives p ρ ls → LanesAhead p ρ ls
  aheadL p ρ []       v y l        = []
  aheadL p ρ (s ∷ ls) v y (l , ls′) = ahead p ρ s v (++⁻ˡ (keys s) y) l ∷ aheadL p ρ ls v (++⁻ʳ (keys s) y) ls′


------------------------------------------------------------------------
-- The order at a hole: its keys, its joiners, the runs its connects hold

keysL-split : ∀ {Γ A} {P : Key → Set} (pre : List (St Γ A)) {s post} → All P (keysL (pre ++ s ∷ post))
            → All P (keysL pre) × All P (keys s) × All P (keysL post)
keysL-split []        a = [] , ++⁻ˡ _ a , ++⁻ʳ _ a
keysL-split (x ∷ pre) a with keysL-split pre (++⁻ʳ (keys x) a)
... | u , v , w = all-++⁺ (++⁻ˡ (keys x) a) u , v , w

lives-split : ∀ {Γ A} p (ρ : NEnv Γ) (pre : List (St Γ A)) {s post} → Lives p ρ (pre ++ s ∷ post) → Lives p ρ pre × Live p ρ s × Lives p ρ post
lives-split p ρ []        (l , ls) = tt , l , ls
lives-split p ρ (x ∷ pre) (l , ls) with lives-split p ρ pre ls
... | u , v , w = (l , u) , v , w

keys-at : ∀ {R Γ A} {P : Key → Set} (c : Ctx R Γ A) (s : St Γ A) → All P (keys (plug c s)) → All P (keys s)
keys-at top                               s a = a
keys-at (inMap f c)                       s a = keys-at c (mapS f s) a
keys-at (inScan f z c)                    s a = keys-at c (scanS f z s) a
keys-at (inCut l w c)                     s a = ++⁻ʳ (mapL proj₂ (own (cutS l w s))) (keys-at c (cutS l w s) a)
keys-at (inLn b c)                        s a = keys-at c (lnS b s) a
keys-at (inTake i q w c)                  s a = ++⁻ʳ (mapL proj₂ (own (takeS i q w s))) (keys-at c (takeS i q w s) a)
keys-at (inOuter op f d n q ls c)         s a = ++⁻ˡ (keys s) (keys-at c (flatS op f d n q s ls) a)
keys-at (inLanes op f d n q o pre post c) s a = proj₁ (proj₂ (keysL-split pre (++⁻ʳ (keys o) (keys-at c (flatS op f d n q o (pre ++ s ∷ post)) a))))
keys-at (inSrc k b c)                     s a = ++⁻ˡ (keys s) (++⁻ʳ (mapL proj₂ (own (connS k s b))) (keys-at c (connS k s b) a))
keys-at (inBody k o c)                    s a = ++⁻ʳ (keys o) (++⁻ʳ (mapL proj₂ (own (connS k o s))) (keys-at c (connS k o s) a))

live-at : ∀ {R Γ A} p (c : Ctx R Γ A) (s : St Γ A) → Live p [] (plug c s) → Live p (envAt c) s
live-at p top                               s l = l
live-at p (inMap f c)                       s l = live-at p c (mapS f s) l
live-at p (inScan f z c)                    s l = live-at p c (scanS f z s) l
live-at p (inCut b w c)                     s l = live-at p c (cutS b w s) l
live-at p (inLn b c)                        s l = live-at p c (lnS b s) l
live-at p (inTake i q w c)                  s l = live-at p c (takeS i q w s) l
live-at p (inOuter op f d n q ls c)         s l = proj₁ (live-at p c (flatS op f d n q s ls) l)
live-at p (inLanes op f d n q o pre post c) s l = proj₁ (proj₂ (lives-split p (envAt c) pre (proj₂ (live-at p c (flatS op f d n q o (pre ++ s ∷ post)) l))))
live-at p (inSrc k b c)                     s l = proj₁ (live-at p c (connS k s b) l)
live-at p (inBody k o c)                    s l = proj₂ (live-at p c (connS k o s) l)

-- Every run a hole's connects hold is an end or ahead of `p`.
env-after : ∀ {R Γ A} p (c : Ctx R Γ A) (s : St Γ A) → Beyond p (keys (plug c s)) → Live p [] (plug c s) → EnvAfter p (envAt c)
env-after p top                               s y l = tt
env-after p (inMap f c)                       s y l = env-after p c (mapS f s) y l
env-after p (inScan f z c)                    s y l = env-after p c (scanS f z s) y l
env-after p (inCut b w c)                     s y l = env-after p c (cutS b w s) y l
env-after p (inLn b c)                        s y l = env-after p c (lnS b s) y l
env-after p (inTake i q w c)                  s y l = env-after p c (takeS i q w s) y l
env-after p (inOuter op f d n q ls c)         s y l = env-after p c (flatS op f d n q s ls) y l
env-after p (inLanes op f d n q o pre post c) s y l = env-after p c (flatS op f d n q o (pre ++ s ∷ post)) y l
env-after p (inSrc k b c)                     s y l = env-after p c (connS k s b) y l
env-after p (inBody k o c)                    s y l = src-settled p (envAt c) (srcG k o) sa , v
  where
    v  = env-after p c (connS k o s) y l
    yc = keys-at c (connS k o s) y
    sa = src-ahead p (envAt c) k o s (++⁻ˡ (mapL proj₂ (own (connS k o s))) yc)
           (ahead p (envAt c) o v (++⁻ˡ (keys o) (++⁻ʳ (mapL proj₂ (own (connS k o s))) yc)) (proj₁ (live-at p c (connS k o s) l)))

------------------------------------------------------------------------
-- A LANE FIRST

first-lanes : ∀ {R Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) p
            → Fresh p (plug c (flatS op f d n q o (pre ++ s ∷ post)))
            → First p (outerᴺ (lane f) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL pre) (envAt c))
                (outerT d (gh o) (envAt c) (poolRuns pre post true (envAt c) (stateᴺ (gh s) (envAt c))))
first-lanes op f d n q o pre post c s p (fresh y l) =
  first (mapᴬ (λ a → not-before p _ (proj₁ a)) (states-ahead p ρ (lanesL post) (lanesL-ahead p ρ post apost)))
        (mapᴬ proj₁ (states-ahead p ρ (lanesL pre) (lanesL-ahead p ρ pre apre)))
        (not-before p _ (proj₁ (outer-ahead p ρ (lane f) d (gh o) ao)))
        (tail-not-before p _ (outerT-after p ρ d (gh o) _ ao
          (tailsOn-after p ρ (deadL pre) _ (deadL-ahead p ρ pre apre) (rests-after p ρ (deadL post) (deadL-ahead p ρ post apost)))))
  where
    t   = flatS op f d n q o (pre ++ s ∷ post)
    ρ   = envAt c
    v   = env-after p c t y l
    yt  = keys-at c t y
    lt  = live-at p c t l
    ao  = ahead p ρ o v (++⁻ˡ (keys o) yt) (proj₁ lt)
    yls = keysL-split pre (++⁻ʳ (keys o) yt)
    lls = lives-split p ρ pre (proj₂ lt)
    apre  = aheadL p ρ pre v (proj₁ yls) (proj₁ lls)
    apost = aheadL p ρ post v (proj₂ (proj₂ yls)) (proj₂ (proj₂ lls))
