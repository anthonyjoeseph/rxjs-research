{-# OPTIONS --guardedness #-}

-- SPIKE 4: WHAT THE HEAP GOT FOR FREE, PAID HERE.  Every path the
-- spike-3 machine follows lands: a job's path from the root, and a
-- joiner's path from its binder, reach a node in every configuration
-- the machine reaches, so the machine's `nothing` arms are dead.
--
-- `Reach` reads only the tree's SHAPE, never a node's data, so a step
-- that rewrites a node's flags or a subject's record moves no path.
-- The shape only grows: a lane is marked off, never removed; a leaf
-- becomes a subtree.  `Good` asks, of each binder, that every joiner it
-- lists or is feeding is reached from it; it is lifted through a
-- context the way growth is.
module spike.StateTree3Valid where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.List.Membership.Propositional using (_∈_)
open import denotation.MonotonicList.Events using (ix)
open import Tree using (Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import spike.StateTree3

------------------------------------------------------------------------
-- Reaching a node: by the tree's shape alone

Leaf : List ℕ → Set
Leaf []      = ⊤
Leaf (_ ∷ _) = ⊥

mutual
  Reach : ∀ {Γ A} → List ℕ → St Γ A → Set
  Reach p (pend o)              = Leaf p
  Reach p (ofS q i xs)          = Leaf p
  Reach p doneS                 = Leaf p
  Reach p (joinS j g x)         = Leaf p
  Reach p (mapS f s)            = One p s
  Reach p (scanS f z s)         = One p s
  Reach p (cutS l a s)          = One p s
  Reach p (lnS b s)             = One p s
  Reach p (takeS i q ph s)      = One p s
  Reach p (flatS op f d n o ls) = Fl p o ls
  Reach p (connS k o b)         = Two p o b

  One : ∀ {Γ A} → List ℕ → St Γ A → Set
  One []          s = ⊤
  One (zero ∷ p)  s = Reach p s
  One (suc _ ∷ p) s = ⊥

  Fl : ∀ {Γ A B} → List ℕ → St Γ A → List (St Γ B) → Set
  Fl []          o ls = ⊤
  Fl (zero ∷ p)  o ls = Reach p o
  Fl (suc i ∷ p) o ls = ReachL i p ls

  Two : ∀ {Γ X B} → List ℕ → St Γ X → St (X ∷ Γ) B → Set
  Two []                o b = ⊤
  Two (zero ∷ p)        o b = Reach p o
  Two (suc zero ∷ p)    o b = Reach p b
  Two (suc (suc _) ∷ p) o b = ⊥

  ReachL : ∀ {Γ B} → ℕ → List ℕ → List (St Γ B) → Set
  ReachL i       p []       = ⊥
  ReachL zero    p (s ∷ ls) = Reach p s
  ReachL (suc i) p (s ∷ ls) = ReachL i p ls

Grows : ∀ {Γ A} → St Γ A → St Γ A → Set
Grows s s′ = ∀ p → Reach p s → Reach p s′

reach-nil : ∀ {Γ A} (s : St Γ A) → Reach [] s
reach-nil (pend o)              = tt
reach-nil (ofS q i xs)          = tt
reach-nil doneS                 = tt
reach-nil (joinS j g x)         = tt
reach-nil (mapS f s)            = tt
reach-nil (scanS f z s)         = tt
reach-nil (cutS l a s)          = tt
reach-nil (lnS b s)             = tt
reach-nil (takeS i q ph s)      = tt
reach-nil (flatS op f d n o ls) = tt
reach-nil (connS k o b)         = tt

-- A leaf grows into anything.
from-leaf : ∀ {Γ A} (s : St Γ A) p → Leaf p → Reach p s
from-leaf s [] _ = reach-nil s

-- Growth under one child.
one-grow : ∀ {Γ A} {s s′ : St Γ A} → Grows s s′ → ∀ p → One p s → One p s′
one-grow g []          r = tt
one-grow g (zero ∷ p)  r = g p r

fl-grow : ∀ {Γ A B} {o o′ : St Γ A} {ls ls′ : List (St Γ B)} → Grows o o′ → (∀ i p → ReachL i p ls → ReachL i p ls′) → ∀ p → Fl p o ls → Fl p o′ ls′
fl-grow g h []          r = tt
fl-grow g h (zero ∷ p)  r = g p r
fl-grow g h (suc i ∷ p) r = h i p r

two-grow : ∀ {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} → Grows o o′ → Grows b b′ → ∀ p → Two p o b → Two p o′ b′
two-grow g h []             r = tt
two-grow g h (zero ∷ p)     r = g p r
two-grow g h (suc zero ∷ p) r = h p r

growsL : ∀ {Γ B} (pre : List (St Γ B)) {s s′ : St Γ B} (post : List (St Γ B)) → Grows s s′
       → ∀ i p → ReachL i p (pre ++ s ∷ post) → ReachL i p (pre ++ s′ ∷ post)
growsL []        post g zero    p r = g p r
growsL []        post g (suc i) p r = r
growsL (x ∷ pre) post g zero    p r = r
growsL (x ∷ pre) post g (suc i) p r = growsL pre post g i p r

reachL-snoc : ∀ {Γ B} (ls : List (St Γ B)) (x : St Γ B) i p → ReachL i p ls → ReachL i p (ls ++ [ x ])
reachL-snoc (s ∷ ls) x zero    p r = r
reachL-snoc (s ∷ ls) x (suc i) p r = reachL-snoc ls x i p r

atL : ∀ {Γ B} (pre : List (St Γ B)) {s : St Γ B} {post p} → Reach p s → ReachL (length pre) p (pre ++ s ∷ post)
atL []        r = r
atL (_ ∷ pre) r = atL pre r

grows-plug : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → Grows s s′ → Grows (plug c s) (plug c s′)
grows-plug top                             g = g
grows-plug (inMap f c)                     g = grows-plug c (one-grow g)
grows-plug (inScan f z c)                  g = grows-plug c (one-grow g)
grows-plug (inCut l a c)                   g = grows-plug c (one-grow g)
grows-plug (inLn b c)                      g = grows-plug c (one-grow g)
grows-plug (inTake i q ph c)               g = grows-plug c (one-grow g)
grows-plug (inOuter op f d n ls c)         g = grows-plug c (fl-grow g λ i p r → r)
grows-plug (inLanes op f d n o pre post c) g = grows-plug c (fl-grow (λ p r → r) (growsL pre post g))
grows-plug (inSrc k b c)                   g = grows-plug c (two-grow g λ p r → r)
grows-plug (inBody k o c)                  g = grows-plug c (two-grow (λ p r → r) g)

-- The hole's own path is reached.
reach-++ : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) q → Reach q s → Reach (dirs c ++ q) (plug c s)
reach-++ top                             s q r = r
reach-++ (inMap f c)                     s q r = re (dirs c) 0 q (reach-++ c (mapS f s) (0 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (mapS f s))) (sym (++-assoc xs [ d ] q))
reach-++ (inScan f z c)                  s q r = re (dirs c) 0 q (reach-++ c (scanS f z s) (0 ∷ q) r)
  where re = λ xs d q → subst (λ w → Reach w (plug c (scanS f z s))) (sym (++-assoc xs [ d ] q))
reach-++ (inCut l a c)                   s q r = re (dirs c) 0 q (reach-++ c (cutS l a s) (0 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (cutS l a s))) (sym (++-assoc xs [ d ] q))
reach-++ (inLn b c)                      s q r = re (dirs c) 0 q (reach-++ c (lnS b s) (0 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (lnS b s))) (sym (++-assoc xs [ d ] q))
reach-++ (inTake i p ph c)               s q r = re (dirs c) 0 q (reach-++ c (takeS i p ph s) (0 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (takeS i p ph s))) (sym (++-assoc xs [ d ] q))
reach-++ (inOuter op f d n ls c)         s q r = re (dirs c) 0 q (reach-++ c (flatS op f d n s ls) (0 ∷ q) r)
  where re = λ xs e q → subst (λ z → Reach z (plug c (flatS op f d n s ls))) (sym (++-assoc xs [ e ] q))
reach-++ (inLanes op f d n o pre post c) s q r =
  re (dirs c) (suc (length pre)) q (reach-++ c (flatS op f d n o (pre ++ s ∷ post)) (suc (length pre) ∷ q) (atL pre r))
  where re = λ xs e q → subst (λ z → Reach z (plug c (flatS op f d n o (pre ++ s ∷ post)))) (sym (++-assoc xs [ e ] q))
reach-++ (inSrc k b c)                   s q r = re (dirs c) 0 q (reach-++ c (connS k s b) (0 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (connS k s b))) (sym (++-assoc xs [ d ] q))
reach-++ (inBody k o c)                  s q r = re (dirs c) 1 q (reach-++ c (connS k o s) (1 ∷ q) r)
  where re = λ xs d q → subst (λ z → Reach z (plug c (connS k o s))) (sym (++-assoc xs [ d ] q))

reach-dirs : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Reach (dirs c) (plug c s)
reach-dirs c s = subst (λ z → Reach z (plug c s)) (++-identityʳ (dirs c)) (reach-++ c s [] (reach-nil s))

------------------------------------------------------------------------
-- Every binder reaches its joiners

Joined : ∀ {Γ X B} → CS X → St Γ X → St (X ∷ Γ) B → Set
Joined k o b = All (λ j → Two (proj₁ j) o b) (CS.subs k)
             × All (λ f → All (λ j → Two (proj₁ j) o b) (proj₂ f)) (CS.feeds k)

joined-grow : ∀ {Γ X B} (k : CS X) {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} → Grows o o′ → Grows b b′ → Joined k o b → Joined k o′ b′
joined-grow k g h (js , fs) = mapᴬ (λ {j} → two-grow g h (proj₁ j)) js , mapᴬ (mapᴬ (λ {j} → two-grow g h (proj₁ j))) fs

mutual
  Good : ∀ {Γ A} → St Γ A → Set
  Good (pend o)              = ⊤
  Good (ofS q i xs)          = ⊤
  Good doneS                 = ⊤
  Good (joinS j g x)         = ⊤
  Good (mapS f s)            = Good s
  Good (scanS f z s)         = Good s
  Good (cutS l a s)          = Good s
  Good (lnS b s)             = Good s
  Good (takeS i q ph s)      = Good s
  Good (flatS op f d n o ls) = Good o × GoodL ls
  Good (connS k o b)         = Good o × Good b × Joined k o b

  GoodL : ∀ {Γ B} → List (St Γ B) → Set
  GoodL []       = ⊤
  GoodL (s ∷ ls) = Good s × GoodL ls

goodL-mid : ∀ {Γ B} (pre : List (St Γ B)) {s s′ : St Γ B} post → (Good s → Good s′) → GoodL (pre ++ s ∷ post) → GoodL (pre ++ s′ ∷ post)
goodL-mid []        post h (g , gl) = h g , gl
goodL-mid (x ∷ pre) post h (g , gl) = g , goodL-mid pre post h gl

goodL-at : ∀ {Γ B} (pre : List (St Γ B)) {s : St Γ B} post → GoodL (pre ++ s ∷ post) → Good s
goodL-at []        post (g , gl) = g
goodL-at (x ∷ pre) post (g , gl) = goodL-at pre post gl

goodL-snoc : ∀ {Γ B} (ls : List (St Γ B)) {x : St Γ B} → GoodL ls → Good x → GoodL (ls ++ [ x ])
goodL-snoc []       gl       gx = gx , tt
goodL-snoc (s ∷ ls) (g , gl) gx = g , goodL-snoc ls gl gx

-- A rewrite of the hole that grows it and keeps it good keeps the whole tree good.
good-plug : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → Grows s s′ → (Good s → Good s′) → Good (plug c s) → Good (plug c s′)
good-plug top                             g h = h
good-plug (inMap f c)                     g h = good-plug c (one-grow g) h
good-plug (inScan f z c)                  g h = good-plug c (one-grow g) h
good-plug (inCut l a c)                   g h = good-plug c (one-grow g) h
good-plug (inLn b c)                      g h = good-plug c (one-grow g) h
good-plug (inTake i q ph c)               g h = good-plug c (one-grow g) h
good-plug (inOuter op f d n ls c)         g h = good-plug c (fl-grow g λ i p r → r) λ (g₀ , gl) → h g₀ , gl
good-plug (inLanes op f d n o pre post c) g h = good-plug c (fl-grow (λ p r → r) (growsL pre post g)) λ (g₀ , gl) → g₀ , goodL-mid pre post h gl
good-plug (inSrc k b c)                   g h = good-plug c (two-grow g λ p r → r) λ (g₀ , gb , jd) → h g₀ , gb , joined-grow k g (λ p r → r) jd
good-plug (inBody k o c)                  g h = good-plug c (two-grow (λ p r → r) g) λ (g₀ , gb , jd) → g₀ , h gb , joined-grow k (λ p r → r) g jd

good-hole : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good (plug c s) → Good s
good-hole top                             s g = g
good-hole (inMap f c)                     s g = good-hole c (mapS f s) g
good-hole (inScan f z c)                  s g = good-hole c (scanS f z s) g
good-hole (inCut l a c)                   s g = good-hole c (cutS l a s) g
good-hole (inLn b c)                      s g = good-hole c (lnS b s) g
good-hole (inTake i q ph c)               s g = good-hole c (takeS i q ph s) g
good-hole (inOuter op f d n ls c)         s g = proj₁ (good-hole c (flatS op f d n s ls) g)
good-hole (inLanes op f d n o pre post c) s g = goodL-at pre post (proj₂ (good-hole c (flatS op f d n o (pre ++ s ∷ post)) g))
good-hole (inSrc k b c)                   s g = proj₁ (good-hole c (connS k s b) g)
good-hole (inBody k o c)                  s g = proj₁ (proj₂ (good-hole c (connS k o s) g))

------------------------------------------------------------------------
-- Unsubscribing, ending a lane: the shape kept

idk : ∀ {Γ A} (s : St Γ A) → Grows s s × (Good s → Good s)
idk s = (λ p r → r) , λ g → g

mutual
  unsub-ok : ∀ {Γ A} (s : St Γ A) → Grows s (unsub s) × (Good s → Good (unsub s))
  unsub-ok (pend o)              = idk (pend o)
  unsub-ok (ofS q i xs)          = (λ p r → r) , λ g → g
  unsub-ok doneS                 = (λ p r → r) , λ g → g
  unsub-ok (cutS l a s)          = idk (cutS l a s)
  unsub-ok (lnS b s)             = idk (lnS b s)
  unsub-ok (joinS j g x)         = idk (joinS j g x)
  unsub-ok (mapS f s)            = one-grow (proj₁ (unsub-ok s)) , proj₂ (unsub-ok s)
  unsub-ok (scanS f z s)         = one-grow (proj₁ (unsub-ok s)) , proj₂ (unsub-ok s)
  unsub-ok (takeS i q ph s)      = one-grow (proj₁ (cut-ok s)) , proj₂ (cut-ok s)
  unsub-ok (flatS op f d n o ls) =
    fl-grow (proj₁ (cut-ok o)) (proj₁ (killAll-ok ls)) , λ (g₀ , gl) → proj₂ (cut-ok o) g₀ , proj₂ (killAll-ok ls) gl
  unsub-ok (connS k o b)         =
    two-grow (proj₁ (unsub-ok o)) (proj₁ (unsub-ok b)) ,
    λ (g₀ , gb , jd) → proj₂ (unsub-ok o) g₀ , proj₂ (unsub-ok b) gb , joined-grow k (proj₁ (unsub-ok o)) (proj₁ (unsub-ok b)) jd

  cut-ok : ∀ {Γ A} (s : St Γ A) → Grows s (cut s) × (Good s → Good (cut s))
  cut-ok (cutS l true s)       = one-grow (proj₁ (unsub-ok s)) , proj₂ (unsub-ok s)
  cut-ok (cutS l false s)      = idk (cutS l false s)
  cut-ok (pend o)              = idk (pend o)
  cut-ok (ofS q i xs)          = (λ p r → r) , λ g → g
  cut-ok doneS                 = (λ p r → r) , λ g → g
  cut-ok (joinS j g x)         = idk (joinS j g x)
  cut-ok (mapS f s)            = idk (mapS f s)
  cut-ok (scanS f z s)         = idk (scanS f z s)
  cut-ok (lnS b s)             = idk (lnS b s)
  cut-ok (takeS i q ph s)      = idk (takeS i q ph s)
  cut-ok (flatS op f d n o ls) = idk (flatS op f d n o ls)
  cut-ok (connS k o b)         = idk (connS k o b)

  killAll-ok : ∀ {Γ B} (ls : List (St Γ B)) → (∀ i p → ReachL i p ls → ReachL i p (killAll ls)) × (GoodL ls → GoodL (killAll ls))
  killAll-ok []                       = (λ i p ()) , λ g → g
  killAll-ok (lnS true s ∷ ls)        = head (lnS true s) (lnS false (cut s)) (one-grow (proj₁ (cut-ok s))) (proj₂ (cut-ok s)) ls (killAll-ok ls)
  killAll-ok (lnS false s ∷ ls)       = kept (lnS false s) ls (killAll-ok ls)
  killAll-ok (pend o ∷ ls)            = kept (pend o) ls (killAll-ok ls)
  killAll-ok (ofS q i xs ∷ ls)        = kept (ofS q i xs) ls (killAll-ok ls)
  killAll-ok (doneS ∷ ls)             = kept doneS ls (killAll-ok ls)
  killAll-ok (joinS j g x ∷ ls)       = kept (joinS j g x) ls (killAll-ok ls)
  killAll-ok (mapS f s ∷ ls)          = kept (mapS f s) ls (killAll-ok ls)
  killAll-ok (scanS f z s ∷ ls)       = kept (scanS f z s) ls (killAll-ok ls)
  killAll-ok (cutS l a s ∷ ls)        = kept (cutS l a s) ls (killAll-ok ls)
  killAll-ok (takeS i q ph s ∷ ls)    = kept (takeS i q ph s) ls (killAll-ok ls)
  killAll-ok (flatS op f d n o l ∷ ls) = kept (flatS op f d n o l) ls (killAll-ok ls)
  killAll-ok (connS k o b ∷ ls)       = kept (connS k o b) ls (killAll-ok ls)

  -- the head rewritten, the rest killed
  head : ∀ {Γ B} (x x′ : St Γ B) → Grows x x′ → (Good x → Good x′) → (ls : List (St Γ B)) {ls′ : List (St Γ B)}
       → (∀ i p → ReachL i p ls → ReachL i p ls′) × (GoodL ls → GoodL ls′)
       → (∀ i p → ReachL i p (x ∷ ls) → ReachL i p (x′ ∷ ls′)) × (GoodL (x ∷ ls) → GoodL (x′ ∷ ls′))
  head x x′ g h ls (gl , hl) = (λ { zero p r → g p r ; (suc i) p r → gl i p r }) , λ (gx , gs) → h gx , hl gs

  kept : ∀ {Γ B} (x : St Γ B) (ls : List (St Γ B)) {ls′ : List (St Γ B)}
       → (∀ i p → ReachL i p ls → ReachL i p ls′) × (GoodL ls → GoodL ls′)
       → (∀ i p → ReachL i p (x ∷ ls) → ReachL i p (x ∷ ls′)) × (GoodL (x ∷ ls) → GoodL (x ∷ ls′))
  kept x = head x x (λ p r → r) (λ g → g)

ended-ok : ∀ {Γ B} (s : St Γ B) → Grows s (ended s) × (Good s → Good (ended s))
ended-ok (lnS b (cutS l a s))       = one-grow (λ p r → r) , λ g → g
ended-ok (lnS b (pend o))           = idk (lnS b (pend o))
ended-ok (lnS b (ofS q i xs))       = idk (lnS b (ofS q i xs))
ended-ok (lnS b doneS)              = idk (lnS b doneS)
ended-ok (lnS b (joinS j g x))      = idk (lnS b (joinS j g x))
ended-ok (lnS b (mapS f s))         = idk (lnS b (mapS f s))
ended-ok (lnS b (scanS f z s))      = idk (lnS b (scanS f z s))
ended-ok (lnS b (lnS b′ s))         = idk (lnS b (lnS b′ s))
ended-ok (lnS b (takeS i q ph s))   = idk (lnS b (takeS i q ph s))
ended-ok (lnS b (flatS op f d n o ls)) = idk (lnS b (flatS op f d n o ls))
ended-ok (lnS b (connS k o b′))     = idk (lnS b (connS k o b′))
ended-ok (pend o)                   = idk (pend o)
ended-ok (ofS q i xs)               = (λ p r → r) , λ g → g
ended-ok doneS                      = (λ p r → r) , λ g → g
ended-ok (joinS j g x)              = idk (joinS j g x)
ended-ok (mapS f s)                 = idk (mapS f s)
ended-ok (scanS f z s)              = idk (scanS f z s)
ended-ok (cutS l a s)               = idk (cutS l a s)
ended-ok (takeS i q ph s)           = idk (takeS i q ph s)
ended-ok (flatS op f d n o ls)      = idk (flatS op f d n o ls)
ended-ok (connS k o b)              = idk (connS k o b)

------------------------------------------------------------------------
-- Moving the focus: a reached path lands, and the tree is kept

data ⊥₁ : Set₁ where


PickLands : ∀ {Γ B} → List ℕ → List (St Γ B) → List (St Γ B) → Maybe (List (St Γ B) × St Γ B × List (St Γ B)) → Set₁
PickLands p pre ls (just (pre′ , s , post)) = Reach p s × pre′ ++ s ∷ post ≡ pre ++ ls
PickLands p pre ls nothing                  = ⊥₁

pick-lands : ∀ {Γ B} i p (pre ls : List (St Γ B)) → ReachL i p ls → PickLands p pre ls (pickL i pre ls)
pick-lands zero    p pre (s ∷ post) r = r , refl
pick-lands (suc i) p pre (s ∷ post) r with pickL i (pre ++ [ s ]) post | pick-lands i p (pre ++ [ s ]) post r
... | just (pre′ , x , post′) | (r′ , e) = r′ , trans e (++-assoc pre [ s ] post)

Lands : ∀ {R Γ A} → List ℕ → Ctx R Γ A → St Γ A → Maybe (Focus R) → Set₁
Lands p c s (just (_ , _ , c′ , s′)) = Reach p s′ × plug c′ s′ ≡ plug c s
Lands p c s nothing                  = ⊥₁

down-lands : ∀ {R Γ A} i p (c : Ctx R Γ A) (s : St Γ A) → Reach (i ∷ p) s → Lands p c s (down i c s)
down-lands i       p c (pend o)              ()
down-lands i       p c (ofS q j xs)          ()
down-lands i       p c doneS                 ()
down-lands i       p c (joinS j g x)         ()
down-lands zero    p c (mapS f s)            r = r , refl
down-lands zero    p c (scanS f z s)         r = r , refl
down-lands zero    p c (cutS l a s)          r = r , refl
down-lands zero    p c (lnS b s)             r = r , refl
down-lands zero    p c (takeS i q ph s)      r = r , refl
down-lands zero    p c (flatS op f d n o ls) r = r , refl
down-lands zero    p c (connS k o b)         r = r , refl
down-lands (suc i) p c (mapS f s)            ()
down-lands (suc i) p c (scanS f z s)         ()
down-lands (suc i) p c (cutS l a s)          ()
down-lands (suc i) p c (lnS b s)             ()
down-lands (suc i) p c (takeS j q ph s)      ()
down-lands (suc zero) p c (connS k o b)      r = r , refl
down-lands (suc (suc i)) p c (connS k o b)   ()
down-lands (suc zero) p c (flatS op f d n o ls) r with pickL zero [] ls | pick-lands zero p [] ls r
... | just (pre , s , post) | (r′ , e) = r′ , cong (λ L → plug c (flatS op f d n o L)) e
down-lands (suc (suc i)) p c (flatS op f d n o ls) r with pickL (suc i) [] ls | pick-lands (suc i) p [] ls r
... | just (pre , s , post) | (r′ , e) = r′ , cong (λ L → plug c (flatS op f d n o L)) e

Landed : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Maybe (Focus R) → Set₁
Landed c s (just (_ , _ , c′ , s′)) = plug c′ s′ ≡ plug c s
Landed c s nothing                  = ⊥₁

-- A reached path never misses.
downs-lands : ∀ {R Γ A} p (c : Ctx R Γ A) (s : St Γ A) → Reach p s → Landed c s (downs p c s)
downs-lands []      c s r = refl
downs-lands (i ∷ p) c s r with down i c s | down-lands i p c s r
... | just (_ , _ , c′ , s′) | (r′ , e) = along (downs p c′ s′) (downs-lands p c′ s′ r′) e
  where
    along : ∀ m → Landed c′ s′ m → plug c′ s′ ≡ plug c s → Landed c s m
    along (just _) e₁ e₂ = trans e₁ e₂

------------------------------------------------------------------------
-- The invariant: every job reached from the root, every binder good

AllR : ∀ {R} → St [] R → List Job → Set
AllR t rs = All (λ j → Reach (proj₁ j) t) rs

V : ∀ {R Γ A} → Ctx R Γ A → St Γ A → List Job → Set
V c s rs = AllR (plug c s) rs × Good (plug c s)

Valid : ∀ {R} → Conf R → Set
Valid k = V (Conf.ctx k) (Conf.foc k) (Conf.rets k)

hole : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} {rs} → Grows s s′ → (Good s → Good s′) → V c s rs → V c s′ rs
hole c g h (a , gd) = mapᴬ (λ {j} → grows-plug c g (proj₁ j)) a , good-plug c g h gd

same : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} {rs} → (∀ p → Reach p s → Reach p s′) → (Good s → Good s′) → V c s rs → V c s′ rs
same = hole

push : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) {rs} t p → V c s rs → V c s ((dirs c , t , p) ∷ rs)
push c s t p (a , gd) = reach-dirs c s ∷ a , gd

moved : ∀ {R} {t t′ : St [] R} {rs} → t′ ≡ t → AllR t rs × Good t → AllR t′ rs × Good t′
moved e v = subst (λ z → AllR z _ × Good z) (sym e) v

leaf : ∀ {R Γ A} (c : Ctx R Γ A) (o : PObs Γ A) (s : St Γ A) {rs} → Good s → V c (pend o) rs → V c s rs
leaf c o s gs = hole c (from-leaf s) (λ _ → gs)

------------------------------------------------------------------------
-- Joining: only the binder's record changes

joinUp-ok : ∀ {R Γ A X} j (c : Ctx R Γ A) (x : X ∈ Γ) acc (s : St Γ A) {rs} → Reach acc s → V c s rs → V (proj₂ (joinUp j c x acc)) s rs
joinUp-ok j top                             () acc s r v
joinUp-ok j (inMap f c)                     x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (mapS f s) r v
... | b , c″ | w = w
joinUp-ok j (inScan f z c)                  x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (scanS f z s) r v
... | b , c″ | w = w
joinUp-ok j (inCut l a c)                   x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (cutS l a s) r v
... | b , c″ | w = w
joinUp-ok j (inLn l c)                      x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (lnS l s) r v
... | b , c″ | w = w
joinUp-ok j (inTake i p ph c)               x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (takeS i p ph s) r v
... | b , c″ | w = w
joinUp-ok j (inOuter op f d n ls c)         x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (flatS op f d n s ls) r v
... | b , c″ | w = w
joinUp-ok j (inLanes op f d n o pre post c) x acc s r v
  with joinUp j c x (suc (length pre) ∷ acc) | joinUp-ok j c x (suc (length pre) ∷ acc) (flatS op f d n o (pre ++ s ∷ post)) (atL pre r) v
... | b , c″ | w = w
joinUp-ok j (inSrc k b′ c)                  x acc s r v with joinUp j c x (0 ∷ acc) | joinUp-ok j c x (0 ∷ acc) (connS k s b′) r v
... | b , c″ | w = w
joinUp-ok j (inBody k o c)            (there x) acc s r v with joinUp j c x (1 ∷ acc) | joinUp-ok j c x (1 ∷ acc) (connS k o s) r v
... | b , c″ | w = w
joinUp-ok j (inBody k o c)          (here refl) acc s r v with CS.closed k
... | true  = v
... | false = hole c (λ p r → r) (λ (g₀ , gb , js , fs) → g₀ , gb , ++⁺ js (r ∷ []) , fs) v

------------------------------------------------------------------------
-- Each part of a step

begin-ok : ∀ {R Γ A} (c : Ctx R Γ A) (o : PObs Γ A) p rs → V c (pend o) rs → Valid (begin c o p rs)
begin-ok c (cold x)          p rs v = leaf c _ doneS tt v
begin-ok c empty             p rs v = leaf c _ doneS tt v
begin-ok c (of xs)           p rs v = leaf c _ (ofS p 0 xs) tt v
begin-ok c (map f s)         p rs v = leaf c _ (mapS f (pend s)) tt v
begin-ok c (scan f z s)      p rs v = leaf c _ (scanS f z (pend s)) tt v
begin-ok c (takeWhile i q s) p rs v =
  push (inCut true false (inTake i q running c)) (pend s) att p (leaf c _ (takeS i q running (cutS true false (pend s))) tt v)
begin-ok c (flatMap op f s)  p rs v =
  push (inCut true false (inOuter op f false 0 [] c)) (pend s) att p (leaf c _ (flatS op f false 0 (cutS true false (pend s)) []) (tt , tt) v)
begin-ok c (connect s b)     p rs v =
  push c (connS (cs false [] [] false true false) (pend s) (pend b)) attBody p (leaf c _ _ (tt , tt , [] , []) v)
begin-ok c (connected x)     p rs v
  with joinUp p c x [] | joinUp-ok p c x [] doneS tt (leaf c _ doneS tt v) | joinUp-ok p c x [] (joinS p true x) tt (leaf c _ (joinS p true x) tt v)
... | true  , c′ | w | _ = w
... | false , c′ | _ | w = w
begin-ok c (defer l)         p rs v = leaf c _ (pend (Later.force l)) tt v

start-ok : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PObs Γ B) d n o ls a p rs {d₀ n₀}
         → V c (flatS op f d₀ n₀ o ls) rs → Valid (start c op f d n o ls a p rs)
start-ok c op f d n o ls a p rs v with closed c
... | true  = same c (λ p r → r) (λ g → g) v
... | false =
  push (inCut true false (inLn true (inLanes op f d (suc n) o ls [] c))) (pend (f a)) att (p ⊕ [ ix 1 ])
    (hole c (fl-grow (λ p r → r) (reachL-snoc ls _)) (λ (g₀ , gl) → g₀ , goodL-snoc ls gl tt) v)

admit-ok : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PObs Γ B) d n o ls a p rs → V c (flatS op f d n o ls) rs → Valid (admit c op f d n o ls a p rs)
admit-ok c (mergeᶠ nothing)  f d n o ls a p rs v = start-ok c _ f d n o ls a p rs v
admit-ok c (mergeᶠ (just m)) f d n o ls a p rs v = v
admit-ok c switchᶠ           f d n o ls a p rs v =
  start-ok c switchᶠ f d 0 o (killAll ls) a p rs {d} {n} (hole c (fl-grow (λ p r → r) (proj₁ (killAll-ok ls))) (λ (g₀ , gl) → g₀ , proj₂ (killAll-ok ls) gl) v)
admit-ok c exhaustᶠ          f d n o ls a p rs v with n ≡ᵇ 0
... | true  = start-ok c exhaustᶠ f d n o ls a p rs v
... | false = v

rise-ok : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) e p rs → V c s rs → Valid (proj₁ (rise c s e p rs))
rise-ok top                             s e      p rs v = v
rise-ok (inMap f c)                     s e      p rs v = v
rise-ok (inScan f z c)                  s (nx a) p rs v = same c (λ p r → r) (λ g → g) v
rise-ok (inScan f z c)                  s cp     p rs v = v
rise-ok (inCut l a c)                   s e      p rs v = v
rise-ok (inLn b c)                      s e      p rs v = v
rise-ok (inTake i q ph c)               s (nx a) p rs v with q a | i
... | true  | _     = v
... | false | true  = push c (takeS true q oweCp s) owed p (same c (λ p r → r) (λ g → g) v)
... | false | false = push c (takeS false q oweCut s) owed p (same c (λ p r → r) (λ g → g) v)
rise-ok (inTake i q ph c)               s cp     p rs v = v
rise-ok (inOuter op f d n ls c)         s (nx a) p rs v = admit-ok c op f d n s ls a p rs v
rise-ok (inOuter op f d n ls c)         s cp     p rs v = same c (λ p r → r) (λ g → g) v
rise-ok (inLanes op f d n o pre post c) s (nx b) p rs v = v
rise-ok (inLanes op f d n o pre post c) s cp     p rs v =
  hole c (fl-grow (λ p r → r) (growsL pre post (proj₁ (ended-ok s)))) (λ (g₀ , gl) → g₀ , goodL-mid pre post (proj₂ (ended-ok s)) gl) v
rise-ok (inSrc k b c)                   s (nx a) p rs v = same c (λ p r → r) (λ (g₀ , gb , js , fs) → g₀ , gb , js , js ∷ fs) v
rise-ok (inSrc k b c)                   s cp     p rs v = same c (λ p r → r) (λ (g₀ , gb , js , fs) → g₀ , gb , js , js ∷ fs) v
rise-ok (inBody k o c)                  s (nx b) p rs v = v
rise-ok (inBody k o c)                  s cp     p rs v = push c (connS k o s) owed p v

feedOn-ok : ∀ {R Γ X B} (c : Ctx R Γ B) (k : CS X) o b p rs → V c (connS k o b) rs → Valid (feedOn c k o b p rs)
feedOn-ok c k o b p rs (a , g) with good-hole c (connS k o b) g
... | (g₀ , gb , js , fs) with CS.feeds k | fs
...   | [] | _ = a , g
...   | (e , []) ∷ fs′ | _ ∷ fs″ = same c (λ p r → r) (λ _ → g₀ , gb , js , fs″) (a , g)
...   | (e , (q , j) ∷ ps) ∷ fs′ | (r ∷ rs′) ∷ fs″
  with downs q c (connS (record k { feeds = (e , ps) ∷ fs′ }) o b) | downs-lands q c (connS (record k { feeds = (e , ps) ∷ fs′ }) o b) r
...     | just (_ , _ , c′ , s′) | e′ =
  moved e′ (push c (connS (record k { feeds = (e , ps) ∷ fs′ }) o b) go p (same c (λ p r → r) (λ _ → g₀ , gb , js , rs′ ∷ fs″) (a , g)))

resume-ok : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) t p rs → V c s rs → Valid (resume c s t p rs)
resume-ok c (ofS q i xs) go p rs v with closed c | xs
... | true  | _       = same c (λ p r → r) (λ _ → tt) v
... | false | []      = same c (λ p r → r) (λ _ → tt) v
... | false | x ∷ xs′ = push c (ofS q (suc i) xs′) go p (same c (λ p r → r) (λ _ → tt) v)
resume-ok c (cutS true a s)  att p rs v = same c (λ p r → r) (λ g → g) v
resume-ok c (cutS false a s) att p rs v = hole c (one-grow (proj₁ (unsub-ok s))) (proj₂ (unsub-ok s)) v
resume-ok c (takeS i q oweCp s) owed p rs v = push c (takeS i q oweCut s) owed p (same c (λ p r → r) (λ g → g) v)
resume-ok c (takeS i q oweCut s) owed p rs v = hole c (one-grow (proj₁ (cut-ok s))) (proj₂ (cut-ok s)) v
resume-ok c (connS k o b) go p rs v = feedOn-ok c k o b p rs v
resume-ok c (connS k o b) attBody p rs v = push c (connS (record k { bodyAtt = true }) o b) att (p ⊕ [ ix 1 ]) (same c (λ p r → r) (λ g → g) v)
resume-ok c (connS k o b) att p rs v with CS.srcLive k
... | true  = same c (λ p r → r) (λ g → g) v
... | false = hole c (two-grow (proj₁ (unsub-ok o)) (λ p r → r))
                (λ (g₀ , gb , jd) → proj₂ (unsub-ok o) g₀ , gb , joined-grow k (proj₁ (unsub-ok o)) (λ p r → r) jd) v
resume-ok c (connS k o b) owed p rs v with CS.srcAtt k
... | true  = hole c (two-grow (proj₁ (unsub-ok o)) (λ p r → r))
                (λ (g₀ , gb , jd) → proj₂ (unsub-ok o) g₀ , gb , joined-grow k (proj₁ (unsub-ok o)) (λ p r → r) jd) v
... | false = same c (λ p r → r) (λ g → g) v
resume-ok c (joinS j true x) go p rs v with fedUp c x
... | just e  = v
... | nothing = v
resume-ok c (pend o)              t p rs v = v
resume-ok c doneS                 t p rs v = v
resume-ok c (mapS f s)            t p rs v = v
resume-ok c (scanS f z s)         t p rs v = v
resume-ok c (lnS b s)             t p rs v = v
resume-ok c (flatS op f d n o ls) t p rs v = v
resume-ok c (ofS q i xs) att     p rs v = v
resume-ok c (ofS q i xs) attBody p rs v = v
resume-ok c (ofS q i xs) owed    p rs v = v
resume-ok c (cutS l a s) go      p rs v = v
resume-ok c (cutS l a s) attBody p rs v = v
resume-ok c (cutS l a s) owed    p rs v = v
resume-ok c (takeS i q running s) t p rs v = v
resume-ok c (takeS i q oweCp s) go      p rs v = v
resume-ok c (takeS i q oweCp s) att     p rs v = v
resume-ok c (takeS i q oweCp s) attBody p rs v = v
resume-ok c (takeS i q oweCut s) go      p rs v = v
resume-ok c (takeS i q oweCut s) att     p rs v = v
resume-ok c (takeS i q oweCut s) attBody p rs v = v
resume-ok c (joinS j true x) att     p rs v = v
resume-ok c (joinS j true x) attBody p rs v = v
resume-ok c (joinS j true x) owed    p rs v = v
resume-ok c (joinS j false x) t p rs v = v

------------------------------------------------------------------------
-- THE INVARIANT, ACROSS EVERY STEP; and the machine's `nothing` arms
-- dead: a job resumed, or a joiner fed, always finds its node.

load-ok : ∀ {R} (o : PObs [] R) → Valid (load o)
load-ok o = [] , tt

stepAt-ok : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) m p rs → V c s rs → Valid (proj₁ (stepAt c s m p rs))
stepAt-ok c s (resuming t) p rs v = resume-ok c s t p rs v
stepAt-ok c s (rising e)   p rs v = rise-ok c s e p rs v
stepAt-ok c (pend o)              subscribing p rs v = begin-ok c o p rs v
stepAt-ok c (ofS q i xs)          subscribing p rs v = v
stepAt-ok c doneS                 subscribing p rs v = v
stepAt-ok c (joinS j g x)         subscribing p rs v = v
stepAt-ok c (mapS f s)            subscribing p rs v = v
stepAt-ok c (scanS f z s)         subscribing p rs v = v
stepAt-ok c (cutS l a s)          subscribing p rs v = v
stepAt-ok c (lnS b s)             subscribing p rs v = v
stepAt-ok c (takeS i q ph s)      subscribing p rs v = v
stepAt-ok c (flatS op f d n o ls) subscribing p rs v = v
stepAt-ok c (connS k o b)         subscribing p rs v = v
stepAt-ok c s absorbed p [] v = v
stepAt-ok c s absorbed p ((q , t , p′) ∷ rs) (r ∷ a , g) with downs q top (plug c s) | downs-lands q top (plug c s) r
... | just (_ , _ , c′ , s′) | e = moved e (a , g)

step-ok : ∀ {R} (k : Conf R) → Valid k → Valid (proj₁ (step k))
step-ok ⟨ c , s , m , p , rs ⟩ v = stepAt-ok c s m p rs v

-- The `nothing` arm of a resume, dead.
pop-lands : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) p q t p′ rs → Valid ⟨ c , s , absorbed , p , (q , t , p′) ∷ rs ⟩
          → Landed top (plug c s) (downs q top (plug c s))
pop-lands c s p q t p′ rs (r ∷ _ , _) = downs-lands q top (plug c s) r

-- The `nothing` arm of a feed, dead: a joiner a binder is feeding is reached from it.
feed-lands : ∀ {R Γ X B} (c : Ctx R Γ B) (k : CS X) o b {rs} e q j ps fs → V c (connS k o b) rs → CS.feeds k ≡ (e , (q , j) ∷ ps) ∷ fs
           → Landed c (connS (record k { feeds = (e , ps) ∷ fs }) o b) (downs q c (connS (record k { feeds = (e , ps) ∷ fs }) o b))
feed-lands c k o b e q j ps fs (_ , g) eq with good-hole c (connS k o b) g
... | (_ , _ , _ , fd) with subst (All _) eq fd
...   | (r ∷ _) ∷ _ = downs-lands q c _ r
