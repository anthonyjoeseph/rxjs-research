{-# OPTIONS --guardedness #-}

-- NOTHING KEYED UNDER A SKIP NOT YET RUN (`Causal`): at every node, each
-- key it owns or will own (`Fut`: a live cold's whole tape, an of's values
-- and completion to come, a joiner's queue) is aloft (`Aloft⁺`) of every key, owned or to come,
-- of each part racing it.  Read over what is to come, a mark run only
-- takes from what the invariant reads: the tree it leaves is weaker
-- (`_≼_`: each node's keys to come among the old ones, or past one at or
-- above it), and a weaker tree is causal wherever the stronger was
-- (`causal-≼`).  "Under" is what a key's place can cause (`Sown`): two
-- keys are far when nothing the one can lead to is anything the other
-- can, so a mark aloft makes all it will plant aloft (`aloft-out`).
module adequacy.Engine.Causal where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; ʳ++-defn; reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; tabulate)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero) renaming (suc to 1+)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Tree using (Obs; FlatOp)
open import denotation.MonotonicList.Events using (Pos; Timeline; ix; last; emit; stall; close; Frame∞; From∞)
open import operation.Key using (Key; at; after)
open import operation.PureObservable using (module Machine; due; Tape; play; ending; over; rest)
open import adequacy.Engine.Sown using (Sown; Sownᴷ; inside; posᴷ; sown-here; sown-ext; sown-trans)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; CS; cs; Att;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; own;
  Mark; ofM; joinM; attached; attAt; free; cpAt; cutAt; overAt; unsub; cut; killAll; unsubIf; _⊕_)

------------------------------------------------------------------------
-- Keys

-- A key far from a mark's: nothing the key's place can cause is anything
-- the mark's can, nor the place a past mark is past.  A past key causes
-- nothing.
Farᴷ : Key → Key → Set
Farᴷ (at p)    (at q)    = ∀ {y} → Sown p y → Sown q y → ⊥
Farᴷ (at p)    (after q) = Sown p q → ⊥
Farᴷ (after p) h         = ⊤

-- A mark at or under no position a key is at.
Freeᴷ : Key → Key → Set
Freeᴷ k (at r)    = (Σ Pos λ ys → posᴷ k ≡ r ++ ys) → ⊥
Freeᴷ k (after _) = ⊤

-- A place far, all it sows far, and free.
far-out : ∀ {x} k {h} → Farᴷ (at x) k → Sownᴷ x h → Farᴷ h k
far-out (at q)    {at z}    fr s = λ a b → fr (sown-trans s a) b
far-out (after q) {at z}    fr s = λ a → fr (sown-trans s a)
far-out k         {after z} fr s = tt

free-out : ∀ {x} k {h} → Farᴷ (at x) k → Sownᴷ x h → Freeᴷ h k
free-out (at r)    fr s (ys , e) = fr s (subst (Sown r) (sym e) (inside ys))
free-out (after r) fr s          = tt

-- A started cold's tape, one leaf move on: a frame's next value or stall,
-- a close's next frame; a completion delivered, nothing.
advance : ∀ {A} → Tape A → Tape A
advance (play τ u i t (emit a k))  = play τ u (1+ i) t k
advance (play τ u i t (stall k))   = play τ u (1+ i) t (Frame∞.force k)
advance (play τ u i t (close k))   = rest τ (u ++ [ last ]) (From∞.force k)
advance (ending e)                 = over
advance over                       = over

ahead : ∀ {A} → ℕ → Tape A → Tape A
ahead zero   l = l
ahead (1+ n) l = ahead n (advance l)

-- Every key a tape is due at, now or after moves to come.
Tapes : ∀ {A} → Tape A → Key → Set
Tapes l h = Σ ℕ λ n → due (ahead n l) ≡ just h

ahead-over : ∀ {A} n → ahead {A} n over ≡ over
ahead-over zero   = refl
ahead-over (1+ n) = ahead-over n

tapes-over : ∀ {A h} → Tapes {A} over h → ⊥
tapes-over {A} (n , e) = none (trans (sym (cong due (ahead-over {A} n))) e)
  where
    none : ∀ {h} → nothing ≡ just h → ⊥
    none ()

own-tape : ∀ {Γ A} b (l : Tape A) {m h} → (m , h) ∈ own {Γ} {A} (coldS b l) → Tapes l h
own-tape b l i with due l in e
own-tape b l (here refl)  | just k = zero , e
own-tape b l (there ())   | just k
own-tape b l ()           | nothing

ofFut : ℕ → Pos → ∀ {A : Set} → List A → List (Mark × Key)
ofFut i p []       = [ (ofM , at (p ⊕ [ last ])) ]
ofFut i p (_ ∷ xs) = (ofM , at (p ⊕ [ ix i ])) ∷ ofFut (1+ i) p xs

-- What a node will own: a live cold's whole tape, an of's every value
-- and completion to come, a joiner's whole queue; else what it owns.
Fut : ∀ {Γ A} → St Γ A → Key → Set
Fut (coldS true l)   h = Tapes l h
Fut (ofS i p xs)     h = Σ Mark λ m → (m , h) ∈ ofFut i p xs
Fut (joinS j g x ib) h = Σ Mark λ m → (m , h) ∈ map (λ qe → (joinM , at (proj₁ qe))) ib
Fut s                h = Σ Mark λ m → (m , h) ∈ own s

Every : ∀ {Γ A} → (Key → Set) → St Γ A → Set
Every P s = ∀ {h} → Fut s h → P h

own-fut : ∀ {Γ A} (s : St Γ A) {m h} → (m , h) ∈ own s → Fut s h
own-fut (pend o)                    i = _ , i
own-fut {Γ} {A} (coldS true l)      i = own-tape {Γ} {A} true l i
own-fut (coldS false l)             i = _ , i
own-fut (ofS j p [])                i = _ , i
own-fut (ofS j p (_ ∷ _))           (here e) = _ , here e
own-fut (ofS j p (_ ∷ _))           (there ())
own-fut doneS                       i = _ , i
own-fut (mapS f s)                  i = _ , i
own-fut (scanS f z s)               i = _ , i
own-fut (cutS l a s)                i = _ , i
own-fut (lnS b s)                   i = _ , i
own-fut (takeS j q w s)             i = _ , i
own-fut (flatS op f d n q o ls)     i = _ , i
own-fut (connS k o b)               i = _ , i
own-fut (joinS j g x [])            ()
own-fut (joinS j g x ((q , _) ∷ _)) (here e) = _ , here e
own-fut (joinS j g x ((q , _) ∷ _)) (there ())

-- Every key every node of a tree owns.
mutual
  Keysᴬ : ∀ {Γ A} → (Key → Set) → St Γ A → Set
  Keysᴬ P s = All (λ mk → P (proj₂ mk)) (own s) × KidKeys P s

  KidKeys : ∀ {Γ A} → (Key → Set) → St Γ A → Set
  KidKeys P (mapS f s)              = Keysᴬ P s
  KidKeys P (scanS f z s)           = Keysᴬ P s
  KidKeys P (cutS l a s)            = Keysᴬ P s
  KidKeys P (lnS b s)               = Keysᴬ P s
  KidKeys P (takeS i q w s)         = Keysᴬ P s
  KidKeys P (flatS op f d n q o ls) = Keysᴬ P o × LaneKeys P ls
  KidKeys P (connS k o b)           = Keysᴬ P o × Keysᴬ P b
  KidKeys P _                       = ⊤

  LaneKeys : ∀ {Γ A} → (Key → Set) → List (St Γ A) → Set
  LaneKeys P []       = ⊤
  LaneKeys P (s ∷ ls) = Keysᴬ P s × LaneKeys P ls

-- Every key every node of a tree owns or will own.
mutual
  Keys⁺ : ∀ {Γ A} → (Key → Set) → St Γ A → Set
  Keys⁺ P s = Every P s × KidKeys⁺ P s

  KidKeys⁺ : ∀ {Γ A} → (Key → Set) → St Γ A → Set
  KidKeys⁺ P (mapS f s)              = Keys⁺ P s
  KidKeys⁺ P (scanS f z s)           = Keys⁺ P s
  KidKeys⁺ P (cutS l a s)            = Keys⁺ P s
  KidKeys⁺ P (lnS b s)               = Keys⁺ P s
  KidKeys⁺ P (takeS i q w s)         = Keys⁺ P s
  KidKeys⁺ P (flatS op f d n q o ls) = Keys⁺ P o × LaneKeys⁺ P ls
  KidKeys⁺ P (connS k o b)           = Keys⁺ P o × Keys⁺ P b
  KidKeys⁺ P _                       = ⊤

  LaneKeys⁺ : ∀ {Γ A} → (Key → Set) → List (St Γ A) → Set
  LaneKeys⁺ P []       = ⊤
  LaneKeys⁺ P (s ∷ ls) = Keys⁺ P s × LaneKeys⁺ P ls

-- What is to come includes what is owned.
every-own : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → Every P s → All (λ mk → P (proj₂ mk)) (own s)
every-own s a = tabulate (λ i → a (own-fut s i))

mutual
  keys-own : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → Keys⁺ P s → Keysᴬ P s
  keys-own s (a , k) = every-own s a , kids-own s k

  kids-own : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → KidKeys⁺ P s → KidKeys P s
  kids-own (pend o)                k        = tt
  kids-own (coldS b l)             k        = tt
  kids-own (ofS i p xs)            k        = tt
  kids-own doneS                   k        = tt
  kids-own (mapS f s)              k        = keys-own s k
  kids-own (scanS f z s)           k        = keys-own s k
  kids-own (cutS l a s)            k        = keys-own s k
  kids-own (lnS b s)               k        = keys-own s k
  kids-own (takeS i q w s)         k        = keys-own s k
  kids-own (flatS op f d n q o ls) (a , b)  = keys-own o a , lanes-own ls b
  kids-own (connS k o b)           (x , y)  = keys-own o x , keys-own b y
  kids-own (joinS j g x ib)        k        = tt

  lanes-own : ∀ {Γ A} {P : Key → Set} (ls : List (St Γ A)) → LaneKeys⁺ P ls → LaneKeys P ls
  lanes-own []       tt       = tt
  lanes-own (s ∷ ls) (a , as) = keys-own s a , lanes-own ls as

-- What every key `P` holds of, `Q` holds of.
mutual
  keys-map : ∀ {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (s : St Γ A) → Keys⁺ P s → Keys⁺ Q s
  keys-map g s (a , k) = (λ f → g (a f)) , kids-map g s k

  kids-map : ∀ {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (s : St Γ A) → KidKeys⁺ P s → KidKeys⁺ Q s
  kids-map g (pend o)                k       = tt
  kids-map g (coldS b l)             k       = tt
  kids-map g (ofS i p xs)            k       = tt
  kids-map g doneS                   k       = tt
  kids-map g (mapS f s)              k       = keys-map g s k
  kids-map g (scanS f z s)           k       = keys-map g s k
  kids-map g (cutS l a s)            k       = keys-map g s k
  kids-map g (lnS b s)               k       = keys-map g s k
  kids-map g (takeS i q w s)         k       = keys-map g s k
  kids-map g (flatS op f d n q o ls) (a , b) = keys-map g o a , lanes-map g ls b
  kids-map g (connS k o b)           (x , y) = keys-map g o x , keys-map g b y
  kids-map g (joinS j h x ib)        k       = tt

  lanes-map : ∀ {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (ls : List (St Γ A)) → LaneKeys⁺ P ls → LaneKeys⁺ Q ls
  lanes-map g []       tt       = tt
  lanes-map g (s ∷ ls) (a , as) = keys-map g s a , lanes-map g ls as

------------------------------------------------------------------------
-- The invariant

-- Every frame above a node's mark at `k`: every key, owned or to come, of
-- each part racing it, and each connect's and cut's own marks, far from `k`; a
-- body's mark at or under no key of its source.  Of every key, not the
-- race's candidates alone: a mark run hands a part's candidacy to a key
-- no candidate constrained.
Aloft⁺ : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Set
Aloft⁺ k top                                s = ⊤
Aloft⁺ k (inMap f c)                        s = Aloft⁺ k c (mapS f s)
Aloft⁺ k (inScan f z c)                     s = Aloft⁺ k c (scanS f z s)
Aloft⁺ k (inCut l a c)                      s = Every (Farᴷ k) (cutS l a s) × Aloft⁺ k c (cutS l a s)
Aloft⁺ k (inLn b c)                         s = Aloft⁺ k c (lnS b s)
Aloft⁺ k (inTake i q w c)                   s = Aloft⁺ k c (takeS i q w s)
Aloft⁺ k (inOuter op f d n q ls c)          s = LaneKeys⁺ (Farᴷ k) ls × Aloft⁺ k c (flatS op f d n q s ls)
Aloft⁺ k (inLanes op f d n q o pre post c)  s =
  Keys⁺ (Farᴷ k) o × LaneKeys⁺ (Farᴷ k) pre × LaneKeys⁺ (Farᴷ k) post × Aloft⁺ k c (flatS op f d n q o (pre ʳ++ s ∷ post))
Aloft⁺ k (inSrc kk b c)                     s =
  Keys⁺ (Farᴷ k) b × Every (Farᴷ k) (connS kk s b) × Aloft⁺ k c (connS kk s b)
Aloft⁺ k (inBody kk o c)                    s =
  Keys⁺ (Farᴷ k) o × Keys⁺ (Freeᴷ k) o × Every (Farᴷ k) (connS kk o s) × Aloft⁺ k c (connS kk o s)

-- At every node under `c`, every key to come aloft.
mutual
  CausalW : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
  CausalW c s = Every (λ h → Aloft⁺ h c s) s × KidsW c s

  KidsW : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
  KidsW c (mapS f s)              = CausalW (inMap f c) s
  KidsW c (scanS f z s)           = CausalW (inScan f z c) s
  KidsW c (cutS l a s)            = CausalW (inCut l a c) s
  KidsW c (lnS b s)               = CausalW (inLn b c) s
  KidsW c (takeS i q w s)         = CausalW (inTake i q w c) s
  KidsW c (flatS op f d n q o ls) = CausalW (inOuter op f d n q ls c) o × LanesW c op f d n q o [] ls
  KidsW c (connS k o b)           = CausalW (inSrc k b c) o × CausalW (inBody k o c) b
  KidsW c _                       = ⊤

  LanesW : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A
         → List (St Γ B) → List (St Γ B) → Set
  LanesW c op f d n q o pre []         = ⊤
  LanesW c op f d n q o pre (s ∷ post) = CausalW (inLanes op f d n q o pre post c) s × LanesW c op f d n q o (s ∷ pre) post

-- Every node's every key to come is aloft.
Causal : ∀ {R} → St [] R → Set
Causal t = CausalW top t

------------------------------------------------------------------------
-- Down to a node

lanes-skip : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ys acc rest
           → LanesW c op f d n q o acc (ys ++ rest) → LanesW c op f d n q o (ys ʳ++ acc) rest
lanes-skip c op f d n q o []       acc rest w       = w
lanes-skip c op f d n q o (y ∷ ys) acc rest (_ , w) = lanes-skip c op f d n q o ys (y ∷ acc) rest w

lanes-at : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre s post
         → LanesW c op f d n q o [] (pre ʳ++ s ∷ post) → CausalW (inLanes op f d n q o pre post c) s
lanes-at c op f d n q o pre s post w =
  proj₁ (subst (λ a → LanesW c op f d n q o a (s ∷ post)) eq
    (lanes-skip c op f d n q o (reverse pre) [] (s ∷ post) (subst (LanesW c op f d n q o []) (ʳ++-defn pre) w)))
  where
    eq : reverse pre ʳ++ [] ≡ pre
    eq = trans (ʳ++-defn (reverse pre)) (trans (++-identityʳ _) (reverse-involutive pre))

-- A causal tree's node: causal under its context.
walk-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Causal (plug c s) → CausalW c s
walk-at top                               s w = w
walk-at (inMap f c)                       s w = proj₂ (walk-at c (mapS f s) w)
walk-at (inScan f z c)                    s w = proj₂ (walk-at c (scanS f z s) w)
walk-at (inCut l a c)                     s w = proj₂ (walk-at c (cutS l a s) w)
walk-at (inLn b c)                        s w = proj₂ (walk-at c (lnS b s) w)
walk-at (inTake i q w′ c)                 s w = proj₂ (walk-at c (takeS i q w′ s) w)
walk-at (inOuter op f d n q ls c)         s w = proj₁ (proj₂ (walk-at c (flatS op f d n q s ls) w))
walk-at (inLanes op f d n q o pre post c) s w =
  lanes-at c op f d n q o pre s post (proj₂ (proj₂ (walk-at c (flatS op f d n q o (pre ʳ++ s ∷ post)) w)))
walk-at (inSrc kk b c)                    s w = proj₁ (proj₂ (walk-at c (connS kk s b) w))
walk-at (inBody kk o c)                   s w = proj₂ (proj₂ (walk-at c (connS kk o s) w))

-- A causal tree's node's own marks: aloft.
causal-own : ∀ {R} {t : St [] R} → Causal t → ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) {m k} → plug c s ≡ t → (m , k) ∈ own s → Aloft⁺ k c s
causal-own ca c s e i = proj₁ (walk-at c s (subst Causal (sym e) ca)) (own-fut s i)

------------------------------------------------------------------------
-- Keyless

-- No key owned or to come anywhere in a tree.
Void : ∀ {Γ A} → St Γ A → Set
Void = Keys⁺ (λ _ → ⊥)

void-keys : ∀ {Γ A} {P : Key → Set} {s : St Γ A} → Void s → Keys⁺ P s
void-keys {s = s} v = keys-map ⊥-elim s v

-- A keyless tree is causal under any context: it has no mark to raise.
mutual
  void-causal : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Void s → CausalW c s
  void-causal c s (a , k) = (λ f → ⊥-elim (a f)) , void-kids c s k

  void-kids : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → KidKeys⁺ (λ _ → ⊥) s → KidsW c s
  void-kids c (pend o)                k       = tt
  void-kids c (coldS b l)             k       = tt
  void-kids c (ofS i p xs)            k       = tt
  void-kids c doneS                   k       = tt
  void-kids c (mapS f s)              k       = void-causal (inMap f c) s k
  void-kids c (scanS f z s)           k       = void-causal (inScan f z c) s k
  void-kids c (cutS l a s)            k       = void-causal (inCut l a c) s k
  void-kids c (lnS b s)               k       = void-causal (inLn b c) s k
  void-kids c (takeS i q w s)         k       = void-causal (inTake i q w c) s k
  void-kids c (flatS op f d n q o ls) (a , b) = void-causal (inOuter op f d n q ls c) o a , void-lanes c op f d n q o [] ls b
  void-kids c (connS kk o b)          (x , y) = void-causal (inSrc kk b c) o x , void-causal (inBody kk o c) b y
  void-kids c (joinS j g x ib)        k       = tt

  void-lanes : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre ls
             → LaneKeys⁺ (λ _ → ⊥) ls → LanesW c op f d n q o pre ls
  void-lanes c op f d n q o pre []       tt       = tt
  void-lanes c op f d n q o pre (s ∷ ls) (a , as) = void-causal (inLanes op f d n q o pre ls c) s a , void-lanes c op f d n q o (s ∷ pre) ls as

------------------------------------------------------------------------
-- Weaker

-- A key weaker than another: whatever is far from or free of the other,
-- and whatever the other is far from or free of, so is it.
record _≤ᴷ_ (h′ h : Key) : Set where
  field
    farK  : ∀ k → Farᴷ k h → Farᴷ k h′
    freeK : ∀ k → Freeᴷ k h → Freeᴷ k h′
    farM  : ∀ g → Farᴷ h g → Farᴷ h′ g
    freeM : ∀ g → Freeᴷ h g → Freeᴷ h′ g
open _≤ᴷ_

≤ᴷ-refl : ∀ {h} → h ≤ᴷ h
≤ᴷ-refl = record { farK = λ _ x → x ; freeK = λ _ x → x ; farM = λ _ x → x ; freeM = λ _ x → x }

-- Past a position is weaker than at any position at or under it.
after≤at : ∀ q r ys → r ≡ q ++ ys → after q ≤ᴷ at r
after≤at q r ys e = record { farK = fk ; freeK = λ _ _ → tt ; farM = λ _ _ → tt ; freeM = fm }
  where
    fk : ∀ k → Farᴷ k (at r) → Farᴷ k (after q)
    fk (at p)    fr a = fr (subst (Sown p) (sym e) (sown-ext ys a)) (sown-here r)
    fk (after p) fr           = tt
    fm : ∀ g → Freeᴷ (at r) g → Freeᴷ (after q) g
    fm (at p)    fr (zs , e′) = fr (zs ++ ys , trans e (trans (cong (_++ ys) e′) (++-assoc p zs ys)))
    fm (after p) fr           = tt

-- Each key to come of `s′` weaker than one of `s`'s.
record NodeW {Γ Γ′ A A′} (s′ : St Γ′ A′) (s : St Γ A) : Set where
  constructor nodeW
  field back : ∀ {h′} → Fut s′ h′ → Σ Key λ h → Fut s h × h′ ≤ᴷ h
open NodeW

node-all : ∀ {Γ Γ′ A A′} {s′ : St Γ′ A′} {s : St Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → NodeW s′ s
         → Every P s → Every P s′
node-all tr nw a f = tr (proj₂ (proj₂ (back nw f))) (a (proj₁ (proj₂ (back nw f))))

-- A connect's own keys, as its record alone gives them.
record ConnW (kk′ kk : CS) : Set₁ where
  constructor connW
  field conn : ∀ {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} → NodeW (connS kk′ o′ b′) (connS kk o b)
open ConnW

-- A cut's own mark kept, or dropped.
data CutW : Att → Att → Set where
  cut-same : ∀ {a} → CutW a a
  cut-drop : ∀ {a} → CutW attached a

cut-fut : ∀ {Γ A} {l l′ a a′} {s s′ : St Γ A} → CutW a′ a → ∀ {h} → Fut (cutS l′ a′ s′) h → Fut (cutS l a s) h
cut-fut {a = attached}  cut-same f = f
cut-fut {a = attAt p}   cut-same f = f
cut-fut                 cut-drop (_ , ())

-- No children.
Bare : ∀ {Γ A} → St Γ A → Set
Bare (pend o)         = ⊤
Bare (coldS b l)      = ⊤
Bare (ofS i p xs)     = ⊤
Bare doneS            = ⊤
Bare (joinS j g x ib) = ⊤
Bare _                = ⊥

-- A tree weaker than another: node by node, the same children.
mutual
  data _≼_ : ∀ {Γ A} → St Γ A → St Γ A → Set₁ where
    w≼ : ∀ {Γ A} {s′ s : St Γ A} → NodeW s′ s → Kids≼ s′ s → s′ ≼ s

  data Kids≼ : ∀ {Γ A} → St Γ A → St Γ A → Set₁ where
    bare≼ : ∀ {Γ A} {s′ s : St Γ A} → Bare s′ → Kids≼ s′ s
    void≼ : ∀ {Γ A} {s′ s : St Γ A} → Void s′ → Kids≼ s′ s
    map≼  : ∀ {Γ A B} {f f′ : A → B} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (mapS f′ s′) (mapS f s)
    scan≼ : ∀ {Γ A B} {f f′ : B → A → B} {z z′} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (scanS f′ z′ s′) (scanS f z s)
    cut≼  : ∀ {Γ A} {l l′ a a′} {s′ s : St Γ A} → CutW a′ a → s′ ≼ s → Kids≼ (cutS l′ a′ s′) (cutS l a s)
    ln≼   : ∀ {Γ A} {b b′} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (lnS b′ s′) (lnS b s)
    take≼ : ∀ {Γ A} {i i′ q q′ w w′} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (takeS i′ q′ w′ s′) (takeS i q w s)
    flat≼ : ∀ {Γ A B} {op op′} {f f′ : A → Obs Timeline Γ B} {d d′ n n′ q q′} {o′ o : St Γ A} {ls′ ls}
          → o′ ≼ o → Lanes≼ ls′ ls → Kids≼ (flatS op′ f′ d′ n′ q′ o′ ls′) (flatS op f d n q o ls)
    conn≼ : ∀ {Γ X B} {kk kk′} {o′ o : St Γ X} {b′ b : St (X ∷ Γ) B}
          → ConnW kk′ kk → o′ ≼ o → b′ ≼ b → Kids≼ (connS kk′ o′ b′) (connS kk o b)

  data Lanes≼ : ∀ {Γ A} → List (St Γ A) → List (St Γ A) → Set₁ where
    []≼  : ∀ {Γ A} → Lanes≼ {Γ} {A} [] []
    _∷≼_ : ∀ {Γ A} {s′ s : St Γ A} {ls′ ls} → s′ ≼ s → Lanes≼ ls′ ls → Lanes≼ (s′ ∷ ls′) (s ∷ ls)

-- A context weaker than another: frame by frame, each sibling weaker.
data _≼ᶜ_ {R} : ∀ {Γ A} → Ctx R Γ A → Ctx R Γ A → Set₁ where
  top≼   : top ≼ᶜ top
  map≼ᶜ  : ∀ {Γ A B} {f f′ : A → B} {c′ c : Ctx R Γ B} → c′ ≼ᶜ c → inMap f′ c′ ≼ᶜ inMap f c
  scan≼ᶜ : ∀ {Γ A B} {f f′ : B → A → B} {z z′} {c′ c : Ctx R Γ B} → c′ ≼ᶜ c → inScan f′ z′ c′ ≼ᶜ inScan f z c
  cut≼ᶜ  : ∀ {Γ A} {l l′ a a′} {c′ c : Ctx R Γ A} → CutW a′ a → c′ ≼ᶜ c → inCut l′ a′ c′ ≼ᶜ inCut l a c
  ln≼ᶜ   : ∀ {Γ A} {b b′} {c′ c : Ctx R Γ A} → c′ ≼ᶜ c → inLn b′ c′ ≼ᶜ inLn b c
  take≼ᶜ : ∀ {Γ A} {i i′ q q′ w w′} {c′ c : Ctx R Γ A} → c′ ≼ᶜ c → inTake i′ q′ w′ c′ ≼ᶜ inTake i q w c
  outer≼ᶜ : ∀ {Γ A B} {op op′} {f f′ : A → Obs Timeline Γ B} {d d′ n n′ q q′} {ls′ ls} {c′ c : Ctx R Γ B}
          → Lanes≼ ls′ ls → c′ ≼ᶜ c → inOuter op′ f′ d′ n′ q′ ls′ c′ ≼ᶜ inOuter op f d n q ls c
  lanes≼ᶜ : ∀ {Γ A B} {op op′} {f f′ : A → Obs Timeline Γ B} {d d′ n n′ q q′} {o′ o : St Γ A} {pre′ pre post′ post} {c′ c : Ctx R Γ B}
          → o′ ≼ o → Lanes≼ pre′ pre → Lanes≼ post′ post → c′ ≼ᶜ c → inLanes op′ f′ d′ n′ q′ o′ pre′ post′ c′ ≼ᶜ inLanes op f d n q o pre post c
  src≼ᶜ  : ∀ {Γ X B} {kk kk′} {b′ b : St (X ∷ Γ) B} {c′ c : Ctx R Γ B} → ConnW kk′ kk → b′ ≼ b → c′ ≼ᶜ c → inSrc kk′ b′ c′ ≼ᶜ inSrc kk b c
  body≼ᶜ : ∀ {Γ X B} {kk kk′} {o′ o : St Γ X} {c′ c : Ctx R Γ B} → ConnW kk′ kk → o′ ≼ o → c′ ≼ᶜ c → inBody kk′ o′ c′ ≼ᶜ inBody kk o c

------------------------------------------------------------------------
-- Weaker keeps the invariant

mutual
  keys-≼ : ∀ {Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → {s′ s : St Γ A} → s′ ≼ s → Keys⁺ P s → Keys⁺ P s′
  keys-≼ tr (w≼ nw ks) (a , k) = node-all tr nw a , kids-≼ tr ks k

  kids-≼ : ∀ {Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → {s′ s : St Γ A} → Kids≼ s′ s → KidKeys⁺ P s → KidKeys⁺ P s′
  kids-≼ tr (bare≼ {s′ = pend o} b)         k       = tt
  kids-≼ tr (bare≼ {s′ = coldS x l} b)      k       = tt
  kids-≼ tr (bare≼ {s′ = ofS i p xs} b)     k       = tt
  kids-≼ tr (bare≼ {s′ = doneS} b)          k       = tt
  kids-≼ tr (bare≼ {s′ = joinS j g x ib} b) k       = tt
  kids-≼ tr (void≼ v)                       k       = proj₂ (void-keys v)
  kids-≼ tr (map≼ r)                        k       = keys-≼ tr r k
  kids-≼ tr (scan≼ r)                       k       = keys-≼ tr r k
  kids-≼ tr (cut≼ cw r)                     k       = keys-≼ tr r k
  kids-≼ tr (ln≼ r)                         k       = keys-≼ tr r k
  kids-≼ tr (take≼ r)                       k       = keys-≼ tr r k
  kids-≼ tr (flat≼ r rs)                    (a , b) = keys-≼ tr r a , lanes-≼ tr rs b
  kids-≼ tr (conn≼ cw r r′)                 (a , b) = keys-≼ tr r a , keys-≼ tr r′ b

  lanes-≼ : ∀ {Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → {ls′ ls : List (St Γ A)} → Lanes≼ ls′ ls
          → LaneKeys⁺ P ls → LaneKeys⁺ P ls′
  lanes-≼ tr []≼       tt       = tt
  lanes-≼ tr (r ∷≼ rs) (a , as) = keys-≼ tr r a , lanes-≼ tr rs as

far-tr : ∀ k {h h′} → h′ ≤ᴷ h → Farᴷ k h → Farᴷ k h′
far-tr k le = farK le k

free-tr : ∀ k {h h′} → h′ ≤ᴷ h → Freeᴷ k h → Freeᴷ k h′
free-tr k le = freeK le k

-- A weaker context reads no more of its siblings; the hole is not read.
aloft-≼ᶜ : ∀ {R Γ A} {k} {c′ c : Ctx R Γ A} → c′ ≼ᶜ c → ∀ {t t′} → Aloft⁺ k c t → Aloft⁺ k c′ t′
aloft-≼ᶜ top≼                         a = tt
aloft-≼ᶜ (map≼ᶜ r)                    a = aloft-≼ᶜ r a
aloft-≼ᶜ (scan≼ᶜ r)                   a = aloft-≼ᶜ r a
aloft-≼ᶜ {k = k} (cut≼ᶜ cw r)         (e , a) = (λ f → e (cut-fut cw f)) , aloft-≼ᶜ r a
aloft-≼ᶜ (ln≼ᶜ r)                     a = aloft-≼ᶜ r a
aloft-≼ᶜ (take≼ᶜ r)                   a = aloft-≼ᶜ r a
aloft-≼ᶜ {k = k} (outer≼ᶜ rs r)       (l , a) = lanes-≼ (far-tr k) rs l , aloft-≼ᶜ r a
aloft-≼ᶜ {k = k} (lanes≼ᶜ ro rp rq r) (o , p , q , a) = keys-≼ (far-tr k) ro o , lanes-≼ (far-tr k) rp p , lanes-≼ (far-tr k) rq q , aloft-≼ᶜ r a
aloft-≼ᶜ {k = k} (src≼ᶜ {b′ = b′} {b} cw rb r) {t} {t′} (x , m , a) =
  keys-≼ (far-tr k) rb x , node-all (far-tr k) (conn cw {o = t} {t′} {b} {b′}) m , aloft-≼ᶜ r a
aloft-≼ᶜ {k = k} (body≼ᶜ {o′ = o′} {o} cw ro r) {t} {t′} (x , f , m , a) =
  keys-≼ (far-tr k) ro x , keys-≼ (free-tr k) ro f , node-all (far-tr k) (conn cw {o = o} {o′} {t} {t′}) m , aloft-≼ᶜ r a

-- A weaker mark is aloft wherever the stronger is.
aloft-≤ : ∀ {R Γ A} {h h′} → h′ ≤ᴷ h → (c : Ctx R Γ A) (t : St Γ A) → Aloft⁺ h c t → Aloft⁺ h′ c t
aloft-≤ le top                               t a = tt
aloft-≤ le (inMap f c)                       t a = aloft-≤ le c (mapS f t) a
aloft-≤ le (inScan f z c)                    t a = aloft-≤ le c (scanS f z t) a
aloft-≤ le (inCut l x c)                     t (e , a) = (λ f → farM le _ (e f)) , aloft-≤ le c (cutS l x t) a
aloft-≤ le (inLn b c)                        t a = aloft-≤ le c (lnS b t) a
aloft-≤ le (inTake i q w c)                  t a = aloft-≤ le c (takeS i q w t) a
aloft-≤ le (inOuter op f d n q ls c)         t (l , a) = lanes-map (farM le _) ls l , aloft-≤ le c (flatS op f d n q t ls) a
aloft-≤ le (inLanes op f d n q o pre post c) t (x , p , r , a) =
  keys-map (farM le _) o x , lanes-map (farM le _) pre p , lanes-map (farM le _) post r , aloft-≤ le c (flatS op f d n q o (pre ʳ++ t ∷ post)) a
aloft-≤ le (inSrc kk b c)                    t (x , m , a) = keys-map (farM le _) b x , (λ f → farM le _ (m f)) , aloft-≤ le c (connS kk t b) a
aloft-≤ le (inBody kk o c)                   t (x , f , m , a) =
  keys-map (farM le _) o x , keys-map (freeM le _) o f , (λ g → farM le _ (m g)) , aloft-≤ le c (connS kk o t) a

-- A mark aloft: all it sows aloft.
aloft-out : ∀ {R Γ A} {x h} (c : Ctx R Γ A) (t : St Γ A) → Aloft⁺ (at x) c t → Sownᴷ x h → Aloft⁺ h c t
aloft-out top                               t a                  s = tt
aloft-out (inMap f c)                       t a                  s = aloft-out c (mapS f t) a s
aloft-out (inScan f z c)                    t a                  s = aloft-out c (scanS f z t) a s
aloft-out (inCut l y c)                     t (e , a)            s = (λ g → far-out _ (e g) s) , aloft-out c (cutS l y t) a s
aloft-out (inLn b c)                        t a                  s = aloft-out c (lnS b t) a s
aloft-out (inTake i q w c)                  t a                  s = aloft-out c (takeS i q w t) a s
aloft-out (inOuter op f d n q ls c)         t (kl , a)           s =
  lanes-map (λ {k} fr → far-out k fr s) ls kl , aloft-out c (flatS op f d n q t ls) a s
aloft-out (inLanes op f d n q o pre post c) t (ko , kp , kq , a) s =
  keys-map (λ {k} fr → far-out k fr s) o ko , lanes-map (λ {k} fr → far-out k fr s) pre kp , lanes-map (λ {k} fr → far-out k fr s) post kq ,
  aloft-out c (flatS op f d n q o (pre ʳ++ t ∷ post)) a s
aloft-out (inSrc kk b c)                    t (kb , m , a)       s =
  keys-map (λ {k} fr → far-out k fr s) b kb , (λ g → far-out _ (m g) s) , aloft-out c (connS kk t b) a s
aloft-out (inBody kk o c)                   t (ko , kf , m , a)  s =
  keys-map (λ {k} fr → far-out k fr s) o ko , keys-map (λ {k} fr → free-out k fr s) o ko , (λ g → far-out _ (m g) s) , aloft-out c (connS kk o t) a s

-- WEAKER STAYS CAUSAL: a weaker tree under a weaker context.
mutual
  causal-≼ : ∀ {R Γ A} {c′ c : Ctx R Γ A} {s′ s : St Γ A} → c′ ≼ᶜ c → s′ ≼ s → CausalW c s → CausalW c′ s′
  causal-≼ {c′ = c′} {c} {s′} {s} rc (w≼ nw ks) (m , k) =
    (λ f → aloft-≤ (proj₂ (proj₂ (back nw f))) c′ s′ (aloft-≼ᶜ rc (m (proj₁ (proj₂ (back nw f)))))) , causal-kids rc ks k

  causal-kids : ∀ {R Γ A} {c′ c : Ctx R Γ A} {s′ s : St Γ A} → c′ ≼ᶜ c → Kids≼ s′ s → KidsW c s → KidsW c′ s′
  causal-kids rc (bare≼ {s′ = pend o} b)         k       = tt
  causal-kids rc (bare≼ {s′ = coldS x l} b)      k       = tt
  causal-kids rc (bare≼ {s′ = ofS i p xs} b)     k       = tt
  causal-kids rc (bare≼ {s′ = doneS} b)          k       = tt
  causal-kids rc (bare≼ {s′ = joinS j g x ib} b) k       = tt
  causal-kids {c′ = c′} {s′ = s′} rc (void≼ v)   k       = proj₂ (void-causal c′ s′ v)
  causal-kids rc (map≼ r)                        k       = causal-≼ (map≼ᶜ rc) r k
  causal-kids rc (scan≼ r)                       k       = causal-≼ (scan≼ᶜ rc) r k
  causal-kids rc (cut≼ cw r)                     k       = causal-≼ (cut≼ᶜ cw rc) r k
  causal-kids rc (ln≼ r)                         k       = causal-≼ (ln≼ᶜ rc) r k
  causal-kids rc (take≼ r)                       k       = causal-≼ (take≼ᶜ rc) r k
  causal-kids rc (flat≼ r rs)                    (o , l) = causal-≼ (outer≼ᶜ rs rc) r o , causal-lanes rc r []≼ rs l
  causal-kids rc (conn≼ cw r r′)                 (o , b) = causal-≼ (src≼ᶜ cw r′ rc) r o , causal-≼ (body≼ᶜ cw r rc) r′ b

  causal-lanes : ∀ {R Γ A B} {op op′} {f f′ : A → Obs Timeline Γ B} {d d′ n n′ q q′} {c′ c : Ctx R Γ B} {o′ o : St Γ A} {pre′ pre post′ post}
               → c′ ≼ᶜ c → o′ ≼ o → Lanes≼ pre′ pre → Lanes≼ post′ post
               → LanesW c op f d n q o pre post → LanesW c′ op′ f′ d′ n′ q′ o′ pre′ post′
  causal-lanes rc ro rp []≼       tt      = tt
  causal-lanes rc ro rp (r ∷≼ rs) (w , l) = causal-≼ (lanes≼ᶜ ro rp rs rc) r w , causal-lanes rc ro (r ∷≼ rp) rs l

------------------------------------------------------------------------
-- Weaker, node by node

-- A connect's own marks read its record alone.
own-conn : ∀ {Γ X B} k {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} → own (connS k o b) ≡ own (connS k o′ b′)
own-conn (cs cl sl sa nothing  nothing  nothing  r e) = refl
own-conn (cs cl sl sa nothing  nothing  (just w) r e) = refl
own-conn (cs cl sl sa nothing  (just a) nothing  r e) = refl
own-conn (cs cl sl sa nothing  (just a) (just w) r e) = refl
own-conn (cs cl sl sa (just p) nothing  nothing  r e) = refl
own-conn (cs cl sl sa (just p) nothing  (just w) r e) = refl
own-conn (cs cl sl sa (just p) (just a) nothing  r e) = refl
own-conn (cs cl sl sa (just p) (just a) (just w) r e) = refl

owned : ∀ {xs ys : List (Mark × Key)} → xs ≡ ys → ∀ {h} → (Σ Mark λ m → (m , h) ∈ xs) → Σ Mark λ m → (m , h) ∈ ys
owned e (m , i) = m , subst (_ ∈_) e i

conn-refl : ∀ k → ConnW k k
conn-refl k = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (λ f → _ , owned (own-conn k {o = o′} {o} {b′} {b}) f , ≤ᴷ-refl))

node-same : ∀ {Γ Γ′ A A′} {s′ : St Γ′ A′} {s : St Γ A} → (∀ {h} → Fut s′ h → Fut s h) → NodeW s′ s
node-same e = nodeW (λ f → _ , e f , ≤ᴷ-refl)

own-cut : ∀ {Γ A} l a {s s′ : St Γ A} → own (cutS l a s) ≡ own (cutS l a s′)
own-cut l attached  = refl
own-cut l (attAt p) = refl

own-take : ∀ {Γ A} i q w {s s′ : St Γ A} → own (takeS i q w s) ≡ own (takeS i q w s′)
own-take i q free       = refl
own-take i q (cpAt p)   = refl
own-take i q (cutAt p)  = refl
own-take i q (overAt p) = refl

mutual
  ≼-refl : ∀ {Γ A} (s : St Γ A) → s ≼ s
  ≼-refl s = w≼ (node-same {s′ = s} {s} (λ f → f)) (kids-refl s)

  kids-refl : ∀ {Γ A} (s : St Γ A) → Kids≼ s s
  kids-refl (pend o)                = bare≼ tt
  kids-refl (coldS b l)             = bare≼ tt
  kids-refl (ofS i p xs)            = bare≼ tt
  kids-refl doneS                   = bare≼ tt
  kids-refl (mapS f s)              = map≼ (≼-refl s)
  kids-refl (scanS f z s)           = scan≼ (≼-refl s)
  kids-refl (cutS l a s)            = cut≼ cut-same (≼-refl s)
  kids-refl (lnS b s)               = ln≼ (≼-refl s)
  kids-refl (takeS i q w s)         = take≼ (≼-refl s)
  kids-refl (flatS op f d n q o ls) = flat≼ (≼-refl o) (lanes-refl ls)
  kids-refl (connS k o b)           = conn≼ (conn-refl k) (≼-refl o) (≼-refl b)
  kids-refl (joinS j g x ib)        = bare≼ tt

  lanes-refl : ∀ {Γ A} (ls : List (St Γ A)) → Lanes≼ ls ls
  lanes-refl []       = []≼
  lanes-refl (s ∷ ls) = ≼-refl s ∷≼ lanes-refl ls

lanes-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {xs′ xs} → Lanes≼ xs′ xs → Lanes≼ (pre ʳ++ xs′) (pre ʳ++ xs)
lanes-ʳ++ []       r = r
lanes-ʳ++ (p ∷ pre) r = lanes-ʳ++ pre (≼-refl p ∷≼ r)

-- A weaker node keeps the whole tree weaker.
plug-≼ : ∀ {R Γ A} (c : Ctx R Γ A) {s′ s : St Γ A} → s′ ≼ s → plug c s′ ≼ plug c s
plug-≼ top                               r = r
plug-≼ (inMap f c)                       {s′} {s} r = plug-≼ c {mapS f s′} {mapS f s} (w≼ (nodeW (λ { (_ , ()) })) (map≼ r))
plug-≼ (inScan f z c)                    {s′} {s} r = plug-≼ c {scanS f z s′} {scanS f z s} (w≼ (nodeW (λ { (_ , ()) })) (scan≼ r))
plug-≼ (inCut l a c)                     {s′} {s} r = plug-≼ c {cutS l a s′} {cutS l a s} (w≼ (node-same (owned (own-cut l a))) (cut≼ cut-same r))
plug-≼ (inLn b c)                        {s′} {s} r = plug-≼ c {lnS b s′} {lnS b s} (w≼ (nodeW (λ { (_ , ()) })) (ln≼ r))
plug-≼ (inTake i q w c)                  {s′} {s} r = plug-≼ c {takeS i q w s′} {takeS i q w s} (w≼ (node-same (owned (own-take i q w))) (take≼ r))
plug-≼ (inOuter op f d n q ls c)         {s′} {s} r = plug-≼ c {flatS op f d n q s′ ls} {flatS op f d n q s ls} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ r (lanes-refl ls)))
plug-≼ (inLanes op f d n q o pre post c) {s′} {s} r =
  plug-≼ c {flatS op f d n q o (pre ʳ++ s′ ∷ post)} {flatS op f d n q o (pre ʳ++ s ∷ post)} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl o) (lanes-ʳ++ pre (r ∷≼ lanes-refl post))))
plug-≼ (inSrc kk b c)                    {s′} {s} r = plug-≼ c {connS kk s′ b} {connS kk s b} (w≼ (conn (conn-refl kk)) (conn≼ (conn-refl kk) r (≼-refl b)))
plug-≼ (inBody kk o c)                   {s′} {s} r = plug-≼ c {connS kk o s′} {connS kk o s} (w≼ (conn (conn-refl kk)) (conn≼ (conn-refl kk) (≼-refl o) r))

-- A weaker node keeps the tree causal.
causal-run : ∀ {R Γ A} (c : Ctx R Γ A) {s′ s : St Γ A} → s′ ≼ s → Causal (plug c s) → Causal (plug c s′)
causal-run c r = causal-≼ top≼ (plug-≼ c r)

-- An unsubscribe, a cut, a kill: weaker.
mutual
  unsub-≼ : ∀ {Γ A} (s : St Γ A) → proj₁ (unsub s) ≼ s
  unsub-≼ (pend o)                = ≼-refl _
  unsub-≼ {Γ} {A} (coldS true l)  = w≼ (node-same (λ { (_ , i) → own-tape {Γ} {A} false l i })) (bare≼ tt)
  unsub-≼ (coldS false l)         = ≼-refl _
  unsub-≼ (ofS i p xs)            = ≼-refl _
  unsub-≼ doneS                   = ≼-refl _
  unsub-≼ (mapS f s)              = w≼ (nodeW (λ { (_ , ()) })) (map≼ (unsub-≼ s))
  unsub-≼ (scanS f z s)           = w≼ (nodeW (λ { (_ , ()) })) (scan≼ (unsub-≼ s))
  unsub-≼ (cutS l a s)            = ≼-refl _
  unsub-≼ (lnS b s)               = ≼-refl _
  unsub-≼ (takeS i q w s)         = w≼ (node-same (owned (own-take i q w))) (take≼ (cut-≼ s))
  unsub-≼ (flatS op f d n q o ls) = w≼ (nodeW (λ { (_ , ()) })) (flat≼ (cut-≼ o) (killAll-≼ ls))
  unsub-≼ (connS k o b)           = w≼ (conn (conn-refl k)) (conn≼ (conn-refl k) (unsub-≼ o) (unsub-≼ b))
  unsub-≼ (joinS j g x ib)        = w≼ (nodeW (λ { (_ , ()) })) (bare≼ tt)

  cut-≼ : ∀ {Γ A} (s : St Γ A) → proj₁ (cut s) ≼ s
  cut-≼ (cutS l attached s)  = w≼ (nodeW (λ { (_ , ()) })) (cut≼ cut-same (unsub-≼ s))
  cut-≼ (cutS l (attAt p) s) = w≼ (node-same (λ f → f)) (cut≼ cut-same (≼-refl s))
  cut-≼ (pend o)                = ≼-refl _
  cut-≼ (coldS b l)             = ≼-refl _
  cut-≼ (ofS i p xs)            = ≼-refl _
  cut-≼ doneS                   = ≼-refl _
  cut-≼ (mapS f s)              = ≼-refl _
  cut-≼ (scanS f z s)           = ≼-refl _
  cut-≼ (lnS b s)               = ≼-refl _
  cut-≼ (takeS i q w s)         = ≼-refl _
  cut-≼ (flatS op f d n q o ls) = ≼-refl _
  cut-≼ (connS k o b)           = ≼-refl _
  cut-≼ (joinS j g x ib)        = ≼-refl _

  killAll-≼ : ∀ {Γ A} (ls : List (St Γ A)) → Lanes≼ (proj₁ (killAll ls)) ls
  killAll-≼ []                 = []≼
  killAll-≼ (lnS true s ∷ ls)  = w≼ (nodeW (λ { (_ , ()) })) (ln≼ (cut-≼ s)) ∷≼ killAll-≼ ls
  killAll-≼ (lnS false s ∷ ls) = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (pend o ∷ ls)                = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (coldS b l ∷ ls)             = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (ofS i p xs ∷ ls)            = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (doneS ∷ ls)                 = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (mapS f s ∷ ls)              = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (scanS f z s ∷ ls)           = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (cutS l a s ∷ ls)            = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (takeS i q w s ∷ ls)         = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (flatS op f d n q o l ∷ ls)  = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (connS k o b ∷ ls)           = ≼-refl _ ∷≼ killAll-≼ ls
  killAll-≼ (joinS j g x ib ∷ ls)        = ≼-refl _ ∷≼ killAll-≼ ls

unsubIf-≼ : ∀ {Γ A} b (s : St Γ A) → proj₁ (unsubIf b s) ≼ s
unsubIf-≼ true  s = unsub-≼ s
unsubIf-≼ false s = ≼-refl s

-- A mark run, node by node: its node weaker.
of-≼ : ∀ {Γ A} i p (x : A) xs → ofS {Γ} (1+ i) p xs ≼ ofS i p (x ∷ xs)
of-≼ i p x xs = w≼ (nodeW (λ { (m , i) → _ , (m , there i) , ≤ᴷ-refl })) (bare≼ tt)

done-≼ : ∀ {Γ A} (s : St Γ A) → doneS ≼ s
done-≼ s = w≼ (nodeW (λ { (_ , ()) })) (bare≼ tt)

join-≼ : ∀ {Γ A} j g g′ (x : A ∈ Γ) qe ib → joinS j g′ x ib ≼ joinS j g x (qe ∷ ib)
join-≼ j g g′ x qe ib = w≼ (nodeW (λ { (m , i) → _ , (m , there i) , ≤ᴷ-refl })) (bare≼ tt)

att-≼ : ∀ {Γ A} l p {s′ s : St Γ A} → s′ ≼ s → cutS l attached s′ ≼ cutS l (attAt p) s
att-≼ l p r = w≼ (nodeW (λ { (_ , ()) })) (cut≼ cut-drop r)

cp-≼ : ∀ {Γ A} i q p (s : St Γ A) → takeS i q (cutAt p) s ≼ takeS i q (cpAt p) s
cp-≼ i q p s = w≼ (nodeW (λ { (_ , here refl) → _ , (_ , here refl) , after≤at p (p ⊕ [ last ]) [ last ] refl ; (_ , there ()) })) (take≼ (≼-refl s))

over-≼ : ∀ {Γ A} i q p {s′ s : St Γ A} → s′ ≼ s → takeS i q (overAt p) s′ ≼ takeS i q (cutAt p) s
over-≼ i q p r = w≼ (nodeW (λ { (_ , ()) })) (take≼ r)

-- A body subscribed: its mark handed to the source's attach, past where
-- the body was keyed.
body-conn : ∀ cl sl sa p as ow r e → ConnW (cs cl sl sa nothing (just (p ⊕ [ ix 1 ])) ow r e) (cs cl sl sa (just p) as ow r e)
body-conn cl sl sa p as ow r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go as ow {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    q = p ⊕ [ ix 1 ]
    hand : after q ≤ᴷ at q
    hand = after≤at q q [] (sym (++-identityʳ q))
    go : ∀ as ow {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {h′} → Fut (connS (cs cl sl sa nothing (just q) ow r e) o′ b′) h′
       → Σ Key λ h → Fut (connS (cs cl sl sa (just p) as ow r e) o b) h × h′ ≤ᴷ h
    go nothing  nothing  (_ , here refl)               = _ , (_ , here refl) , hand
    go nothing  nothing  (_ , there ())
    go nothing  (just w) (_ , here refl)               = _ , (_ , here refl) , hand
    go nothing  (just w) (_ , there (here refl))       = _ , (_ , there (here refl)) , ≤ᴷ-refl
    go nothing  (just w) (_ , there (there ()))
    go (just a) nothing  (_ , here refl)               = _ , (_ , here refl) , hand
    go (just a) nothing  (_ , there ())
    go (just a) (just w) (_ , here refl)               = _ , (_ , here refl) , hand
    go (just a) (just w) (_ , there (here refl))       = _ , (_ , there (there (here refl))) , ≤ᴷ-refl
    go (just a) (just w) (_ , there (there ()))

-- A source's attach run: its mark dropped.
src-conn : ∀ cl sl sa ba a ow r e → ConnW (cs cl sl true ba nothing ow r e) (cs cl sl sa ba (just a) ow r e)
src-conn cl sl sa ba a ow r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go ba ow {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    go : ∀ ba ow {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {h′} → Fut (connS (cs cl sl true ba nothing ow r e) o′ b′) h′
       → Σ Key λ h → Fut (connS (cs cl sl sa ba (just a) ow r e) o b) h × h′ ≤ᴷ h
    go nothing  nothing  (_ , ())
    go nothing  (just w) (_ , here refl)               = _ , (_ , there (here refl)) , ≤ᴷ-refl
    go nothing  (just w) (_ , there ())
    go (just p) nothing  (_ , here refl)               = _ , (_ , here refl) , ≤ᴷ-refl
    go (just p) nothing  (_ , there ())
    go (just p) (just w) (_ , here refl)               = _ , (_ , here refl) , ≤ᴷ-refl
    go (just p) (just w) (_ , there (here refl))       = _ , (_ , there (there (here refl))) , ≤ᴷ-refl
    go (just p) (just w) (_ , there (there ()))

-- A source's teardown run: its mark dropped.
owed-conn : ∀ cl sl sa ba as w r e → ConnW (cs cl false sa ba as nothing r e) (cs cl sl sa ba as (just w) r e)
owed-conn cl sl sa ba as w r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go ba as {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    go : ∀ ba as {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {h′} → Fut (connS (cs cl false sa ba as nothing r e) o′ b′) h′
       → Σ Key λ h → Fut (connS (cs cl sl sa ba as (just w) r e) o b) h × h′ ≤ᴷ h
    go nothing  nothing  (_ , ())
    go nothing  (just a) (_ , here refl)               = _ , (_ , here refl) , ≤ᴷ-refl
    go nothing  (just a) (_ , there ())
    go (just p) nothing  (_ , here refl)               = _ , (_ , here refl) , ≤ᴷ-refl
    go (just p) nothing  (_ , there ())
    go (just p) (just a) (_ , here refl)               = _ , (_ , here refl) , ≤ᴷ-refl
    go (just p) (just a) (_ , there (here refl))       = _ , (_ , there (here refl)) , ≤ᴷ-refl
    go (just p) (just a) (_ , there (there ()))

conn-≼ : ∀ {Γ X B} {kk′ kk} {o′ o : St Γ X} {b′ b : St (X ∷ Γ) B} → ConnW kk′ kk → o′ ≼ o → b′ ≼ b → connS kk′ o′ b′ ≼ connS kk o b
conn-≼ cw ro rb = w≼ (conn cw) (conn≼ cw ro rb)

-- A live cold's leaf run: its tape moved on.
cold-≼ : ∀ {Γ A} (l : Tape A) → coldS {Γ} true (advance l) ≼ coldS true l
cold-≼ l = w≼ (node-same (λ { (n , e) → 1+ n , e })) (bare≼ tt)

-- A cold whose tape is over: nothing to come.
cold-over : ∀ {Γ A} b b′ (l : Tape A) → coldS {Γ} b′ over ≼ coldS b l
cold-over b true  l = w≼ (nodeW (λ f → ⊥-elim (tapes-over f))) (bare≼ tt)
cold-over b false l = w≼ (nodeW (λ { (_ , ()) })) (bare≼ tt)

-- A keyless node: weaker than any.
void-≼ : ∀ {Γ A} {s′ s : St Γ A} → Void s′ → s′ ≼ s
void-≼ v = w≼ (nodeW (λ f → ⊥-elim (proj₁ v f))) (void≼ v)
