{-# OPTIONS --guardedness #-}

-- NOTHING KEYED UNDER A SKIP NOT YET RUN (`Causal`): at every node, each
-- mark it owns or will own (`fut`: an of's values and completion to come,
-- a joiner's queue) is aloft (`Aloft⁺`) of every key, owned or to come,
-- of each part racing it.  Read over what is to come, a mark run only
-- takes from what the invariant reads: the tree it leaves is weaker
-- (`_≼_`: each node's keys to come among the old ones, or past one at or
-- above it), and a weaker tree is causal wherever the stronger was
-- (`causal-≼`).
module adequacy.Engine.Causal where

open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse; replicate; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; ʳ++-defn; reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; tabulate; lookup) renaming (map to allMap)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ) renaming (suc to 1+)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Tree using (Obs; FlatOp)
open import denotation.MonotonicList.Events using (Pos; Timeline; ix; last)
open import operation.Key using (Key; at; after)
open import operation.PureObservable using (module Machine; due)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; CS; cs;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; own;
  Mark; ofM; joinM; attached; attAt; free; cpAt; cutAt; overAt; unsub; cut; killAll; unsubIf; _⊕_)

------------------------------------------------------------------------
-- Keys

-- A position's key: where it is, or the position it is past.
posᴷ : Key → Pos
posᴷ (at p)    = p
posᴷ (after p) = p

-- A key far from a mark's: no position its events reach at or under the
-- mark's, an at-key's own with `ix 0`s appended as `shift` appends them.
Farᴷ : Key → Key → Set
Farᴷ (at p)    (at q)    = ∀ n → (Σ Pos λ ys → q ++ replicate n (ix 0) ≡ p ++ ys) → ⊥
Farᴷ (at p)    (after q) = (Σ Pos λ ys → q ≡ p ++ ys) → ⊥
Farᴷ (after p) h         = ⊤

-- A mark at or under no position a key is at.
Freeᴷ : Key → Key → Set
Freeᴷ k (at r)    = (Σ Pos λ ys → posᴷ k ≡ r ++ ys) → ⊥
Freeᴷ k (after _) = ⊤

-- What a node will own: an of's every value and completion to come, a
-- joiner's whole queue; else what it owns.
ofFut : ℕ → Pos → ∀ {A : Set} → List A → List (Mark × Key)
ofFut i p []       = [ (ofM , at (p ⊕ [ last ])) ]
ofFut i p (_ ∷ xs) = (ofM , at (p ⊕ [ ix i ])) ∷ ofFut (1+ i) p xs

fut : ∀ {Γ A} → St Γ A → List (Mark × Key)
fut (ofS i p xs)     = ofFut i p xs
fut (joinS j g x ib) = map (λ qe → (joinM , at (proj₁ qe))) ib
fut s                = own s

own-fut : ∀ {Γ A} (s : St Γ A) {mk} → mk ∈ own s → mk ∈ fut s
own-fut (pend o)                    i = i
own-fut (coldS b l)                 i = i
own-fut (ofS i p [])                m = m
own-fut (ofS i p (_ ∷ _))           (here e) = here e
own-fut (ofS i p (_ ∷ _))           (there ())
own-fut doneS                       i = i
own-fut (mapS f s)                  i = i
own-fut (scanS f z s)               i = i
own-fut (cutS l a s)                i = i
own-fut (lnS b s)                   i = i
own-fut (takeS i q w s)             m = m
own-fut (flatS op f d n q o ls)     i = i
own-fut (connS k o b)               i = i
own-fut (joinS j g x [])            ()
own-fut (joinS j g x ((q , _) ∷ _)) (here e) = here e
own-fut (joinS j g x ((q , _) ∷ _)) (there ())

-- Every key every node of a tree owns, or will own, as `ks` reads it.
mutual
  KeysBy : (∀ {Γ A} → St Γ A → List (Mark × Key)) → ∀ {Γ A} → (Key → Set) → St Γ A → Set
  KeysBy ks P s = All (λ mk → P (proj₂ mk)) (ks s) × KidKeys ks P s

  KidKeys : (∀ {Γ A} → St Γ A → List (Mark × Key)) → ∀ {Γ A} → (Key → Set) → St Γ A → Set
  KidKeys ks P (mapS f s)              = KeysBy ks P s
  KidKeys ks P (scanS f z s)           = KeysBy ks P s
  KidKeys ks P (cutS l a s)            = KeysBy ks P s
  KidKeys ks P (lnS b s)               = KeysBy ks P s
  KidKeys ks P (takeS i q w s)         = KeysBy ks P s
  KidKeys ks P (flatS op f d n q o ls) = KeysBy ks P o × LaneKeysBy ks P ls
  KidKeys ks P (connS k o b)           = KeysBy ks P o × KeysBy ks P b
  KidKeys ks P _                       = ⊤

  LaneKeysBy : (∀ {Γ A} → St Γ A → List (Mark × Key)) → ∀ {Γ A} → (Key → Set) → List (St Γ A) → Set
  LaneKeysBy ks P []       = ⊤
  LaneKeysBy ks P (s ∷ ls) = KeysBy ks P s × LaneKeysBy ks P ls

Keysᴬ : ∀ {Γ A} → (Key → Set) → St Γ A → Set
Keysᴬ = KeysBy own

LaneKeys : ∀ {Γ A} → (Key → Set) → List (St Γ A) → Set
LaneKeys = LaneKeysBy own

Keys⁺ : ∀ {Γ A} → (Key → Set) → St Γ A → Set
Keys⁺ = KeysBy fut

LaneKeys⁺ : ∀ {Γ A} → (Key → Set) → List (St Γ A) → Set
LaneKeys⁺ = LaneKeysBy fut

-- What is to come includes what is owned.
mutual
  keys-own : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → Keys⁺ P s → Keysᴬ P s
  keys-own s (a , k) = tabulate (λ i → lookup a (own-fut s i)) , kids-own s k

  kids-own : ∀ {Γ A} {P : Key → Set} (s : St Γ A) → KidKeys fut P s → KidKeys own P s
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
  keys-map : ∀ {ks : ∀ {Γ A} → St Γ A → List (Mark × Key)} {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (s : St Γ A)
           → KeysBy ks P s → KeysBy ks Q s
  keys-map g s (a , k) = allMap g a , kids-map g s k

  kids-map : ∀ {ks : ∀ {Γ A} → St Γ A → List (Mark × Key)} {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (s : St Γ A)
           → KidKeys ks P s → KidKeys ks Q s
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

  lanes-map : ∀ {ks : ∀ {Γ A} → St Γ A → List (Mark × Key)} {Γ A} {P Q : Key → Set} → (∀ {h} → P h → Q h) → (ls : List (St Γ A))
            → LaneKeysBy ks P ls → LaneKeysBy ks Q ls
  lanes-map g []       tt       = tt
  lanes-map g (s ∷ ls) (a , as) = keys-map g s a , lanes-map g ls as

------------------------------------------------------------------------
-- The invariant

-- Every frame above a node's mark at `k`: every key, owned or to come, of
-- each part racing it, and each connect's own marks, far from `k`; a
-- body's mark at or under no key of its source.  Of every key, not the
-- race's candidates alone: a mark run hands a part's candidacy to a key
-- no candidate constrained.
Aloft⁺ : ∀ {R Γ A} → Key → Ctx R Γ A → St Γ A → Set
Aloft⁺ k top                                s = ⊤
Aloft⁺ k (inMap f c)                        s = Aloft⁺ k c (mapS f s)
Aloft⁺ k (inScan f z c)                     s = Aloft⁺ k c (scanS f z s)
Aloft⁺ k (inCut l a c)                      s = Aloft⁺ k c (cutS l a s)
Aloft⁺ k (inLn b c)                         s = Aloft⁺ k c (lnS b s)
Aloft⁺ k (inTake i q w c)                   s = Aloft⁺ k c (takeS i q w s)
Aloft⁺ k (inOuter op f d n q ls c)          s = LaneKeys⁺ (Farᴷ k) ls × Aloft⁺ k c (flatS op f d n q s ls)
Aloft⁺ k (inLanes op f d n q o pre post c)  s =
  Keys⁺ (Farᴷ k) o × LaneKeys⁺ (Farᴷ k) pre × LaneKeys⁺ (Farᴷ k) post × Aloft⁺ k c (flatS op f d n q o (pre ʳ++ s ∷ post))
Aloft⁺ k (inSrc kk b c)                     s =
  Keys⁺ (Farᴷ k) b × All (λ mk → Farᴷ k (proj₂ mk)) (fut (connS kk s b)) × Aloft⁺ k c (connS kk s b)
Aloft⁺ k (inBody kk o c)                    s =
  Keys⁺ (Farᴷ k) o × Keys⁺ (Freeᴷ k) o × All (λ mk → Farᴷ k (proj₂ mk)) (fut (connS kk o s)) × Aloft⁺ k c (connS kk o s)

-- At every node under `c`, every mark to come aloft.
mutual
  CausalW : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
  CausalW c s = All (λ mk → Aloft⁺ (proj₂ mk) c s) (fut s) × KidsW c s

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

-- Every node's every mark to come is aloft.
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
causal-own ca c s e i = lookup (proj₁ (walk-at c s (subst Causal (sym e) ca))) (own-fut s i)

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
    fk (at p)    fr (zs , e′) = fr 0 (zs ++ ys , trans (++-identityʳ r) (trans e (trans (cong (_++ ys) e′) (++-assoc p zs ys))))
    fk (after p) fr           = tt
    fm : ∀ g → Freeᴷ (at r) g → Freeᴷ (after q) g
    fm (at p)    fr (zs , e′) = fr (zs ++ ys , trans e (trans (cong (_++ ys) e′) (++-assoc p zs ys)))
    fm (after p) fr           = tt

-- Each mark to come of `s′` weaker than one of `s`'s.
record NodeW {Γ Γ′ A A′} (s′ : St Γ′ A′) (s : St Γ A) : Set where
  constructor nodeW
  field back : ∀ {mk′} → mk′ ∈ fut s′ → Σ (Mark × Key) λ mk → mk ∈ fut s × proj₂ mk′ ≤ᴷ proj₂ mk
open NodeW

node-all : ∀ {Γ Γ′ A A′} {s′ : St Γ′ A′} {s : St Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → NodeW s′ s
         → All (λ mk → P (proj₂ mk)) (fut s) → All (λ mk → P (proj₂ mk)) (fut s′)
node-all tr nw a = tabulate (λ i → tr (proj₂ (proj₂ (back nw i))) (lookup a (proj₁ (proj₂ (back nw i)))))

-- A connect's own marks, as its record alone gives them.
record ConnW (kk′ kk : CS) : Set₁ where
  constructor connW
  field conn : ∀ {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} → NodeW (connS kk′ o′ b′) (connS kk o b)
open ConnW

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
    map≼  : ∀ {Γ A B} {f f′ : A → B} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (mapS f′ s′) (mapS f s)
    scan≼ : ∀ {Γ A B} {f f′ : B → A → B} {z z′} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (scanS f′ z′ s′) (scanS f z s)
    cut≼  : ∀ {Γ A} {l l′ a a′} {s′ s : St Γ A} → s′ ≼ s → Kids≼ (cutS l′ a′ s′) (cutS l a s)
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
  cut≼ᶜ  : ∀ {Γ A} {l l′ a a′} {c′ c : Ctx R Γ A} → c′ ≼ᶜ c → inCut l′ a′ c′ ≼ᶜ inCut l a c
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

  kids-≼ : ∀ {Γ A} {P : Key → Set} → (∀ {h h′} → h′ ≤ᴷ h → P h → P h′) → {s′ s : St Γ A} → Kids≼ s′ s → KidKeys fut P s → KidKeys fut P s′
  kids-≼ tr (bare≼ {s′ = pend o} b)         k       = tt
  kids-≼ tr (bare≼ {s′ = coldS x l} b)      k       = tt
  kids-≼ tr (bare≼ {s′ = ofS i p xs} b)     k       = tt
  kids-≼ tr (bare≼ {s′ = doneS} b)          k       = tt
  kids-≼ tr (bare≼ {s′ = joinS j g x ib} b) k       = tt
  kids-≼ tr (map≼ r)                        k       = keys-≼ tr r k
  kids-≼ tr (scan≼ r)                       k       = keys-≼ tr r k
  kids-≼ tr (cut≼ r)                        k       = keys-≼ tr r k
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
aloft-≼ᶜ (cut≼ᶜ r)                    a = aloft-≼ᶜ r a
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
aloft-≤ le (inCut l x c)                     t a = aloft-≤ le c (cutS l x t) a
aloft-≤ le (inLn b c)                        t a = aloft-≤ le c (lnS b t) a
aloft-≤ le (inTake i q w c)                  t a = aloft-≤ le c (takeS i q w t) a
aloft-≤ le (inOuter op f d n q ls c)         t (l , a) = lanes-map (farM le _) ls l , aloft-≤ le c (flatS op f d n q t ls) a
aloft-≤ le (inLanes op f d n q o pre post c) t (x , p , r , a) =
  keys-map (farM le _) o x , lanes-map (farM le _) pre p , lanes-map (farM le _) post r , aloft-≤ le c (flatS op f d n q o (pre ʳ++ t ∷ post)) a
aloft-≤ le (inSrc kk b c)                    t (x , m , a) = keys-map (farM le _) b x , allMap (farM le _) m , aloft-≤ le c (connS kk t b) a
aloft-≤ le (inBody kk o c)                   t (x , f , m , a) =
  keys-map (farM le _) o x , keys-map (freeM le _) o f , allMap (farM le _) m , aloft-≤ le c (connS kk o t) a

-- WEAKER STAYS CAUSAL: a weaker tree under a weaker context.
mutual
  causal-≼ : ∀ {R Γ A} {c′ c : Ctx R Γ A} {s′ s : St Γ A} → c′ ≼ᶜ c → s′ ≼ s → CausalW c s → CausalW c′ s′
  causal-≼ {c′ = c′} {c} {s′} {s} rc (w≼ nw ks) (m , k) =
    tabulate (λ i → aloft-≤ (proj₂ (proj₂ (back nw i))) c′ s′ (aloft-≼ᶜ rc (lookup m (proj₁ (proj₂ (back nw i)))))) , causal-kids rc ks k

  causal-kids : ∀ {R Γ A} {c′ c : Ctx R Γ A} {s′ s : St Γ A} → c′ ≼ᶜ c → Kids≼ s′ s → KidsW c s → KidsW c′ s′
  causal-kids rc (bare≼ {s′ = pend o} b)         k       = tt
  causal-kids rc (bare≼ {s′ = coldS x l} b)      k       = tt
  causal-kids rc (bare≼ {s′ = ofS i p xs} b)     k       = tt
  causal-kids rc (bare≼ {s′ = doneS} b)          k       = tt
  causal-kids rc (bare≼ {s′ = joinS j g x ib} b) k       = tt
  causal-kids rc (map≼ r)                        k       = causal-≼ (map≼ᶜ rc) r k
  causal-kids rc (scan≼ r)                       k       = causal-≼ (scan≼ᶜ rc) r k
  causal-kids rc (cut≼ r)                        k       = causal-≼ (cut≼ᶜ rc) r k
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

conn-refl : ∀ k → ConnW k k
conn-refl k = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (λ i → _ , subst (_ ∈_) (own-conn k {o = o′} {o} {b′} {b}) i , ≤ᴷ-refl))

node-same : ∀ {Γ Γ′ A A′} {s′ : St Γ′ A′} {s : St Γ A} → fut s′ ≡ fut s → NodeW s′ s
node-same e = nodeW (λ i → _ , subst (_ ∈_) e i , ≤ᴷ-refl)

own-cut : ∀ {Γ A} l a {s s′ : St Γ A} → own (cutS l a s) ≡ own (cutS l a s′)
own-cut l attached  = refl
own-cut l (attAt p) = refl

own-take : ∀ {Γ A} i q w {s s′ : St Γ A} → own (takeS i q w s) ≡ own (takeS i q w s′)
own-take i q free       = refl
own-take i q (cpAt p)   = refl
own-take i q (cutAt p)  = refl
own-take i q (overAt p) = refl

own-cold : ∀ {Γ A} b b′ l → own {Γ} {A} (coldS b l) ≡ own {Γ} {A} (coldS b′ l)
own-cold b b′ l with due l
... | just k  = refl
... | nothing = refl

mutual
  ≼-refl : ∀ {Γ A} (s : St Γ A) → s ≼ s
  ≼-refl s = w≼ (node-same {s′ = s} {s} refl) (kids-refl s)

  kids-refl : ∀ {Γ A} (s : St Γ A) → Kids≼ s s
  kids-refl (pend o)                = bare≼ tt
  kids-refl (coldS b l)             = bare≼ tt
  kids-refl (ofS i p xs)            = bare≼ tt
  kids-refl doneS                   = bare≼ tt
  kids-refl (mapS f s)              = map≼ (≼-refl s)
  kids-refl (scanS f z s)           = scan≼ (≼-refl s)
  kids-refl (cutS l a s)            = cut≼ (≼-refl s)
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
plug-≼ (inMap f c)                       {s′} {s} r = plug-≼ c {mapS f s′} {mapS f s} (w≼ (nodeW (λ ())) (map≼ r))
plug-≼ (inScan f z c)                    {s′} {s} r = plug-≼ c {scanS f z s′} {scanS f z s} (w≼ (nodeW (λ ())) (scan≼ r))
plug-≼ (inCut l a c)                     {s′} {s} r = plug-≼ c {cutS l a s′} {cutS l a s} (w≼ (node-same (own-cut l a)) (cut≼ r))
plug-≼ (inLn b c)                        {s′} {s} r = plug-≼ c {lnS b s′} {lnS b s} (w≼ (nodeW (λ ())) (ln≼ r))
plug-≼ (inTake i q w c)                  {s′} {s} r = plug-≼ c {takeS i q w s′} {takeS i q w s} (w≼ (node-same (own-take i q w)) (take≼ r))
plug-≼ (inOuter op f d n q ls c)         {s′} {s} r = plug-≼ c {flatS op f d n q s′ ls} {flatS op f d n q s ls} (w≼ (nodeW (λ ())) (flat≼ r (lanes-refl ls)))
plug-≼ (inLanes op f d n q o pre post c) {s′} {s} r =
  plug-≼ c {flatS op f d n q o (pre ʳ++ s′ ∷ post)} {flatS op f d n q o (pre ʳ++ s ∷ post)} (w≼ (nodeW (λ ())) (flat≼ (≼-refl o) (lanes-ʳ++ pre (r ∷≼ lanes-refl post))))
plug-≼ (inSrc kk b c)                    {s′} {s} r = plug-≼ c {connS kk s′ b} {connS kk s b} (w≼ (conn (conn-refl kk)) (conn≼ (conn-refl kk) r (≼-refl b)))
plug-≼ (inBody kk o c)                   {s′} {s} r = plug-≼ c {connS kk o s′} {connS kk o s} (w≼ (conn (conn-refl kk)) (conn≼ (conn-refl kk) (≼-refl o) r))

-- A weaker node keeps the tree causal.
causal-run : ∀ {R Γ A} (c : Ctx R Γ A) {s′ s : St Γ A} → s′ ≼ s → Causal (plug c s) → Causal (plug c s′)
causal-run c r = causal-≼ top≼ (plug-≼ c r)

-- An unsubscribe, a cut, a kill: weaker.
mutual
  unsub-≼ : ∀ {Γ A} (s : St Γ A) → proj₁ (unsub s) ≼ s
  unsub-≼ (pend o)                = ≼-refl _
  unsub-≼ {Γ} {A} (coldS true l)  = w≼ (node-same (own-cold {Γ} {A} false true l)) (bare≼ tt)
  unsub-≼ (coldS false l)         = ≼-refl _
  unsub-≼ (ofS i p xs)            = ≼-refl _
  unsub-≼ doneS                   = ≼-refl _
  unsub-≼ (mapS f s)              = w≼ (nodeW (λ ())) (map≼ (unsub-≼ s))
  unsub-≼ (scanS f z s)           = w≼ (nodeW (λ ())) (scan≼ (unsub-≼ s))
  unsub-≼ (cutS l a s)            = ≼-refl _
  unsub-≼ (lnS b s)               = ≼-refl _
  unsub-≼ (takeS i q w s)         = w≼ (node-same (own-take i q w)) (take≼ (cut-≼ s))
  unsub-≼ (flatS op f d n q o ls) = w≼ (nodeW (λ ())) (flat≼ (cut-≼ o) (killAll-≼ ls))
  unsub-≼ (connS k o b)           = w≼ (conn (conn-refl k)) (conn≼ (conn-refl k) (unsub-≼ o) (unsub-≼ b))
  unsub-≼ (joinS j g x ib)        = w≼ (nodeW (λ ())) (bare≼ tt)

  cut-≼ : ∀ {Γ A} (s : St Γ A) → proj₁ (cut s) ≼ s
  cut-≼ (cutS l attached s)  = w≼ (nodeW (λ ())) (cut≼ (unsub-≼ s))
  cut-≼ (cutS l (attAt p) s) = w≼ (node-same refl) (cut≼ (≼-refl s))
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
  killAll-≼ (lnS true s ∷ ls)  = w≼ (nodeW (λ ())) (ln≼ (cut-≼ s)) ∷≼ killAll-≼ ls
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
of-≼ i p x xs = w≼ (nodeW (λ m → _ , there m , ≤ᴷ-refl)) (bare≼ tt)

done-≼ : ∀ {Γ A} (s : St Γ A) → doneS ≼ s
done-≼ s = w≼ (nodeW (λ ())) (bare≼ tt)

join-≼ : ∀ {Γ A} j g g′ (x : A ∈ Γ) qe ib → joinS j g′ x ib ≼ joinS j g x (qe ∷ ib)
join-≼ j g g′ x qe ib = w≼ (nodeW (λ m → _ , there m , ≤ᴷ-refl)) (bare≼ tt)

att-≼ : ∀ {Γ A} l p {s′ s : St Γ A} → s′ ≼ s → cutS l attached s′ ≼ cutS l (attAt p) s
att-≼ l p r = w≼ (nodeW (λ ())) (cut≼ r)

cp-≼ : ∀ {Γ A} i q p (s : St Γ A) → takeS i q (cutAt p) s ≼ takeS i q (cpAt p) s
cp-≼ i q p s = w≼ (nodeW (λ { (here refl) → _ , here refl , after≤at p (p ⊕ [ last ]) [ last ] refl ; (there ()) })) (take≼ (≼-refl s))

over-≼ : ∀ {Γ A} i q p {s′ s : St Γ A} → s′ ≼ s → takeS i q (overAt p) s′ ≼ takeS i q (cutAt p) s
over-≼ i q p r = w≼ (nodeW (λ ())) (take≼ r)

-- A body subscribed: its mark handed to the source's attach, past where
-- the body was keyed.
body-conn : ∀ cl sl sa p as ow r e → ConnW (cs cl sl sa nothing (just (p ⊕ [ ix 1 ])) ow r e) (cs cl sl sa (just p) as ow r e)
body-conn cl sl sa p as ow r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go as ow {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    q = p ⊕ [ ix 1 ]
    hand : after q ≤ᴷ at q
    hand = after≤at q q [] (sym (++-identityʳ q))
    go : ∀ as ow {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {mk′} → mk′ ∈ fut (connS (cs cl sl sa nothing (just q) ow r e) o′ b′)
       → Σ (Mark × Key) λ mk → mk ∈ fut (connS (cs cl sl sa (just p) as ow r e) o b) × proj₂ mk′ ≤ᴷ proj₂ mk
    go nothing  nothing  (here refl)         = _ , here refl , hand
    go nothing  nothing  (there ())
    go nothing  (just w) (here refl)         = _ , here refl , hand
    go nothing  (just w) (there (here refl)) = _ , there (here refl) , ≤ᴷ-refl
    go nothing  (just w) (there (there ()))
    go (just a) nothing  (here refl)         = _ , here refl , hand
    go (just a) nothing  (there ())
    go (just a) (just w) (here refl)         = _ , here refl , hand
    go (just a) (just w) (there (here refl)) = _ , there (there (here refl)) , ≤ᴷ-refl
    go (just a) (just w) (there (there ()))

-- A source's attach run: its mark dropped.
src-conn : ∀ cl sl sa ba a ow r e → ConnW (cs cl sl true ba nothing ow r e) (cs cl sl sa ba (just a) ow r e)
src-conn cl sl sa ba a ow r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go ba ow {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    go : ∀ ba ow {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {mk′} → mk′ ∈ fut (connS (cs cl sl true ba nothing ow r e) o′ b′)
       → Σ (Mark × Key) λ mk → mk ∈ fut (connS (cs cl sl sa ba (just a) ow r e) o b) × proj₂ mk′ ≤ᴷ proj₂ mk
    go nothing  nothing  ()
    go nothing  (just w) (here refl)         = _ , there (here refl) , ≤ᴷ-refl
    go nothing  (just w) (there ())
    go (just p) nothing  (here refl)         = _ , here refl , ≤ᴷ-refl
    go (just p) nothing  (there ())
    go (just p) (just w) (here refl)         = _ , here refl , ≤ᴷ-refl
    go (just p) (just w) (there (here refl)) = _ , there (there (here refl)) , ≤ᴷ-refl
    go (just p) (just w) (there (there ()))

-- A source's teardown run: its mark dropped.
owed-conn : ∀ cl sl sa ba as w r e → ConnW (cs cl false sa ba as nothing r e) (cs cl sl sa ba as (just w) r e)
owed-conn cl sl sa ba as w r e = connW (λ {Γ} {X} {B} {o} {o′} {b} {b′} → nodeW (go ba as {Γ} {X} {B} {o} {o′} {b} {b′}))
  where
    go : ∀ ba as {Γ X B} {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {mk′} → mk′ ∈ fut (connS (cs cl false sa ba as nothing r e) o′ b′)
       → Σ (Mark × Key) λ mk → mk ∈ fut (connS (cs cl sl sa ba as (just w) r e) o b) × proj₂ mk′ ≤ᴷ proj₂ mk
    go nothing  nothing  ()
    go nothing  (just a) (here refl)         = _ , here refl , ≤ᴷ-refl
    go nothing  (just a) (there ())
    go (just p) nothing  (here refl)         = _ , here refl , ≤ᴷ-refl
    go (just p) nothing  (there ())
    go (just p) (just a) (here refl)         = _ , here refl , ≤ᴷ-refl
    go (just p) (just a) (there (here refl)) = _ , there (here refl) , ≤ᴷ-refl
    go (just p) (just a) (there (there ()))

conn-≼ : ∀ {Γ X B} {kk′ kk} {o′ o : St Γ X} {b′ b : St (X ∷ Γ) B} → ConnW kk′ kk → o′ ≼ o → b′ ≼ b → connS kk′ o′ b′ ≼ connS kk o b
conn-≼ cw ro rb = w≼ (conn cw) (conn≼ cw ro rb)
