{-# OPTIONS --guardedness #-}

-- THE KEY A SEARCH FINDS IS THE LEAST: no mark any node of the tree owns
-- is keyed strictly before it.  Every frame passes its child's key up
-- unchanged and races its children by `<ᴷ`, so the winner is a minimum.
module adequacy.Least where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import operation.Key using (Key; _<ᴷ_; clash; ≮ᴷ-trans; <ᴷ-trans; <ᴷ-irrefl)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Mark; own; ownBest; seek; kids; lanes; first; retag; raceT; sourceT; Cand; Out;
                    mapT; scanT; cutT; takeT; outerT; laneT; alive; plug; still; shows; nx; cp; free; cpAt; cutAt; overAt;
                    coldS; ofS; doneS; pend; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)

------------------------------------------------------------------------
-- The keys a tree's marks carry

mutual
  -- `κ` keys a mark some node of `s` owns.
  data KeyIn : ∀ {Γ A} → St Γ A → Key → Set₁ where
    k-own : ∀ {Γ A} {s : St Γ A} {m κ} → (m , κ) ∈ own s → KeyIn s κ
    k-kid : ∀ {Γ A} {s : St Γ A} {κ} → KidIn s κ → KeyIn s κ

  -- … one a child's subtree owns.
  data KidIn : ∀ {Γ A} → St Γ A → Key → Set₁ where
    k-map   : ∀ {Γ A B} {f : A → B} {s : St Γ A} {κ} → KeyIn s κ → KidIn (mapS f s) κ
    k-scan  : ∀ {Γ A B} {f : B → A → B} {z} {s : St Γ A} {κ} → KeyIn s κ → KidIn (scanS f z s) κ
    k-cut   : ∀ {Γ A} {l a} {s : St Γ A} {κ} → KeyIn s κ → KidIn (cutS l a s) κ
    k-ln    : ∀ {Γ A} {b} {s : St Γ A} {κ} → KeyIn s κ → KidIn (lnS b s) κ
    k-take  : ∀ {Γ A} {i q w} {s : St Γ A} {κ} → KeyIn s κ → KidIn (takeS i q w s) κ
    k-outer : ∀ {Γ A B} {op f ω d n q} {o : St Γ A} {ls : List (St Γ B)} {κ} → KeyIn o κ → KidIn (flatS op f ω d n q o ls) κ
    k-lane  : ∀ {Γ A B} {op f ω d n q} {o : St Γ A} {ls : List (St Γ B)} {s κ} → s ∈ ls → KeyIn s κ → KidIn (flatS op f ω d n q o ls) κ
    k-src   : ∀ {Γ X B} {k} {o : St Γ X} {b : St (X ∷ Γ) B} {κ} → KeyIn o κ → KidIn (connS k o b) κ
    k-body  : ∀ {Γ X B} {k} {o : St Γ X} {b : St (X ∷ Γ) B} {κ} → KeyIn b κ → KidIn (connS k o b) κ

-- No key of `s` strictly before `h`.
Lo : ∀ {Γ A} → St Γ A → Key → Set₁
Lo s h = ∀ {κ} → KeyIn s κ → κ <ᴷ h ≡ false

------------------------------------------------------------------------
-- A candidate's key bounds a key from below

keyOf : ∀ {R A} → Maybe (Cand R A) → Maybe Key
keyOf nothing            = nothing
keyOf (just (_ , h , _)) = just h

Below : Maybe Key → Key → Set
Below nothing  κ = ⊥
Below (just h) κ = κ <ᴷ h ≡ false

-- The least so far, kept or beaten.
beat : ∀ κ h h′ → h′ <ᴷ h ≡ true → κ <ᴷ h ≡ false → κ <ᴷ h′ ≡ false
beat κ h h′ lt nb with κ <ᴷ h′ in e
... | false = refl
... | true  = ⊥-elim (clash (<ᴷ-trans κ h′ h e lt) nb)

first-l : ∀ {R A} (x y : Maybe (Cand R A)) {κ} → Below (keyOf x) κ → Below (keyOf (first x y)) κ
first-l (just _)           nothing             b = b
first-l (just (f , h , o)) (just (g , h′ , o′)) {κ} b with h′ <ᴷ h in e
... | true  = beat κ h h′ e b
... | false = b

first-r : ∀ {R A} (x y : Maybe (Cand R A)) {κ} → Below (keyOf y) κ → Below (keyOf (first x y)) κ
first-r nothing            (just _)            b = b
first-r (just (f , h , o)) (just (g , h′ , o′)) {κ} b with h′ <ᴷ h in e
... | true  = b
... | false = ≮ᴷ-trans κ h′ h b e

keep : ∀ κ {h h′} → h′ ≡ h → κ <ᴷ h ≡ false → κ <ᴷ h′ ≡ false
keep κ refl b = b

-- Every frame's retag keeps the key.
Keeps : ∀ {A B} → (Key → Out A → Key × Out B) → Set
Keeps t = ∀ h o → proj₁ (t h o) ≡ h

retag-b : ∀ {R A B} {t : Key → Out A → Key × Out B} → Keeps t → ∀ (x : Maybe (Cand R A)) {κ}
        → Below (keyOf x) κ → Below (keyOf (retag t x)) κ
retag-b kp (just (f , h , o)) {κ} b = keep κ (kp h o) b

mapKp : ∀ {A B} (f : A → B) → Keeps (mapT f)
mapKp f h still     = refl
mapKp f h (shows _) = refl

scanKp : ∀ {A B} (f : B → A → B) z → Keeps (scanT f z)
scanKp f z h still          = refl
scanKp f z h (shows (nx _)) = refl
scanKp f z h (shows cp)     = refl

cutKp : ∀ {A} l → Keeps (cutT {A} l)
cutKp l h o = refl

takeKp : ∀ {A} i (q : A → Bool) w → Keeps (takeT i q w)
takeKp i q free       h still          = refl
takeKp i q free       h (shows (nx _)) = refl
takeKp i q free       h (shows cp)     = refl
takeKp i q (cpAt _)   h o              = refl
takeKp i q (cutAt _)  h o              = refl
takeKp i q (overAt _) h o              = refl

outerKp : ∀ {A B : Set} n (q : List A) → Keeps (outerT {A} {B} n q)
outerKp n q h still          = refl
outerKp n q h (shows (nx _)) = refl
outerKp n q h (shows cp)     = refl

laneKp : ∀ {A B : Set} d n (q : List A) → Keeps (laneT {A} {B} d n q)
laneKp d n []      h still          = refl
laneKp d n []      h (shows (nx _)) = refl
laneKp d n []      h (shows cp)     = refl
laneKp d n (_ ∷ _) h still          = refl
laneKp d n (_ ∷ _) h (shows (nx _)) = refl
laneKp d n (_ ∷ _) h (shows cp)     = refl

race-l : ∀ {R A B} d n (q : List A) (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) {κ}
       → Below (keyOf x) κ → Below (keyOf (raceT d n q x y)) κ
race-l d n q (just (f , h , o)) nothing {κ} b = keep κ (outerKp n q h o) b
race-l d n q (just (f , h , o)) (just (g , k , o′)) {κ} b with h <ᴷ k in e
... | true  = keep κ (outerKp n q h o) b
... | false = keep κ (laneKp d n q k o′) (≮ᴷ-trans κ h k b e)

race-r : ∀ {R A B} d n (q : List A) (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) {κ}
       → Below (keyOf y) κ → Below (keyOf (raceT d n q x y)) κ
race-r d n q nothing (just (g , k , o′)) {κ} b = keep κ (laneKp d n q k o′) b
race-r d n q (just (f , h , o)) (just (g , k , o′)) {κ} b with h <ᴷ k in e
... | true  = keep κ (outerKp n q h o) (beat κ k h e b)
... | false = keep κ (laneKp d n q k o′) b

source-l : ∀ {R A B} (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) {κ}
         → Below (keyOf x) κ → Below (keyOf (sourceT x y)) κ
source-l (just _)           nothing             b = b
source-l (just (f , h , o)) (just (g , k , o′)) {κ} b with h <ᴷ k in e
... | true  = b
... | false = ≮ᴷ-trans κ h k b e

source-r : ∀ {R A B} (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) {κ}
         → Below (keyOf y) κ → Below (keyOf (sourceT x y)) κ
source-r nothing            (just _)            b = b
source-r (just (f , h , o)) (just (g , k , o′)) {κ} b with h <ᴷ k in e
... | true  = beat κ k h e b
... | false = b

------------------------------------------------------------------------
-- THE SEARCH'S KEY IS THE LEAST

own-b : ∀ {R Γ A} (c : Ctx R Γ A) s ms {m κ} → (m , κ) ∈ ms → Below (keyOf (ownBest c s ms)) κ
own-b c s ((m , κ) ∷ ms) (here refl) = first-l (just _) (ownBest c s ms) (<ᴷ-irrefl κ)
own-b c s (_ ∷ ms)       (there mk)  = first-r (just _) (ownBest c s ms) (own-b c s ms mk)

mutual
  seek-b : ∀ {R Γ A} (c : Ctx R Γ A) s {κ} → KeyIn s κ → Below (keyOf (seek c s)) κ
  seek-b c s (k-own mk) = first-l (ownBest c s (own s)) (kids c s) (own-b c s (own s) mk)
  seek-b c s (k-kid ki) = first-r (ownBest c s (own s)) (kids c s) (kids-b c s ki)

  kids-b : ∀ {R Γ A} (c : Ctx R Γ A) s {κ} → KidIn s κ → Below (keyOf (kids c s)) κ
  kids-b c (mapS f s)    (k-map ki)  = retag-b (mapKp f) (seek (inMap f c) s) (seek-b (inMap f c) s ki)
  kids-b c (scanS f z s) (k-scan ki) = retag-b (scanKp f z) (seek (inScan f z c) s) (seek-b (inScan f z c) s ki)
  kids-b c (cutS l a s)  (k-cut ki)  = retag-b (cutKp l) (seek (inCut l a c) s) (seek-b (inCut l a c) s ki)
  kids-b c (lnS b s)     (k-ln ki)   = seek-b (inLn b c) s ki
  kids-b c (takeS i q w s) (k-take ki) = retag-b (takeKp i q w) (seek (inTake i q w c) s) (seek-b (inTake i q w c) s ki)
  kids-b c (flatS op f ω d n q o ls) (k-outer ki) =
    race-l d n q (seek (inOuter op f ω d n q ls c) o) (lanes c op f ω d n q o [] ls) (seek-b (inOuter op f ω d n q ls c) o ki)
  kids-b c (flatS op f ω d n q o ls) (k-lane mem ki) =
    race-r d n q (seek (inOuter op f ω d n q ls c) o) (lanes c op f ω d n q o [] ls) (lanes-b c op f ω d n q o [] ls mem ki)
  kids-b c (connS k o b) (k-src ki)  = source-l (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-b (inSrc k b c) o ki)
  kids-b c (connS k o b) (k-body ki) = source-r (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-b (inBody k o c) b ki)

  lanes-b : ∀ {R Γ A B} (c : Ctx R Γ B) op f ω d n (q : List A) (o : St Γ A) pre (ls : List (St Γ B)) {s κ}
          → s ∈ ls → KeyIn s κ → Below (keyOf (lanes c op f ω d n q o pre ls)) κ
  lanes-b c op f ω d n q o pre (s ∷ post) (here refl) ki =
    first-l (retag (cutT (alive s)) (seek (inLanes op f ω d n q o pre post c) s)) (lanes c op f ω d n q o (s ∷ pre) post)
            (retag-b (cutKp (alive s)) (seek (inLanes op f ω d n q o pre post c) s) (seek-b (inLanes op f ω d n q o pre post c) s ki))
  lanes-b c op f ω d n q o pre (s ∷ post) (there mem) ki =
    first-r (retag (cutT (alive s)) (seek (inLanes op f ω d n q o pre post c) s)) (lanes c op f ω d n q o (s ∷ pre) post)
            (lanes-b c op f ω d n q o (s ∷ pre) post mem ki)

-- What the search finds, keyed `h`, is keyed no later than any mark.
seek-lo : ∀ {R Γ A} (c : Ctx R Γ A) s {f h o} → seek c s ≡ just (f , h , o) → Lo s h
seek-lo c s eq ki with seek c s | seek-b c s ki
seek-lo c s refl ki | just _ | b = b

-- A search that finds nothing: no node owns a mark.
seek-none : ∀ {R Γ A} (c : Ctx R Γ A) s → seek c s ≡ nothing → ∀ {κ} → KeyIn s κ → ⊥
seek-none c s eq ki with seek c s | seek-b c s ki
seek-none c s refl ki | nothing | ()
