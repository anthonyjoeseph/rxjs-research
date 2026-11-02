{-# OPTIONS --guardedness #-}

-- WHAT A SEARCH FINDS: a node's own mark, as `own` keys it, at a hole of
-- the tree searched, keyed before no other.
module adequacy.Found where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (Obs)
open import denotation.Events using (Timeline)
open import operation.Key using (Key; _<ᴷ_)
open import operation.PureObservable using (module Machine; Tape; due)
open Machine using (St; Ctx; plug; search; found; Mark; ofM; attM; bodyM; srcAttM; owedM; joinM; leafM; cpM; cutM; attAt; attached; free; cpAt; cutAt; overAt;
                    seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT; Cand; Out; alive; CS; cutT;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Least using (Lo; Keeps; mapKp; scanKp; cutKp; takeKp; outerKp; laneKp; seek-lo)

-- The marks nodes own.
data Marked {Γ : List Set} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofK   : ∀ {A} i p (xs : List A) → Marked (ofS i p xs) ofM
  attK  : ∀ {A} l p (s : St Γ A) → Marked (cutS l (attAt p) s) attM
  conK  : ∀ {X A} k (o : St Γ X) (b : St (X ∷ Γ) A) m → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Marked (connS k o b) m
  joinK : ∀ {A} j g (x : A ∈ Γ) q e ib → Marked (joinS j g x ((q , e) ∷ ib)) joinM
  leafK : ∀ {A} b (l : Tape A) → Marked (coldS b l) leafM
  stopK : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cpAt r) s) cpM
  cutK  : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cutAt r) s) cutM

-- A candidate's mark is one its node owns, its focus a hole of the tree
-- searched.
data Owned {R A} (t : St [] R) : Maybe (Cand R A) → Set₁ where
  o-none : Owned t nothing
  o-just : ∀ {Γ B c s m κ h o} → Marked {Γ} {B} s m → (m , κ) ∈ own s → plug c s ≡ t → h ≡ κ
         → Owned t (just (found (Γ , B , c , s) m κ , h , o))

first-owned : ∀ {R A t} {x y : Maybe (Cand R A)} → Owned t x → Owned t y → Owned t (first x y)
first-owned o-none                    oy                            = oy
first-owned (o-just mk mi pe hk)      o-none                        = o-just mk mi pe hk
first-owned (o-just {h = h} mk mi pe hk) (o-just {h = h′} mk′ mi′ pe′ hk′) with h′ <ᴷ h
... | true  = o-just mk′ mi′ pe′ hk′
... | false = o-just mk mi pe hk

retag-owned : ∀ {R A B t} {g : Key → Out A → Key × Out B} {x : Maybe (Cand R A)} → Keeps g → Owned t x → Owned t (retag g x)
retag-owned kp o-none                                = o-none
retag-owned kp (o-just {h = h} {o = o} mk mi pe hk) = o-just mk mi pe (trans (kp h o) hk)

race-owned : ∀ {R A B t} d n (q : List A) {x : Maybe (Cand R A)} {y : Maybe (Cand R B)} → Owned t x → Owned t y → Owned t (raceT d n q x y)
race-owned d n q o-none o-none = o-none
race-owned d n q o-none (o-just {h = k} {o = o′} mk mi pe hk) = o-just mk mi pe (trans (laneKp d n q k o′) hk)
race-owned d n q (o-just {h = h} {o = o} mk mi pe hk) o-none = o-just mk mi pe (trans (outerKp n q h o) hk)
race-owned d n q (o-just {h = h} {o = o} mk mi pe hk) (o-just {h = k} {o = o′} mk′ mi′ pe′ hk′) with h <ᴷ k
... | true  = o-just mk mi pe (trans (outerKp n q h o) hk)
... | false = o-just mk′ mi′ pe′ (trans (laneKp d n q k o′) hk′)

source-owned : ∀ {R A B t} {x : Maybe (Cand R A)} {y : Maybe (Cand R B)} → Owned t x → Owned t y → Owned t (sourceT x y)
source-owned o-none                         oy                              = oy
source-owned (o-just mk mi pe hk)           o-none                          = o-just mk mi pe hk
source-owned (o-just {h = h} mk mi pe hk)   (o-just {h = k} mk′ mi′ pe′ hk′) with h <ᴷ k
... | true  = o-just mk mi pe hk
... | false = o-just mk′ mi′ pe′ hk′

own-marked : ∀ {Γ A} (s : St Γ A) → All (λ mk → Marked s (proj₁ mk)) (own s)
own-marked (coldS b l) with due l
... | just _  = leafK b l ∷ᴬ []ᴬ
... | nothing = []ᴬ
own-marked (ofS i p [])                  = ofK i p [] ∷ᴬ []ᴬ
own-marked (ofS i p (x ∷ xs))            = ofK i p (x ∷ xs) ∷ᴬ []ᴬ
own-marked (cutS l (attAt p) s)          = attK l p s ∷ᴬ []ᴬ
own-marked (cutS l attached s)           = []ᴬ
own-marked (takeS i q (cpAt p) s)        = stopK i q p s ∷ᴬ []ᴬ
own-marked (takeS i q (cutAt p) s)       = cutK i q p s ∷ᴬ []ᴬ
own-marked (takeS i q free s)            = []ᴬ
own-marked (takeS i q (overAt p) s)      = []ᴬ
own-marked (connS k o b) with CS.bodyAt k | CS.attSrc k | CS.owedAt k
... | just _  | just _  | just _  = B ∷ᴬ S ∷ᴬ O ∷ᴬ []ᴬ
  where B = conK k o b bodyM (inj₁ refl); S = conK k o b srcAttM (inj₂ (inj₁ refl)); O = conK k o b owedM (inj₂ (inj₂ refl))
... | just _  | just _  | nothing = conK k o b bodyM (inj₁ refl) ∷ᴬ conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ []ᴬ
... | just _  | nothing | just _  = conK k o b bodyM (inj₁ refl) ∷ᴬ conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | just _  | nothing | nothing = conK k o b bodyM (inj₁ refl) ∷ᴬ []ᴬ
... | nothing | just _  | just _  = conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | nothing | just _  | nothing = conK k o b srcAttM (inj₂ (inj₁ refl)) ∷ᴬ []ᴬ
... | nothing | nothing | just _  = conK k o b owedM (inj₂ (inj₂ refl)) ∷ᴬ []ᴬ
... | nothing | nothing | nothing = []ᴬ
own-marked (joinS j g x ((q , e) ∷ ib)) = joinK j g x q e ib ∷ᴬ []ᴬ
own-marked (joinS j g x [])              = []ᴬ
own-marked (pend _ _)                    = []ᴬ
own-marked doneS                         = []ᴬ
own-marked (mapS _ _)                    = []ᴬ
own-marked (scanS _ _ _)                 = []ᴬ
own-marked (lnS _ _)                     = []ᴬ
own-marked (flatS _ _ _ _ _ _ _ _)         = []ᴬ

ownBest-owned : ∀ {R Γ A} (c : Ctx R Γ A) s ms → All (λ mk → Marked s (proj₁ mk)) ms → (∀ {mk} → mk ∈ ms → mk ∈ own s)
              → Owned (plug c s) (ownBest c s ms)
ownBest-owned c s []       []ᴬ         sub = o-none
ownBest-owned c s (_ ∷ ms) (mk ∷ᴬ mks) sub = first-owned (o-just mk (sub (here refl)) refl refl) (ownBest-owned c s ms mks (λ m → sub (there m)))

mutual
  seek-owned : ∀ {R Γ A} (c : Ctx R Γ A) s → Owned (plug c s) (seek c s)
  seek-owned c s = first-owned (ownBest-owned c s (own s) (own-marked s) (λ m → m)) (kids-owned c s)

  kids-owned : ∀ {R Γ A} (c : Ctx R Γ A) s → Owned (plug c s) (kids c s)
  kids-owned c (mapS f s)              = retag-owned (mapKp f) (seek-owned (inMap f c) s)
  kids-owned c (scanS f z s)           = retag-owned (scanKp f z) (seek-owned (inScan f z c) s)
  kids-owned c (cutS l a s)            = retag-owned (cutKp l) (seek-owned (inCut l a c) s)
  kids-owned c (lnS b s)               = seek-owned (inLn b c) s
  kids-owned c (takeS i q w s)         = retag-owned (takeKp i q w) (seek-owned (inTake i q w c) s)
  kids-owned c (flatS op f ω d n q o ls) = race-owned d n q (seek-owned (inOuter op f ω d n q ls c) o) (lanes-owned c op f ω d n q o [] ls)
  kids-owned c (connS k o b)           = source-owned (seek-owned (inSrc k b c) o) (seek-owned (inBody k o c) b)
  kids-owned c (pend _ _)              = o-none
  kids-owned c (coldS _ _)             = o-none
  kids-owned c (ofS _ _ _)             = o-none
  kids-owned c doneS                   = o-none
  kids-owned c (joinS _ _ _ _)         = o-none

  lanes-owned : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) ω d n q o pre ls
              → Owned (plug c (flatS op f ω d n q o (pre ʳ++ ls))) (lanes c op f ω d n q o pre ls)
  lanes-owned c op f ω d n q o pre []         = o-none
  lanes-owned c op f ω d n q o pre (s ∷ post) =
    first-owned (retag-owned (cutKp (alive s)) (seek-owned (inLanes op f ω d n q o pre post c) s)) (lanes-owned c op f ω d n q o (s ∷ pre) post)

found-of : ∀ {R B t} {x : Maybe (Cand R B)} {Γ A c′ s′ m κ}
         → Owned t x → mapᴹ proj₁ x ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m × plug c′ s′ ≡ t
found-of o-none               ()
found-of (o-just mk _ pe _) refl = mk , pe

-- The found mark's own key, and no mark of the tree keyed before it.
found-least : ∀ {R} {t : St [] R} {Γ A c′ s′ m κ}
            → search top t ≡ just (found (Γ , A , c′ , s′) m κ) → (m , κ) ∈ own s′ × Lo t κ
found-least {t = t} fd with seek top t in sk | seek-owned top t
found-least refl | just _ | o-just _ mi _ refl = mi , seek-lo top _ sk

-- WHAT A SEARCH FINDS: a node's own mark, as `own` keys it, at a hole of
-- the tree searched.
found-mark : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m
found-mark c s fd = proj₁ (found-of (seek-owned top (plug c s)) fd)

found-plug : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ}
           → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → plug c′ s′ ≡ plug c s
found-plug c s fd = proj₂ (found-of (seek-owned top (plug c s)) fd)
