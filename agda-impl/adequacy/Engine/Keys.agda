{-# OPTIONS --guardedness #-}

-- WHERE EACH NODE SITS IN THE TREE'S POSITIONS, node by node, in the
-- environment its connects give it.  `adequacy.Engine.Head.Frag` is
-- structural and says nothing of positions, so what a node's shape needs
-- of them is kept here, of the whole tree (`Keys`), and read at a hole
-- (`keyed-at`).  A tape and an of in shape; a takeWhile owing its end
-- owing it under a head, ahead of its source's tail; a connect's source
-- one past a head, its body keyed under the mark and rising past the
-- source; a merge keyed under a mark alien to its environment; a joiner's
-- feed in order ahead of its rejoined source.
--
-- REFUTED: 345be263 a joiner's feed ahead of its rejoined source, of any tree in the fragment
module adequacy.Engine.Keys where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; [_]; _ʳ++_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; ix; last; end; Timeline)
open import Tree using (Obs)
open import denotation.MonotonicList using (MonotonicList)
open import denotation.Unfold using (NEnv; stateᴺ; cutᴺ; states; outerᴺ; joined; fedᴺ)
open import operation.PureObservable using (module Machine)
open Machine using (Owe; St; coldS; ofS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import operation.AbstractObservable using (cpAt)
open import adequacy.Engine.Meaning using (vals; endOf; gh; envAt; srcG; srcRun; srcState; lane; outerG; poolG; deadL; lanesL)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Placed.Order using (Alien; Alienᴱ; Atop; Past; Clear; Disjoint; Ordered; Steady; Owned; Every; Every∞; EveryT; Headed)
open import adequacy.Placed.Trail using (Parted; Spread; Trail; TrailE)
open import adequacy.Placed.Burst using (module Bursting; Fresh; FreshRun)
open import adequacy.Placed.Walk using (module Walk)
open import adequacy.Placed.Rising using (Rise)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open Events∞

------------------------------------------------------------------------
-- Shapes

-- A run in order and steady, it and what it leaves running headed, the
-- latter trailing it.
Shape′ : ∀ {A} → Events A → Tail → Set
Shape′ x c = ((Ordered x × Steady x) × Every Headed x × EveryT Headed c) × Trail x c

Shape : ∀ {A} → Events∞ A → Set
Shape σ = Shape′ (force σ) (cut σ)

------------------------------------------------------------------------
-- A merge under its mark `p`

module _ (p : Pos) where
  open FlatOrder p using (K; Ok; Under; Aside; Pool)

  -- A lane in flight keyed under its root, beyond its shape.
  data LaneKeys {B} : List (Events∞ B) → List Pos → Set where
    []ᴷ  : LaneKeys [] []
    _∷ᴷ_ : ∀ {r l ls rs} → Every∞ (Under r) l × Ok r × Spread (force l) → LaneKeys ls rs → LaneKeys (l ∷ ls) (r ∷ rs)

  -- The outer keyed under the merge, beyond its shape, its values lanes.
  OuterKeys : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  OuterKeys nothing  = ⊤
  OuterKeys (just e) = Spread (force e) × Every∞ K e

  -- A merge in flight: its lanes and its outer keyed, its lanes parted
  -- and aside from the outer, its pool.
  FlatKeys : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → Tail → List Pos → Set
  FlatKeys o ls t rs = LaneKeys ls rs × Parted rs × All (Aside o) rs × OuterKeys o × Pool o rs t

-- A merge's outer, as its lanes' generator reads it.
outerOf : ∀ {Γ A C} (f : A → Obs Timeline Γ C) dn (s : St Γ A) (ρ : NEnv Γ) → Maybe (Events∞ (MonotonicList C))
outerOf f dn s ρ = outerᴺ (lane f) (outerG dn (gh s)) ρ

------------------------------------------------------------------------
-- A joiner

-- Each step fed a joiner and not yet shown, headed, at or before the
-- next and steady past it.
Steps : ∀ {A} → Pos → Maybe A → Events A → Set
Steps q (just _) x = Past q x
Steps q nothing  x = Clear q x

Fed : ∀ {A} → List (Pos × Maybe A) → Events A → Set
Fed []             x = ⊤
Fed ((q , a) ∷ xs) x = (Headed q × Atop q (fedᴺ xs x) × Steps q a (fedᴺ xs x)) × Fed xs x

-- Its end told under a head; else joined under a head where its source
-- has not been.
Joins : ∀ {Γ A} → A ∈ Γ → Pos → Maybe Pos → NEnv Γ → Set
Joins i p (just c) ρ = Headed c
Joins i p nothing  ρ = Headed p × Alien p (lookup ρ i)

------------------------------------------------------------------------
-- A connect

-- Its body's state and its source's.
bodyIn : ∀ {Γ X B} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Events∞ B
bodyIn k o b ρ = stateᴺ (gh b) (srcRun (srcG k o) ρ ∷ᴬ ρ)

srcIn : ∀ {Γ X} (k : CS) (o : St Γ X) (ρ : NEnv Γ) → Events∞ X
srcIn k o ρ = srcState (srcG k o) ρ

-- A source subscribed at its body's mark, under a head where no source
-- of its environment has been.
SubKeys : ∀ {Γ} → Maybe Pos → NEnv Γ → Set
SubKeys nothing  ρ = ⊤
SubKeys (just p) ρ = Headed (p ⊕ (ix 1 ∷ [])) × Alienᴱ (p ⊕ (ix 1 ∷ [])) ρ

-- An ended source ended under a head.
EndKeys : CS → Set
EndKeys (cs true sl sa nothing as ow r en) = Headed en
EndKeys _                                  = ⊤

-- Its source subscribed one past a head, its mark; its body `β` keyed
-- under the mark, rising past the source's subscription, fresh where the
-- source `σ` cues it; the source keyed under its own subscription, apart
-- from the body's; no body step under where a source step shows.
record ConnAt {Γ X B} (k : CS) (β : Events∞ B) (σ : Events∞ X) (ρ : NEnv Γ) : Set where
  field
    mark : Pos
    hm   : Headed mark
    at   : CS.srcAt k ≡ mark ++ [ ix 1 ]
    kb   : Every∞ (Owned (mark ++ [ ix 0 ])) β
    kr   : Every∞ (Rise (mark ++ [ ix 1 ])) β
    fr   : FreshRun (mark ++ [ ix 0 ]) (force β)
    cue  : Σ Pos (λ l → Owned (mark ++ [ ix 0 ]) l × Bursting.Cue (mark ++ [ ix 1 ]) l (force σ)
                      × EveryT (Fresh (mark ++ [ ix 0 ]) l) (cut β))
    ks   : Every∞ (Disjoint (mark ++ [ ix 0 ])) σ
    rs   : Every∞ (Owned (mark ++ [ ix 1 ])) σ
    ub   : Walk.UB mark hm β σ
    sub  : SubKeys (CS.bodyAt k) ρ
    ends : EndKeys k

ConnKeys : ∀ {Γ X B} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Set
ConnKeys k o b ρ = ConnAt k (bodyIn k o b ρ) (srcIn k o ρ) ρ

------------------------------------------------------------------------
-- A takeWhile and a merge, their child read as a run

-- A takeWhile owing its end owing it under a head, ahead of what its
-- source `h` leaves running.
TakeAt : ∀ {A} → Owe → Events∞ A → Set
TakeAt {A} (cpAt k) h = Headed (k ⊕ (last ∷ [])) × EveryT (TrailE (end {A} (k ⊕ (last ∷ [])))) (cut h)
TakeAt          _   h = ⊤

-- A merge keyed under a mark alien to its environment.
FlatAt : ∀ {Γ B} → NEnv Γ → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → Tail → Set
FlatAt ρ o ls t = Σ Pos (λ p → Headed p × Alienᴱ p ρ × Σ (List Pos) (FlatKeys p o ls t))

------------------------------------------------------------------------
-- The tree

-- What a node keeps of its own positions.
Here : ∀ {Γ A} → St Γ A → NEnv Γ → Set
Here (coldS b l)               ρ = Shape (stateᴺ (gh (coldS b l)) ρ)
Here (ofS i p xs)              ρ = Shape (stateᴺ (gh (ofS i p xs)) ρ)
Here (takeS i p w s)           ρ = TakeAt w (stateᴺ (gh s) ρ)
Here (connS k o b)             ρ = ConnKeys k o b ρ
Here (flatS op f dn n qs s ls) ρ = FlatAt ρ (outerOf f dn s ρ) (states (lanesL ls) ρ) (cutᴺ (poolG dn (gh s) (deadL ls)) ρ)
Here (joinS j true y ib)       ρ = Joins y j (endOf ib) ρ × Fed (vals ib) (joined y j (endOf ib) ρ)
Here _                         ρ = ⊤

-- Every node keeping its own, each in the environment its connects give it.
mutual
  Keyed : ∀ {Γ A} → St Γ A → NEnv Γ → Set
  Keyed s ρ = Here s ρ × Kids s ρ

  Kids : ∀ {Γ A} → St Γ A → NEnv Γ → Set
  Kids (mapS f s)              ρ = Keyed s ρ
  Kids (scanS f z s)           ρ = Keyed s ρ
  Kids (cutS l a s)            ρ = Keyed s ρ
  Kids (lnS b s)               ρ = Keyed s ρ
  Kids (takeS i w x s)         ρ = Keyed s ρ
  Kids (flatS op f d n q o ls) ρ = Keyed o ρ × KeyedL ls ρ
  Kids (connS k o b)           ρ = Keyed o ρ × Keyed b (srcRun (srcG k o) ρ ∷ᴬ ρ)
  Kids _                       ρ = ⊤

  KeyedL : ∀ {Γ A} → List (St Γ A) → NEnv Γ → Set
  KeyedL []       ρ = ⊤
  KeyedL (l ∷ ls) ρ = Keyed l ρ × KeyedL ls ρ

Keys : ∀ {R} → St [] R → Set
Keys t = Keyed t []ᴬ

-- The fragment, its positions kept.
Held : ∀ {R} → St [] R → Set
Held t = Frag t × Keys t

-- A list reversed onto another keeps the latter's.
keyedL-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {ys} {ρ : NEnv Γ} → KeyedL (pre ʳ++ ys) ρ → KeyedL ys ρ
keyedL-ʳ++ []        k = k
keyedL-ʳ++ (x ∷ pre) k = proj₂ (keyedL-ʳ++ pre k)

-- A hole's own, read off the whole tree's.
keyed-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Keys (plug c s) → Keyed s (envAt c)
keyed-at top                               s k = k
keyed-at (inMap f c)                       s k = proj₂ (keyed-at c (mapS f s) k)
keyed-at (inScan f z c)                    s k = proj₂ (keyed-at c (scanS f z s) k)
keyed-at (inCut l a c)                     s k = proj₂ (keyed-at c (cutS l a s) k)
keyed-at (inLn b c)                        s k = proj₂ (keyed-at c (lnS b s) k)
keyed-at (inTake i p w c)                  s k = proj₂ (keyed-at c (takeS i p w s) k)
keyed-at (inOuter op f d n q ls c)         s k = proj₁ (proj₂ (keyed-at c (flatS op f d n q s ls) k))
keyed-at (inLanes op f d n q o pre post c) s k = proj₁ (keyedL-ʳ++ pre (proj₂ (proj₂ (keyed-at c (flatS op f d n q o (pre ʳ++ s ∷ post)) k))))
keyed-at (inSrc k b c)                     s x = proj₁ (proj₂ (keyed-at c (connS k s b) x))
keyed-at (inBody k o c)                    s x = proj₂ (proj₂ (keyed-at c (connS k o s) x))

here-at : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Held (plug c s) → Here s (envAt c)
here-at c s h = proj₁ (keyed-at c s (proj₂ h))
