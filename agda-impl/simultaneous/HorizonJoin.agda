{-# OPTIONS --guardedness #-}

-- WHERE A JOIN HANGS.  A join keeps its outer's boundaries, always, and
-- each running lane's while the lane is not cut before it; a held one
-- while the lane is not cut before the connect it waits on, as a join
-- keeps that lane's pins (`JoinBd.JBd`).
--
-- A JOIN'S CUTS ARE BOUNDED (`JoinB.bounded`).  Every join row is an
-- outer row, a value's marker or a lane row, so it agrees across cuts
-- once the outer does and that value's lane does; and the join's end is
-- decided by ends at or before it, so it agrees too.  A running lane
-- uncut at a row is clear there: each of its boundaries at or before the
-- row is cut, or is the join's.  A lane's pin waits on a connect past the
-- lane's subscription, so past the value; one cut past its connect shows
-- through the lane's own pins.  Which lanes run, and where each is cut,
-- is the policy's, decided before the row.
module simultaneous.HorizonJoin where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Bool using (T)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; Label; ix; _⊕_; _≟ᵖ_; inside)
open import denotation.EmissionSet using (Ev; out; pin; EmissionSet; _≺_; _≼_; At; Ended; Den; coldAt; module Joining; module Bounded)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-ext; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≼-refl; ≼-trans; ≼-or-≻)
open import denotation.Laws.Worlds using (_⊑_; InvAt; Disj; W; W⁼; step; inW; here; plain-ix; lead; l-root; l-in; l-hot; leads;
  ⊑-snoc; ⊑-snoc⁺; ⊑-trans; ⊑-refl; ⊑-inside; ⊑-≼; inside-⊑; w-up; not-up; apart-w; nest-in; nest; nest⁼; Plain; ⊕-injʳ; ⊕-injˡ; ⊕-identityʳ)
open import simultaneous.Horizon using (Tag; free; held; module Cuts; under-child)
open import simultaneous.Placed using (module Placing)

------------------------------------------------------------------------
-- A join's boundaries

module JoinBd {A : Set} (o : EmissionSet A) (Runs : Pos → Set) (Cut : Pos → Pos → Set)
  (Bdo : Pos → Tag → Set) (BdL : Pos → A → Pos → Tag → Set) where

  data JBd : Pos → Tag → Set where
    outerB : ∀ {b g} → Bdo b g → JBd b g
    laneB  : ∀ {q a b} → o q (out a) → Runs q → BdL q a b free → ¬ Cut q b → JBd b free
    laneH  : ∀ {q a b r} → o q (out a) → Runs q → BdL q a b (held r) → ¬ Cut q r → JBd b (held r)

-- A BOUNDED MERGE'S: its lanes', each where the schedule subscribes it.
module CcJ {A B : Set} (m : ℕ) (o : ℕ → EmissionSet A) (L : A → Pos → ℕ → EmissionSet B) where

  -- The lanes at `N`, each read off its cut wherever it is subscribed.
  fD : ℕ → A → Den B
  fD N a = coldAt (λ s → L a s N)

  module BN (N : ℕ) = Bounded m (fD N) (o N)

  Jc : ℕ → EmissionSet B
  Jc N = BN.JoinT N

  -- The value at `q`'s lane's boundaries, at its subscription.
  LBd : (A → Pos → ℕ → Pos → Tag → Set) → ℕ → Pos → A → Pos → Tag → Set
  LBd BdL N q a b g = Σ ℕ λ i → Σ Pos λ s → BN.Sub N i q s a × BdL a s N b g

------------------------------------------------------------------------
-- An outer's rows, against a value's second child's world

module JoinRows {A : Set} (o : ℕ → EmissionSet A) (H : ℕ → Pos → Set) (p : Pos)
  (io : ∀ N → InvAt (H N) p (o N)) (dj : ∀ N → Disj (H N) p) where

  -- A lane's subscription lies in the join's world.
  ow : ∀ {N q a} → o N q (out a) → W (H N) p (q ⊕ [ ix 1 ])
  ow {N} x = step (inW (InvAt.world (io N) x)) plain-ix

  -- What a plain child of an outer row reaches leads no position of
  -- another child's world, unless it is that child: the two worlds are
  -- apart, and neither row lies in the other's children's.
  off-lane : ∀ {N q₀ a₀ y e l w b} → o N q₀ (out a₀) → o N y e → Plain l → W⁼ (H N) (y ⊕ [ l ]) w
           → ¬ (y ⊕ [ l ] ≡ q₀ ⊕ [ ix 1 ]) → W⁼ (H N) (q₀ ⊕ [ ix 1 ]) b → ¬ w ⊑ b
  off-lane {N} {q₀} x₀ x pl v ne wb le with lead wb le
  ... | l-in u     = apart-w pl plain-ix ne (λ z → InvAt.under (io N) x₀ x plain-ix z (⊑-refl _))
                       (λ z → InvAt.under (io N) x x₀ pl z (⊑-refl _)) v (inW u)
  ... | l-hot hh r = dj N hh (nest-in (step (inW (InvAt.world (io N) x)) pl) v) (⊑-inside r)
  ... | l-root r with ⊑-snoc q₀ r
  ...   | inj₁ wq   = InvAt.under (io N) x x₀ pl v wq
  ...   | inj₂ refl = [ ne , (λ z → InvAt.under (io N) x x₀ pl z (⊑-refl q₀)) ]′ (w-up plain-ix v)

  -- An outer row leads another only as itself.
  row-lead : ∀ {N y e q e′} → o N y e → o N q e′ → y ⊑ q → y ≡ q
  row-lead {y = y} _ _ ([] , eq) = sym (trans eq (⊕-identityʳ y))
  row-lead {N} oy oq (_ ∷ _ , refl) = ⊥-elim (InvAt.flat (io N) oy oq)

  -- A valueless outer row leads nothing in a value's second child's
  -- world: no other outer row leads that world.
  root-lo : ∀ {N q a b y e} → o N q (out a) → W (H N) (q ⊕ [ ix 1 ]) b → o N y e → (∀ {a′} → ¬ e ≡ out a′) → ¬ y ⊑ b
  root-lo {N} x wb oy ne le with lead (inW wb) le
  ... | l-hot hh r = dj N hh (InvAt.world (io N) oy) (⊑-inside r)
  ... | l-in v     = InvAt.under (io N) x oy plain-ix (inW v) (⊑-refl _)
  root-lo {N} {q} x wb oy ne le | l-root r with ⊑-snoc q r
  ...   | inj₂ refl = InvAt.flat (io N) x oy
  ...   | inj₁ yq with row-lead oy x yq
  ...     | refl = ne (InvAt.func (io N) oy x)

  -- Nor does any value's marker.
  root-lv : ∀ {N q a b y a′} → o N q (out a) → W (H N) (q ⊕ [ ix 1 ]) b → o N y (out a′) → ¬ (y ⊕ [ ix 0 ]) ⊑ b
  root-lv {N} x wb oy le with lead (inW wb) le
  ... | l-hot hh r = dj N hh (step (inW (InvAt.world (io N) oy)) plain-ix) (⊑-inside r)
  root-lv {N} {q} {y = y} x wb oy le | l-in v with w-up plain-ix (inW v)
  ...   | inj₂ v′ = InvAt.under (io N) x oy plain-ix v′ (⊑-refl y)
  ...   | inj₁ eq with ⊕-injʳ q y eq
  ...     | ()
  root-lv {N} {q} {y = y} x wb oy le | l-root r with ⊑-snoc q r
  ...   | inj₂ eq with ⊕-injʳ y q eq
  ...     | ()
  root-lv {N} {q} {y = y} x wb oy le | l-root r | inj₁ r′ with row-lead oy x (⊑-trans (⊑-snoc⁺ y) r′)
  ...     | refl = not-up {H = H N} (InvAt.real (io N) x) here r′

------------------------------------------------------------------------
-- A join's cuts

-- The join of an outer's cuts and its lanes', each value's lane
-- subscribed under its row, running and cut as the policy says.
module JoinJ {A B : Set} (o : ℕ → EmissionSet A) (L : A → Pos → ℕ → EmissionSet B)
  (Runs : ℕ → Pos → Set) (Cut : ℕ → Pos → Pos → Set) where

  Lane : ℕ → Pos → A → EmissionSet B
  Lane N = At (λ a s → L a s N)

  module J (N : ℕ) = Joining (Lane N) (o N) (λ _ _ → ⊥) (Ended (o N)) (Runs N) (Cut N) (λ _ → ⊥)

  Jc : ℕ → EmissionSet B
  Jc N = J.JoinT N

  -- Two cuts agree up to `k` on every running lane's rows it is not cut
  -- before.
  LanesAgree : ℕ → ℕ → Pos → Set
  LanesAgree N N′ k = ∀ {q a y e} → o N q (out a) → Runs N q → y ≼ k → ¬ Cut N q y
                    → (L a (q ⊕ [ ix 1 ]) N y e → L a (q ⊕ [ ix 1 ]) N′ y e) × (L a (q ⊕ [ ix 1 ]) N′ y e → L a (q ⊕ [ ix 1 ]) N y e)

-- The merge: every lane runs, none is cut.
module MergeJ {A B : Set} (o : ℕ → EmissionSet A) (L : A → Pos → ℕ → EmissionSet B) = JoinJ o L (λ _ _ → ⊤) (λ _ _ _ → ⊥)

-- WHERE A JOIN'S BOUNDARIES LIE, from where its outer's and its lanes'
-- do.
module JoinP {A B : Set} (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  (Runs : ℕ → Pos → Set) (Cut : ℕ → Pos → Pos → Set)
  (o-func : ∀ {N y e e′} → o N y e → o N y e′ → e ≡ e′)
  (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos)
  (io : ∀ N → InvAt (H N) p (o N)) (dj : ∀ N → Disj (H N) p)
  (lw : ∀ {N q a y e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → W (H N) (q ⊕ [ ix 1 ]) y)
  (po : Placing.Placed H Env p o Bdo)
  (pl : ∀ {N q a} → o N q (out a) → Placing.Placed H Env (q ⊕ [ ix 1 ]) (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  where

  open JoinJ o L Runs Cut using (Jc)
  open JoinBd using (outerB; laneB; laneH)
  open JoinRows o H p io dj using (ow; off-lane)

  MBd : ℕ → Pos → Tag → Set
  MBd N = JoinBd.JBd (o N) (Runs N) (Cut N) (Bdo N) (λ q a → BdL a (q ⊕ [ ix 1 ]) N)

  -- A join row stands on an outer row: as a valueless one, a value's
  -- marker, or a row of the value's lane.
  data Stand (N : ℕ) (y : Pos) : Set where
    on   : ∀ {q e} → o N q e → (∀ {a} → ¬ e ≡ out a) → y ≡ q → Stand N y
    mark : ∀ {q a} → o N q (out a) → y ≡ q ⊕ [ ix 0 ] → Stand N y
    inln : ∀ {q a e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → Stand N y

  stand : ∀ {N y e} → Jc N y e → Stand N y
  stand (Joining.val x)             = mark x refl
  stand (Joining.step x)            = on x (λ ()) refl
  stand (Joining.opin x)            = on x (λ ()) refl
  stand (Joining.oend x _)          = on x (λ ()) refl
  stand (Joining.opass x _)         = on x (λ ()) refl
  stand (Joining.lane x _ l _ _)    = inln x (proj₁ l)
  stand (Joining.lend x _ l _ _ _)  = inln x (proj₁ l)
  stand (Joining.lpass x _ l _ _ _) = inln x (proj₁ l)
  stand (Joining.hand _ _ _ _ ())
  stand (Joining.left x _ l _ _)    = inln x (proj₁ l)
  stand (Joining.run () _)
  stand (Joining.rend () _ _)
  stand (Joining.rpass () _ _)
  stand (Joining.rhand () _)

  -- So a plain child's world of a join row lies in a plain child's world
  -- of an outer row.
  up-to : ∀ {N y l w} → Stand N y → Plain l → W⁼ (H N) (y ⊕ [ l ]) w
        → Σ Pos λ q → Σ (Ev A) (o N q) × Σ Label λ l′ → Plain l′ × W⁼ (H N) (q ⊕ [ l′ ]) w
  up-to (on x _ refl)   pl v = _ , (_ , x) , _ , pl , v
  up-to (mark x refl)   pl v = _ , (_ , x) , ix 0 , plain-ix , nest⁼ (inW (step here pl)) v
  up-to {N} (inln x l)  pl v = _ , (_ , x) , ix 1 , plain-ix , nest⁼ (inW (step (inW (lw x l)) pl)) v

  -- A lane's own boundary, as the join's.
  lane-own : ∀ {N q₀ a₀ b g} (x₀ : o N q₀ (out a₀)) → Placing.Own H Env (q₀ ⊕ [ ix 1 ]) (L a₀ (q₀ ⊕ [ ix 1 ])) N b g
           → Placing.Own H Env p Jc N b g
  lane-own {N} {q₀} {a₀} {b} x₀ own = record
    { world  = nest (inW (ow x₀)) (OL.Own.world own)
    ; real   = OL.Own.real own
    ; holder = λ eq → nest⁼ (inW (ow x₀)) (proj₁ (OL.Own.holder own eq)) , proj₂ (OL.Own.holder own eq)
    ; under  = under }
    where
      module OL = Placing H Env (q₀ ⊕ [ ix 1 ]) (L a₀ (q₀ ⊕ [ ix 1 ]))

      wb : W⁼ (H N) (q₀ ⊕ [ ix 1 ]) b
      wb = inW (OL.Own.world own)

      at : ∀ {y l w} → Stand N y → Plain l → W⁼ (H N) (y ⊕ [ l ]) w → ¬ w ⊑ b
      at {l = l} (on {q} x nv refl) pl v = off-lane x₀ x pl v ne wb
        where
          ne : ¬ (q ⊕ [ l ] ≡ q₀ ⊕ [ ix 1 ])
          ne eq with ⊕-injˡ q q₀ eq
          ... | refl = nv (InvAt.func (io N) x x₀)
      at (mark {q} x refl) pl v =
        off-lane x₀ x plain-ix (nest⁼ (inW (step here pl)) v) (λ eq → ix01 (⊕-injʳ q q₀ eq)) wb
        where
          ix01 : ¬ ix 0 ≡ ix 1
          ix01 ()
      at (inln {q} x l) pl v with q ≟ᵖ q₀
      ... | no ne = off-lane x₀ x plain-ix (nest⁼ (inW (step (inW (lw x l)) pl)) v) (λ eq → ne (⊕-injˡ q q₀ eq)) wb
      ... | yes refl with o-func x x₀
      ...   | refl = OL.Own.under own l pl v

      under : ∀ {y e l w} → Jc N y e → Plain l → W⁼ (H N) (y ⊕ [ l ]) w → ¬ w ⊑ b
      under j = at (stand j)

  -- A JOIN'S BOUNDARIES ARE PLACED: the outer's own by the outer, every
  -- join row standing on an outer row; a lane's own in its value's
  -- child's world, under its own lane's rows by the lane and under every
  -- other row by `off-lane`.
  placed : Placing.Placed H Env p Jc MBd
  placed {N} (outerB bd) = [ (λ own → inj₁ (outer own)) , inj₂ ]′ (po bd)
    where
      module O = Placing H Env p o

      outer : ∀ {b g} → O.Own N b g → Placing.Own H Env p Jc N b g
      outer own = record
        { world = O.Own.world own ; real = O.Own.real own ; holder = O.Own.holder own
        ; under = λ j pl v le → let (_ , (_ , x) , _ , pl′ , v′) = up-to (stand j) pl v in O.Own.under own x pl′ v′ le }
  placed {N} (laneB x₀ _ bd _) = [ (λ own → inj₁ (lane-own x₀ own)) , inj₂ ]′ (pl x₀ bd)
  placed {N} (laneH x₀ _ bd _) = [ (λ own → inj₁ (lane-own x₀ own)) , inj₂ ]′ (pl x₀ bd)

module JoinB {A B : Set} (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set) (Bo : Cuts.Bounded o Bdo)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  (BL : ∀ {N q a} → o N q (out a) → Cuts.Bounded (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  (pin-after : ∀ {N M q a y r} → o N q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → (q ⊕ [ ix 1 ]) ≼ r)
  (pin-in : ∀ {N q a y r} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y (pin r) → T (inside r y))
  (o-func : ∀ {N y e e′} → o N y e → o N y e′ → e ≡ e′)
  -- each cut under hot rows `H`, its scope's boundaries `Env`
  (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos)
  (io : ∀ N → InvAt (H N) p (o N)) (dj : ∀ N → Disj (H N) p)
  (lw : ∀ {N q a y e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → W (H N) (q ⊕ [ ix 1 ]) y)
  (po : Placing.Placed H Env p o Bdo)
  (pl : ∀ {N q a} → o N q (out a) → Placing.Placed H Env (q ⊕ [ ix 1 ]) (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  (el : ∀ {N b g} → Env N b g → ∀ {w} → W⁼ (H N) p w → ¬ w ⊑ b)
  -- the policy: a cut stays cut, and both are decided before the row
  (Runs : ℕ → Pos → Set) (Cut : ℕ → Pos → Pos → Set)
  (cut-up : ∀ {N q k y} → Cut N q k → k ≼ y → Cut N q y)
  (cut→ : ∀ {N N′ k q y} → AgreeTo k (o N) (o N′) → y ≼ k → Cut N q y → Cut N′ q y)
  (cut← : ∀ {N N′ k q y} → AgreeTo k (o N) (o N′) → y ≼ k → Cut N′ q y → Cut N q y)
  (runs→ : ∀ {N N′ k q} → AgreeTo k (o N) (o N′) → JoinJ.LanesAgree o L Runs Cut N N′ k → q ≼ k → Runs N q → Runs N′ q)
  (runs← : ∀ {N N′ k q} → AgreeTo k (o N) (o N′) → JoinJ.LanesAgree o L Runs Cut N N′ k → q ≼ k → Runs N′ q → Runs N q)
  where

  open JoinJ o L Runs Cut public

  open JoinP o Bdo L BdL Runs Cut o-func H Env p io dj lw po pl using (MBd)
  open JoinRows o H p io dj using (ow; root-lo; root-lv)

  open JoinBd using (outerB; laneB; laneH)

  module SM = Cuts Jc MBd
  module SO = Cuts o Bdo
  module BO = SO.Bounded Bo
  module BLn {N q a} (x : o N q (out a)) = Cuts.Bounded (BL x)

  held-in : ∀ {N b r} → MBd N b (held r) → r ≺ b
  held-in {N} {b} (outerB bd)          = BO.held-in {N} {b} bd
  held-in {N} {b} (laneH {r = r} x _ bd _) = BLn.held-in x {N} {b} {r} bd

  held-under : ∀ {N b r} → MBd N b (held r) → r ⊑ b
  held-under {N} {b} (outerB bd)          = BO.held-under {N} {b} bd
  held-under {N} {b} (laneH {r = r} x _ bd _) = BLn.held-under x {N} {b} {r} bd

  -- Below a value's row, the value is the same in every cut agreeing there.
  below : ∀ {q k} → (q ⊕ [ ix 1 ]) ≺ k → q ≼ k
  below {q} {k} lt = ≺→≼ {q} {k} (≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) (≺→≼ {q ⊕ [ ix 1 ]} {k} lt))

  qk : ∀ {q c k} → c ≼ k → q ≺ c → q ≼ k
  qk {q} {c} {k} ck qc = ≺→≼ {q} {k} (≺-≼-≺ {q} {c} {k} qc ck)

  -- A value's marker, or a row of its lane, lies past the value.
  val≼ : ∀ {q k} → (q ⊕ [ ix 0 ]) ≼ k → q ≼ k
  val≼ {q} {k} qk′ = ≺→≼ {q} {k} (≺-≼-≺ {q} {q ⊕ [ ix 0 ]} {k} (≺-ext q []) qk′)

  lane≼ : ∀ {q y k} → (q ⊕ [ ix 1 ]) ≺ y → y ≼ k → q ≼ k
  lane≼ {q} {y} {k} sq yk = below {q} {k} (≺-≼-≺ {q ⊕ [ ix 1 ]} {y} {k} sq yk)

  -- A pin of `r` lies at or past `r`.
  pin≼ : ∀ {r y k} → T (inside r y) → y ≼ k → r ≼ k
  pin≼ {r} {y} {k} ins yk = ≼-trans {r} {y} {k} (⊑-≼ (inside-⊑ r y ins)) yk

  -- A RUNNING LANE UNCUT AT `y`, IN A JOIN CLEAR TO `k ≽ y`, IS CLEAR TO
  -- `y`: a boundary of it at or before `y` is free and uncut, or held by
  -- a connect before it and so uncut there, and either way the join's.
  lane-clear : ∀ {N q a k y} → SM.Clear N k → o N q (out a) → Runs N q → y ≼ k → ¬ Cut N q y
             → Cuts.Clear (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])) N y
  lane-clear {N} {q} {a} {k} {y} cl x rn yk nc {b} {g} bd = [ gone g bd , (λ yb → yb) ]′ (≼-or-≻ b y)
    where
      gone : ∀ g → BdL a (q ⊕ [ ix 1 ]) N b g → b ≼ y → y ≺ b
      gone free     bd′ by = ⊥-elim (≼-trans {b} {y} {k} by yk (cl (laneB x rn bd′ (λ cb → nc (cut-up cb by)))))
      gone (held r) bd′ by = ⊥-elim (≼-trans {b} {y} {k} by yk (cl (laneH x rn bd′
        (λ cr → nc (cut-up cr (≼-trans {r} {b} {y} (≺→≼ {r} {b} (BLn.held-in x {N} {b} {r} bd′)) by))))))

  lanes-agree : ∀ {N N′ k} → SM.Clear N k → N ≤ N′ → LanesAgree N N′ k
  lanes-agree {N} {N′} {k} cl le {q} {a} {y} {e} x rn yk nc =
    upto (BLn.fwd x {N} {y} (lane-clear {N} {q} {a} {k} {y} (λ {b} {g} → cl {b} {g}) x rn yk nc) le) {y} {e} (≼-refl {y})

  -- A RUNNING LANE'S PINS OF `r`, uncut at `r`, settle where the join's
  -- held boundaries of `r` lie: they are the lane's.
  lane-pins : ∀ {N N′ q a r k} → SM.Clear N r → SM.HeldClear N r k → N ≤ N′ → o N q (out a) → Runs N q → ¬ Cut N q r
            → Cuts.PinAgree (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])) r k (L a (q ⊕ [ ix 1 ]) N) (L a (q ⊕ [ ix 1 ]) N′)
  lane-pins {N} {N′} {q} {a} {r} {k} cr hr le x rn nc =
    BLn.fwd-pin x {N} {r} {k} (lane-clear {N} {q} {a} {r} {r} (λ {b} {g} → cr {b} {g}) x rn (≼-refl {r}) nc) (λ {b} bd → hr (laneH x rn bd nc)) le

  ended→ : ∀ {X} {t t′ : EmissionSet X} {k c} → AgreeTo k t t′ → c ≼ k → Ended t c → Ended t′ c
  ended→ {k = k} {c} ag ck (c₀ , x , cc) = c₀ , proj₁ (upto ag (≼-trans {c₀} {c} {k} cc ck)) x , cc

  ended← : ∀ {X} {t t′ : EmissionSet X} {k c} → AgreeTo k t t′ → c ≼ k → Ended t′ c → Ended t c
  ended← {k = k} {c} ag ck (c₀ , x , cc) = c₀ , proj₂ (upto ag (≼-trans {c₀} {c} {k} cc ck)) x , cc

  -- CLEAR, SO SETTLED: the outer by its own, each running lane where it
  -- is uncut by its own, its cut pins by its own pins.
  fwd : ∀ {N k} → SM.Clear N k → SM.Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} yk → to yk , from yk) ⟩
    where
      ago : AgreeTo k (o N) (o N′)
      ago = BO.fwd {N} {k} (λ bd → cl (outerB bd)) le

      agl : LanesAgree N N′ k
      agl = lanes-agree {N} {N′} {k} (λ {b} {g} → cl {b} {g}) le

      o→ : ∀ {y e} → y ≼ k → o N y e → o N′ y e
      o→ yk = proj₁ (upto ago yk)

      o← : ∀ {y e} → y ≼ k → o N′ y e → o N y e
      o← yk = proj₂ (upto ago yk)

      l→ : ∀ {q a y e} → o N q (out a) → Runs N q → y ≼ k → ¬ Cut N q y → Lane N q a y e → Lane N′ q a y e
      l→ x rn yk nc l = proj₁ (agl x rn yk nc) (proj₁ l) , proj₂ l

      l← : ∀ {q a y e} → o N q (out a) → Runs N q → y ≼ k → ¬ Cut N q y → Lane N′ q a y e → Lane N q a y e
      l← x rn yk nc l = proj₂ (agl x rn yk nc) (proj₁ l) , proj₂ l

      pins : ∀ {q a r} → o N q (out a) → Runs N q → ¬ Cut N q r → r ≼ k
           → Cuts.PinAgree (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])) r k (L a (q ⊕ [ ix 1 ]) N) (L a (q ⊕ [ ix 1 ]) N′)
      pins {q} {a} {r} x rn nc rk = lane-pins {N} {N′} {q} {a} {r} {k} (λ {b} m → ≼-≺-≺ {r} {k} {b} rk (cl m)) (λ {b} m → cl m) le x rn nc

      done→ : ∀ {c} → c ≼ k → J.Done N c → J.Done N′ c
      done→ {c} ck (ov , ls) = ended→ ago ck ov , lns
        where
          lns : ∀ {q a} → o N′ q (out a) → Runs N′ q → q ≺ c → ¬ Cut N′ q c → Ended (Lane N′ q a) c
          lns {q} x′ rn′ qc nc′ = c₀ , l→ x rn c₀k (λ ct → nc (cut-up ct c₀c)) l , c₀c
            where
              x = o← (qk {q} {c} {k} ck qc) x′
              rn = runs← ago agl (qk {q} {c} {k} ck qc) rn′
              nc : ¬ Cut N q c
              nc ct = nc′ (cut→ ago ck ct)
              en = ls x rn qc nc
              c₀ = proj₁ en
              l = proj₁ (proj₂ en)
              c₀c = proj₂ (proj₂ en)
              c₀k = ≼-trans {c₀} {c} {k} c₀c ck

      done← : ∀ {c} → c ≼ k → J.Done N′ c → J.Done N c
      done← {c} ck (ov , ls) = ended← ago ck ov , lns
        where
          lns : ∀ {q a} → o N q (out a) → Runs N q → q ≺ c → ¬ Cut N q c → Ended (Lane N q a) c
          lns {q} x rn qc nc = c₀ , l← x rn c₀k (λ ct → nc (cut-up ct c₀c)) l , c₀c
            where
              en = ls (o→ (qk {q} {c} {k} ck qc) x) (runs→ ago agl (qk {q} {c} {k} ck qc) rn) qc (λ ct → nc (cut← ago ck ct))
              c₀ = proj₁ en
              l = proj₁ (proj₂ en)
              c₀c = proj₂ (proj₂ en)
              c₀k = ≼-trans {c₀} {c} {k} c₀c ck

      to : ∀ {y e} → y ≼ k → Jc N y e → Jc N′ y e
      to {y} yk (Joining.val {q} x)  = Joining.val (o→ (val≼ {q} {k} yk) x)
      to yk (Joining.step x)         = Joining.step (o→ yk x)
      to yk (Joining.opin x)         = Joining.opin (o→ yk x)
      to yk (Joining.oend x d)       = Joining.oend (o→ yk x) (done→ yk d)
      to yk (Joining.opass x nd)     = Joining.opass (o→ yk x) (λ d → nd (done← yk d))
      to {y} yk (Joining.lane {q} x rn l nc w) =
        Joining.lane (o→ (lane≼ {q} {y} {k} (proj₂ l) yk) x) (runs→ ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn) (l→ x rn yk nc l) (λ ct → nc (cut← ago yk ct)) w
      to {y} yk (Joining.lend {q} x rn l nc nh d) =
        Joining.lend (o→ (lane≼ {q} {y} {k} (proj₂ l) yk) x) (runs→ ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn) (l→ x rn yk nc l) (λ ct → nc (cut← ago yk ct)) nh (done→ yk d)
      to {y} yk (Joining.lpass {q} x rn l nc nh nd) =
        Joining.lpass (o→ (lane≼ {q} {y} {k} (proj₂ l) yk) x) (runs→ ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn) (l→ x rn yk nc l) (λ ct → nc (cut← ago yk ct)) nh (λ d → nd (done← yk d))
      to yk (Joining.hand _ _ _ _ ())
      to {y} yk (Joining.left {q} {r = r} x rn l nc ins) =
        Joining.left (o→ (lane≼ {q} {y} {k} (proj₂ l) yk) x) (runs→ ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn)
          (proj₁ (pins x rn nc (pin≼ {r} {y} {k} ins yk) yk) (proj₁ l) , proj₂ l) (λ ct → nc (cut← ago (pin≼ {r} {y} {k} ins yk) ct)) ins
      to yk (Joining.run () _)
      to yk (Joining.rend () _ _)
      to yk (Joining.rpass () _ _)
      to yk (Joining.rhand () _)

      from : ∀ {y e} → y ≼ k → Jc N′ y e → Jc N y e
      from {y} yk (Joining.val {q} x) = Joining.val (o← (val≼ {q} {k} yk) x)
      from yk (Joining.step x)        = Joining.step (o← yk x)
      from yk (Joining.opin x)        = Joining.opin (o← yk x)
      from yk (Joining.oend x d)      = Joining.oend (o← yk x) (done← yk d)
      from yk (Joining.opass x nd)    = Joining.opass (o← yk x) (λ d → nd (done→ yk d))
      from {y} yk (Joining.lane {q} x′ rn′ l nc′ w) = Joining.lane x rn (l← x rn yk nc l) nc w
        where
          x = o← (lane≼ {q} {y} {k} (proj₂ l) yk) x′
          rn = runs← ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn′
          nc : ¬ Cut N q y
          nc ct = nc′ (cut→ ago yk ct)
      from {y} yk (Joining.lend {q} x′ rn′ l nc′ nh d) = Joining.lend x rn (l← x rn yk nc l) nc nh (done← yk d)
        where
          x = o← (lane≼ {q} {y} {k} (proj₂ l) yk) x′
          rn = runs← ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn′
          nc : ¬ Cut N q y
          nc ct = nc′ (cut→ ago yk ct)
      from {y} yk (Joining.lpass {q} x′ rn′ l nc′ nh nd) = Joining.lpass x rn (l← x rn yk nc l) nc nh (λ d → nd (done→ yk d))
        where
          x = o← (lane≼ {q} {y} {k} (proj₂ l) yk) x′
          rn = runs← ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn′
          nc : ¬ Cut N q y
          nc ct = nc′ (cut→ ago yk ct)
      from yk (Joining.hand _ _ _ _ ())
      from {y} yk (Joining.left {q} {r = r} x′ rn′ l nc′ ins) =
        Joining.left x rn (proj₂ (pins x rn nc rk yk) (proj₁ l) , proj₂ l) nc ins
        where
          rk = pin≼ {r} {y} {k} ins yk
          x = o← (lane≼ {q} {y} {k} (proj₂ l) yk) x′
          rn = runs← ago agl (lane≼ {q} {y} {k} (proj₂ l) yk) rn′
          nc : ¬ Cut N q r
          nc ct = nc′ (cut→ ago rk ct)
      from yk (Joining.run () _)
      from yk (Joining.rend () _ _)
      from yk (Joining.rpass () _ _)
      from yk (Joining.rhand () _)

  -- PINS OF `r` SETTLE: the outer's by its own; a lane's by its own, its
  -- value before `r`, where the outer agrees.  A lane's pin of `r` uncut
  -- at its row is uncut at `r`, so every one shows as left behind.
  fwd-pin : ∀ {N r k} → SM.Clear N r → SM.HeldClear N r k → SM.PinSettled N r k
  fwd-pin {N} {r} {k} cr hr {N′} le {y} yk = to , from
    where
      ago : AgreeTo r (o N) (o N′)
      ago = BO.fwd {N} {r} (λ bd → cr (outerB bd)) le

      agl : LanesAgree N N′ r
      agl = lanes-agree {N} {N′} {r} (λ {b} {g} → cr {b} {g}) le

      opa : (o N y (pin r) → o N′ y (pin r)) × (o N′ y (pin r) → o N y (pin r))
      opa = BO.fwd-pin {N} {r} {k} (λ bd → cr (outerB bd)) (λ bd → hr (outerB bd)) le {y} yk

      qr : ∀ {M q a} → o M q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → q ≼ r
      qr {q = q} x l = ≺→≼ {q} {r} (≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {r} (≺-ext q []) (pin-after x l))

      uncut : ∀ {M q a} → o M q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → ¬ Cut M q y → ¬ Cut M q r
      uncut x l nc ct = nc (cut-up ct (⊑-≼ (inside-⊑ r y (pin-in x l))))

      left→ : ∀ {q a} → o N q (out a) → Runs N q → Lane N q a y (pin r) → ¬ Cut N q r → T (inside r y) → Jc N′ y (pin r)
      left→ x rn l nc ins =
        Joining.left (proj₁ (upto ago (qr x (proj₁ l))) x) (runs→ ago agl (qr x (proj₁ l)) rn)
          (proj₁ (lane-pins {N} {N′} {r = r} {k} (λ {b} {g} → cr {b} {g}) (λ {b} → hr {b}) le x rn nc yk) (proj₁ l) , proj₂ l) (λ ct → nc (cut← ago (≼-refl {r}) ct)) ins

      left← : ∀ {q a} → o N′ q (out a) → Runs N′ q → Lane N′ q a y (pin r) → ¬ Cut N′ q r → T (inside r y) → Jc N y (pin r)
      left← x′ rn′ l nc′ ins = Joining.left x rn (proj₂ (lane-pins {N} {N′} {r = r} {k} (λ {b} {g} → cr {b} {g}) (λ {b} → hr {b}) le x rn nc yk) (proj₁ l) , proj₂ l) nc ins
        where
          x = proj₂ (upto ago (qr x′ (proj₁ l))) x′
          rn = runs← ago agl (qr x′ (proj₁ l)) rn′
          nc = λ ct → nc′ (cut→ ago (≼-refl {r}) ct)

      to : Jc N y (pin r) → Jc N′ y (pin r)
      to (Joining.opin x)              = Joining.opin (proj₁ opa x)
      to (Joining.lane x rn l nc w)    = left→ x rn l (uncut x (proj₁ l) nc) (pin-in x (proj₁ l))
      to (Joining.left x rn l nc ins)  = left→ x rn l nc ins
      to (Joining.run () _)

      from : Jc N′ y (pin r) → Jc N y (pin r)
      from (Joining.opin x)            = Joining.opin (proj₂ opa x)
      from (Joining.lane x rn l nc w)  = left← x rn l (uncut x (proj₁ l) nc) (pin-in x (proj₁ l))
      from (Joining.left x rn l nc ins) = left← x rn l nc ins
      from (Joining.run () _)

  -- AN OUTER BOUNDARY is led by no lane's row: the outer's own lies
  -- under no world of its rows' children, its scope's under no world
  -- position.
  gap-ol : ∀ {N b g q a y e} → Bdo N b g → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → ¬ y ⊑ b
  gap-ol bd x l with po bd
  ... | inj₁ own = Placing.Own.under own x plain-ix (inW (lw x l))
  ... | inj₂ env = el env (inW (nest-in (ow x) (inW (lw x l))))

  -- A LANE'S BOUNDARY is led by no valueless outer row: the lane's own
  -- lies in the lane's world, which no other outer row leads.
  gap-lo : ∀ {N q a b g y e} → o N q (out a) → BdL a (q ⊕ [ ix 1 ]) N b g → o N y e → (∀ {a′} → ¬ e ≡ out a′) → ¬ y ⊑ b
  gap-lo {N} x bd oy ne le with pl x bd
  ... | inj₂ env = el env (inW (InvAt.world (io N) oy)) le
  ... | inj₁ own = root-lo x (Placing.Own.world own) oy ne le

  -- Nor any value's marker.
  gap-lv : ∀ {N q a b g y a′} → o N q (out a) → BdL a (q ⊕ [ ix 1 ]) N b g → o N y (out a′) → ¬ (y ⊕ [ ix 0 ]) ⊑ b
  gap-lv {N} x bd oy le with pl x bd
  ... | inj₂ env = el env (inW (step (inW (InvAt.world (io N) oy)) plain-ix)) le
  ... | inj₁ own = root-lv x (Placing.Own.world own) oy le

  -- Nor another lane's row: two values' lanes are apart.
  gap-ll : ∀ {N q a q′ a′ b g y e} → o N q (out a) → o N q′ (out a′) → ¬ q ≡ q′
         → BdL a (q ⊕ [ ix 1 ]) N b g → L a′ (q′ ⊕ [ ix 1 ]) N y e → ¬ y ⊑ b
  gap-ll {N} {q} {q′ = q′} {y = y} x x′ ne bd l le with pl x bd
  ... | inj₂ env = el env (inW (nest-in (ow x′) (inW (lw x′ l)))) le
  ... | inj₁ own = leads dj′ (lw x′ l) nin nup (inW (Placing.Own.world own)) le
    where
      dj′ : Disj (H N) (q′ ⊕ [ ix 1 ])
      dj′ hh w ins = dj N hh (nest-in (ow x′) (inW w)) ins

      n₁ : W⁼ (H N) (q′ ⊕ [ ix 1 ]) q → ⊥
      n₁ v = InvAt.under (io N) x′ x plain-ix v (⊑-refl q)

      n₂ : W⁼ (H N) (q ⊕ [ ix 1 ]) q′ → ⊥
      n₂ v = InvAt.under (io N) x x′ plain-ix v (⊑-refl q′)

      nin : W⁼ (H N) (q ⊕ [ ix 1 ]) y → ⊥
      nin v = apart-w plain-ix plain-ix (λ eq → ne (⊕-injˡ q q′ eq)) n₁ n₂ v (inW (lw x′ l))

      nup : y ⊑ (q ⊕ [ ix 1 ]) → ⊥
      nup r with ⊑-snoc q r
      ... | inj₁ yq = InvAt.under (io N) x′ x plain-ix (inW (lw x′ l)) yq
      ... | inj₂ eq with w-up plain-ix (subst (W⁼ (H N) (q′ ⊕ [ ix 1 ])) eq (inW (lw x′ l)))
      ...   | inj₁ eq′ = ne (sym (⊕-injˡ q′ q eq′))
      ...   | inj₂ v   = n₁ v

  -- A join row is a valueless outer row, a value's marker, or a lane's
  -- row: what leads none of them leads no join row.  A value's own row
  -- is not one: it leads its lane.
  gap-row : ∀ {N b} → (∀ {y e} → o N y e → (∀ {a} → ¬ e ≡ out a) → ¬ y ⊑ b) → (∀ {y a} → o N y (out a) → ¬ (y ⊕ [ ix 0 ]) ⊑ b)
          → (∀ {q a y e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → ¬ y ⊑ b)
          → ∀ {y e} → Jc N y e → ¬ y ⊑ b
  gap-row O V Ln (Joining.val x)             = V x
  gap-row O V Ln (Joining.step x)            = O x (λ ())
  gap-row O V Ln (Joining.opin x)            = O x (λ ())
  gap-row O V Ln (Joining.oend x _)          = O x (λ ())
  gap-row O V Ln (Joining.opass x _)         = O x (λ ())
  gap-row O V Ln (Joining.lane x _ l _ _)    = Ln x (proj₁ l)
  gap-row O V Ln (Joining.lend x _ l _ _ _)  = Ln x (proj₁ l)
  gap-row O V Ln (Joining.lpass x _ l _ _ _) = Ln x (proj₁ l)
  gap-row O V Ln (Joining.hand _ _ _ _ ())
  gap-row O V Ln (Joining.left x _ l _ _)    = Ln x (proj₁ l)
  gap-row O V Ln (Joining.run () _)
  gap-row O V Ln (Joining.rend () _ _)
  gap-row O V Ln (Joining.rpass () _ _)
  gap-row O V Ln (Joining.rhand () _)

  -- A lane's boundary and a lane's row: one lane's by its own gap.
  lanes : ∀ {N q a b g} → o N q (out a) → BdL a (q ⊕ [ ix 1 ]) N b g
        → ∀ {q′ a′ y e} → o N q′ (out a′) → L a′ (q′ ⊕ [ ix 1 ]) N y e → ¬ y ⊑ b
  lanes {N} {q} x bd {q′} x′ l with q ≟ᵖ q′
  ... | no ne = gap-ll x x′ ne bd l
  ... | yes refl with o-func x x′
  ...   | refl = BLn.gap x bd l

  gap-m : ∀ {N b g y e} → MBd N b g → Jc N y e → ¬ y ⊑ b
  gap-m (outerB bd) j       = gap-row (λ x _ → BO.gap bd x) (λ x → under-child (ix 0) (BO.gap bd x)) (gap-ol bd) j
  gap-m (laneB x _ bd _) j  = gap-row (gap-lo x bd) (gap-lv x bd) (lanes x bd) j
  gap-m (laneH x _ bd _) j  = gap-row (gap-lo x bd) (gap-lv x bd) (lanes x bd) j

  bounded : SM.Bounded
  bounded = record { gap = gap-m ; held-in = λ {N} {b} {r} → held-in {N} {b} {r} ; held-under = λ {N} {b} {r} → held-under {N} {b} {r} ; fwd = fwd ; fwd-pin = λ {N} {r} {k} → fwd-pin {N} {r} {k} }
