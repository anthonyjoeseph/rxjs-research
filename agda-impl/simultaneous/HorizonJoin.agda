{-# OPTIONS --guardedness #-}

-- WHERE A JOIN HANGS.  A join keeps its outer's boundaries, always, and
-- each running lane's while the lane is not cut before it; a held one
-- while the lane is not cut before the connect it waits on, as a join
-- keeps that lane's pins (`JoinBd.JBd`).
--
-- THE MERGE'S CUTS ARE BOUNDED (`MergeB.bounded`).  Every merge row is an
-- outer row, a value's marker or a lane row, so it agrees across cuts
-- once the outer does and that value's lane does; and the merge's end is
-- decided by ends at or before it, so it agrees too.  A lane's pin waits
-- on a connect past the lane's subscription, so past the value.
module simultaneous.HorizonJoin where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; Label; ix; _⊕_; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; pin; EmissionSet; _≺_; _≼_; At; Ended; module Joining)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-ext; ≺→≼; ≺-≼-≺; ≼-refl; ≼-trans)
open import denotation.Laws.Worlds using (_⊑_; InvAt; Disj; W; W⁼; step; inW; here; plain-ix; lead; l-root; l-in; l-hot; leads;
  ⊑-snoc; ⊑-snoc⁺; ⊑-trans; ⊑-refl; ⊑-inside; w-up; not-up; apart-w; nest-in; nest; nest⁼; Plain; ⊕-injʳ; ⊕-injˡ; ⊕-identityʳ)
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

------------------------------------------------------------------------
-- The merge's cuts

-- The merge of an outer's cuts and its lanes', each value's lane
-- subscribed under its row.
module MergeJ {A B : Set} (o : ℕ → EmissionSet A) (L : A → Pos → ℕ → EmissionSet B) where

  Lane : ℕ → Pos → A → EmissionSet B
  Lane N = At (λ a s → L a s N)

  module J (N : ℕ) = Joining (Lane N) (o N) (λ _ _ → ⊥) (Ended (o N)) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥)

  Jc : ℕ → EmissionSet B
  Jc N = J.JoinT N

-- WHERE THE MERGE'S BOUNDARIES LIE, from where its outer's and its
-- lanes' do.
module MergeP {A B : Set} (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  (o-func : ∀ {N y e e′} → o N y e → o N y e′ → e ≡ e′)
  (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos)
  (io : ∀ N → InvAt (H N) p (o N)) (dj : ∀ N → Disj (H N) p)
  (lw : ∀ {N q a y e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → W (H N) (q ⊕ [ ix 1 ]) y)
  (po : Placing.Placed H Env p o Bdo)
  (pl : ∀ {N q a} → o N q (out a) → Placing.Placed H Env (q ⊕ [ ix 1 ]) (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  where

  open MergeJ o L using (Jc)
  open JoinBd using (outerB; laneB; laneH)

  MBd : ℕ → Pos → Tag → Set
  MBd N = JoinBd.JBd (o N) (λ _ → ⊤) (λ _ _ → ⊥) (Bdo N) (λ q a → BdL a (q ⊕ [ ix 1 ]) N)

  -- A lane's subscription lies in the merge's world.
  ow : ∀ {N q a} → o N q (out a) → W (H N) p (q ⊕ [ ix 1 ])
  ow {N} x = step (inW (InvAt.world (io N) x)) plain-ix

  -- A merge row stands on an outer row: as a valueless one, a value's
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

  -- So a plain child's world of a merge row lies in a plain child's world
  -- of an outer row.
  up-to : ∀ {N y l w} → Stand N y → Plain l → W⁼ (H N) (y ⊕ [ l ]) w
        → Σ Pos λ q → Σ (Ev A) (o N q) × Σ Label λ l′ → Plain l′ × W⁼ (H N) (q ⊕ [ l′ ]) w
  up-to (on x _ refl)   pl v = _ , (_ , x) , _ , pl , v
  up-to (mark x refl)   pl v = _ , (_ , x) , ix 0 , plain-ix , nest⁼ (inW (step here pl)) v
  up-to {N} (inln x l)  pl v = _ , (_ , x) , ix 1 , plain-ix , nest⁼ (inW (step (inW (lw x l)) pl)) v

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

  -- A lane's own boundary, as the merge's.
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

  -- THE MERGE'S BOUNDARIES ARE PLACED: the outer's own by the outer, every
  -- merge row standing on an outer row; a lane's own in its value's
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

module MergeB {A B : Set} (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set) (Bo : Cuts.Bounded o Bdo)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  (BL : ∀ {N q a} → o N q (out a) → Cuts.Bounded (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  (pin-after : ∀ {N M q a y r} → o N q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → (q ⊕ [ ix 1 ]) ≼ r)
  (o-func : ∀ {N y e e′} → o N y e → o N y e′ → e ≡ e′)
  -- each cut under hot rows `H`, its scope's boundaries `Env`
  (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos)
  (io : ∀ N → InvAt (H N) p (o N)) (dj : ∀ N → Disj (H N) p)
  (lw : ∀ {N q a y e} → o N q (out a) → L a (q ⊕ [ ix 1 ]) N y e → W (H N) (q ⊕ [ ix 1 ]) y)
  (po : Placing.Placed H Env p o Bdo)
  (pl : ∀ {N q a} → o N q (out a) → Placing.Placed H Env (q ⊕ [ ix 1 ]) (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  (el : ∀ {N b g} → Env N b g → ∀ {w} → W⁼ (H N) p w → ¬ w ⊑ b)
  where

  open MergeJ o L public

  open MergeP o Bdo L BdL o-func H Env p io dj lw po pl using (MBd; ow)

  open JoinBd using (outerB; laneB; laneH)

  module SM = Cuts Jc MBd
  module SO = Cuts o Bdo
  module BO = SO.Bounded Bo
  module BLn {N q a} (x : o N q (out a)) = Cuts.Bounded (BL x)

  -- A lane's boundary is the merge's.
  lane-of : ∀ {N q a b} g → o N q (out a) → BdL a (q ⊕ [ ix 1 ]) N b g → MBd N b g
  lane-of free     x bd = laneB x tt bd (λ ())
  lane-of (held r) x bd = laneH x tt bd (λ ())

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

  -- Two cuts agreeing on the outer and on each value's lane up to `k`
  -- agree on the merge.
  module Step {N N′ k} (ago : AgreeTo k (o N) (o N′))
    (agl : ∀ {q a} → o N q (out a) → AgreeTo k (Lane N q a) (Lane N′ q a)) where

    o→ : ∀ {y e} → y ≼ k → o N y e → o N′ y e
    o→ yk = proj₁ (upto ago yk)

    o← : ∀ {y e} → y ≼ k → o N′ y e → o N y e
    o← yk = proj₂ (upto ago yk)

    ended→ : ∀ {X} {t t′ : EmissionSet X} {c} → AgreeTo k t t′ → c ≼ k → Ended t c → Ended t′ c
    ended→ {c = c} ag ck (c₀ , x , cc) = c₀ , proj₁ (upto ag (≼-trans {c₀} {c} {k} cc ck)) x , cc

    ended← : ∀ {X} {t t′ : EmissionSet X} {c} → AgreeTo k t t′ → c ≼ k → Ended t′ c → Ended t c
    ended← {c = c} ag ck (c₀ , x , cc) = c₀ , proj₂ (upto ag (≼-trans {c₀} {c} {k} cc ck)) x , cc

    done→ : ∀ {c} → c ≼ k → J.Done N c → J.Done N′ c
    done→ {c} ck (ov , ls) =
      ended→ ago ck ov , λ {q} x′ _ qc _ → ended→ (agl (o← (qk {q} {c} {k} ck qc) x′)) ck (ls (o← (qk {q} {c} {k} ck qc) x′) tt qc (λ ()))

    done← : ∀ {c} → c ≼ k → J.Done N′ c → J.Done N c
    done← {c} ck (ov , ls) =
      ended← ago ck ov , λ {q} x _ qc _ → ended← (agl x) ck (ls (o→ (qk {q} {c} {k} ck qc) x) tt qc (λ ()))

    -- A value's marker, or a row of its lane, lies past the value.
    val≼ : ∀ {q y} → (q ⊕ [ ix 0 ]) ≼ y → y ≼ k → q ≼ k
    val≼ {q} {y} qy yk = ≺→≼ {q} {k} (≺-≼-≺ {q} {q ⊕ [ ix 0 ]} {k} (≺-ext q []) (≼-trans {q ⊕ [ ix 0 ]} {y} {k} qy yk))

    lane≼ : ∀ {q y} → (q ⊕ [ ix 1 ]) ≺ y → y ≼ k → q ≼ k
    lane≼ {q} {y} sq yk = below {q} {k} (≺-≼-≺ {q ⊕ [ ix 1 ]} {y} {k} sq yk)

    l→ : ∀ {q a y e} (x : o N q (out a)) → y ≼ k → Lane N q a y e → Lane N′ q a y e
    l→ x yk = proj₁ (upto (agl x) yk)

    l← : ∀ {q a y e} (x : o N q (out a)) → y ≼ k → Lane N′ q a y e → Lane N q a y e
    l← x yk = proj₂ (upto (agl x) yk)

    to : ∀ {y e} → y ≼ k → Jc N y e → Jc N′ y e
    to {y} yk (Joining.val {q} x)  = Joining.val (o→ (val≼ {q} {y} (≼-refl {y}) yk) x)
    to yk (Joining.step x)         = Joining.step (o→ yk x)
    to yk (Joining.opin x)         = Joining.opin (o→ yk x)
    to yk (Joining.oend x d)       = Joining.oend (o→ yk x) (done→ yk d)
    to yk (Joining.opass x nd)     = Joining.opass (o→ yk x) (λ d → nd (done← yk d))
    to {y} yk (Joining.lane {q} x _ l nc w) = Joining.lane (o→ (lane≼ {q} {y} (proj₂ l) yk) x) tt (l→ x yk l) nc w
    to {y} yk (Joining.lend {q} x _ l nc nh d) = Joining.lend (o→ (lane≼ {q} {y} (proj₂ l) yk) x) tt (l→ x yk l) nc nh (done→ yk d)
    to {y} yk (Joining.lpass {q} x _ l nc nh nd) = Joining.lpass (o→ (lane≼ {q} {y} (proj₂ l) yk) x) tt (l→ x yk l) nc nh (λ d → nd (done← yk d))
    to yk (Joining.hand _ _ _ _ ())
    to {y} yk (Joining.left {q} x _ l nc ins) = Joining.left (o→ (lane≼ {q} {y} (proj₂ l) yk) x) tt (l→ x yk l) nc ins
    to yk (Joining.run () _)
    to yk (Joining.rend () _ _)
    to yk (Joining.rpass () _ _)
    to yk (Joining.rhand () _)

    from : ∀ {y e} → y ≼ k → Jc N′ y e → Jc N y e
    from {y} yk (Joining.val {q} x) = Joining.val (o← (val≼ {q} {y} (≼-refl {y}) yk) x)
    from yk (Joining.step x)        = Joining.step (o← yk x)
    from yk (Joining.opin x)        = Joining.opin (o← yk x)
    from yk (Joining.oend x d)      = Joining.oend (o← yk x) (done← yk d)
    from yk (Joining.opass x nd)    = Joining.opass (o← yk x) (λ d → nd (done→ yk d))
    from {y} yk (Joining.lane {q} x′ _ l nc w) = Joining.lane x tt (l← x yk l) nc w
      where x = o← (lane≼ {q} {y} (proj₂ l) yk) x′
    from {y} yk (Joining.lend {q} x′ _ l nc nh d) = Joining.lend x tt (l← x yk l) nc nh (done← yk d)
      where x = o← (lane≼ {q} {y} (proj₂ l) yk) x′
    from {y} yk (Joining.lpass {q} x′ _ l nc nh nd) = Joining.lpass x tt (l← x yk l) nc nh (λ d → nd (done→ yk d))
      where x = o← (lane≼ {q} {y} (proj₂ l) yk) x′
    from yk (Joining.hand _ _ _ _ ())
    from {y} yk (Joining.left {q} x′ _ l nc ins) = Joining.left x tt (l← x yk l) nc ins
      where x = o← (lane≼ {q} {y} (proj₂ l) yk) x′
    from yk (Joining.run () _)
    from yk (Joining.rend () _ _)
    from yk (Joining.rpass () _ _)
    from yk (Joining.rhand () _)

  -- A lane agreeing up to `k`, read past its subscription.
  at-ag : ∀ {N N′ k q a} → AgreeTo k (L a (q ⊕ [ ix 1 ]) N) (L a (q ⊕ [ ix 1 ]) N′) → AgreeTo k (Lane N q a) (Lane N′ q a)
  at-ag ag = ⟨ (λ yk → (λ l → proj₁ (upto ag yk) (proj₁ l) , proj₂ l) , (λ l → proj₂ (upto ag yk) (proj₁ l) , proj₂ l)) ⟩

  -- CLEAR, SO SETTLED: the outer by its own, each value's lane by its own.
  fwd : ∀ {N k} → SM.Clear N k → SM.Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} yk → S.to yk , S.from yk) ⟩
    where
      ago : AgreeTo k (o N) (o N′)
      ago = BO.fwd {N} {k} (λ bd → cl (outerB bd)) le

      agl : ∀ {q a} → o N q (out a) → AgreeTo k (Lane N q a) (Lane N′ q a)
      agl x = at-ag (BLn.fwd x {N} {k} (λ {b} {g} bd → cl (lane-of g x bd)) le)

      module S = Step ago agl

  -- PINS OF `r` SETTLE: the outer's by its own; a lane's by its own, its
  -- value before `r`, where the outer agrees.
  fwd-pin : ∀ {N r k} → SM.Clear N r → SM.HeldClear N r k → SM.PinSettled N r k
  fwd-pin {N} {r} {k} cr hr {N′} le {y} yk = to , from
    where
      ago : AgreeTo r (o N) (o N′)
      ago = BO.fwd {N} {r} (λ bd → cr (outerB bd)) le

      opa : (o N y (pin r) → o N′ y (pin r)) × (o N′ y (pin r) → o N y (pin r))
      opa = BO.fwd-pin {N} {r} {k} (λ bd → cr (outerB bd)) (λ bd → hr (outerB bd)) le {y} yk

      lpa : ∀ {q a} (x : o N q (out a)) → (L a (q ⊕ [ ix 1 ]) N y (pin r) → L a (q ⊕ [ ix 1 ]) N′ y (pin r)) × (L a (q ⊕ [ ix 1 ]) N′ y (pin r) → L a (q ⊕ [ ix 1 ]) N y (pin r))
      lpa x = BLn.fwd-pin x {N} {r} {k} (λ {b} {g} bd → cr (lane-of g x bd)) (λ {b} bd → hr (laneH x tt bd (λ ()))) le {y} yk

      qr : ∀ {M q a} → o M q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → q ≼ r
      qr {q = q} x l = ≺→≼ {q} {r} (≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {r} (≺-ext q []) (pin-after x l))

      to : Jc N y (pin r) → Jc N′ y (pin r)
      to (Joining.opin x)              = Joining.opin (proj₁ opa x)
      to (Joining.lane x _ l nc w)     = Joining.lane (proj₁ (upto ago (qr x (proj₁ l))) x) tt (proj₁ (lpa x) (proj₁ l) , proj₂ l) nc w
      to (Joining.left x _ l nc ins)   = Joining.left (proj₁ (upto ago (qr x (proj₁ l))) x) tt (proj₁ (lpa x) (proj₁ l) , proj₂ l) nc ins
      to (Joining.run () _)

      from : Jc N′ y (pin r) → Jc N y (pin r)
      from (Joining.opin x)            = Joining.opin (proj₂ opa x)
      from (Joining.lane x′ _ l nc w)  = Joining.lane x tt (proj₂ (lpa x) (proj₁ l) , proj₂ l) nc w
        where x = proj₂ (upto ago (qr x′ (proj₁ l))) x′
      from (Joining.left x′ _ l nc ins) = Joining.left x tt (proj₂ (lpa x) (proj₁ l) , proj₂ l) nc ins
        where x = proj₂ (upto ago (qr x′ (proj₁ l))) x′
      from (Joining.run () _)

  -- An outer row leads another only as itself.
  row-lead : ∀ {N y e q e′} → o N y e → o N q e′ → y ⊑ q → y ≡ q
  row-lead {y = y} _ _ ([] , eq) = sym (trans eq (⊕-identityʳ y))
  row-lead {N} oy oq (_ ∷ _ , refl) = ⊥-elim (InvAt.flat (io N) oy oq)

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
  ... | inj₁ own with lead (inW (Placing.Own.world own)) le
  ...   | l-hot hh r = dj N hh (InvAt.world (io N) oy) (⊑-inside r)
  ...   | l-in v     = InvAt.under (io N) x oy plain-ix (inW v) (⊑-refl _)
  gap-lo {N} {q} x bd oy ne le | inj₁ own | l-root r with ⊑-snoc q r
  ...   | inj₂ refl = InvAt.flat (io N) x oy
  ...   | inj₁ yq with row-lead oy x yq
  ...     | refl = ne (InvAt.func (io N) oy x)

  -- Nor any value's marker.
  gap-lv : ∀ {N q a b g y a′} → o N q (out a) → BdL a (q ⊕ [ ix 1 ]) N b g → o N y (out a′) → ¬ (y ⊕ [ ix 0 ]) ⊑ b
  gap-lv {N} x bd oy le with pl x bd
  ... | inj₂ env = el env (inW (step (inW (InvAt.world (io N) oy)) plain-ix)) le
  ... | inj₁ own with lead (inW (Placing.Own.world own)) le
  ...   | l-hot hh r = dj N hh (step (inW (InvAt.world (io N) oy)) plain-ix) (⊑-inside r)
  gap-lv {N} {q} {y = y} x bd oy le | inj₁ own | l-in v with w-up plain-ix (inW v)
  ...   | inj₂ v′ = InvAt.under (io N) x oy plain-ix v′ (⊑-refl y)
  ...   | inj₁ eq with ⊕-injʳ q y eq
  ...     | ()
  gap-lv {N} {q} {y = y} x bd oy le | inj₁ own | l-root r with ⊑-snoc q r
  ...   | inj₂ eq with ⊕-injʳ y q eq
  ...     | ()
  gap-lv {N} {q} {y = y} x bd oy le | inj₁ own | l-root r | inj₁ r′ with row-lead oy x (⊑-trans (⊑-snoc⁺ y) r′)
  ...     | refl = not-up {H = H N} (InvAt.real (io N) x) here r′

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

  -- A merge row is a valueless outer row, a value's marker, or a lane's
  -- row: what leads none of them leads no merge row.  A value's own row
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
