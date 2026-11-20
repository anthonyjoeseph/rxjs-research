{-# OPTIONS --guardedness #-}

-- WHERE A BOUNDED MERGE HANGS: its outer's boundaries, and each lane's at
-- the subscription the schedule gives it (`CcJ.LBd`).  Every value runs
-- and no lane is cut, but a queued lane subscribes under the end that
-- frees it, so lanes' worlds nest.
--
-- ITS CUTS ARE BOUNDED (`CcB.bounded`).  Every lane before a boundary is
-- clear there, so the lanes agree where they are subscribed, and the
-- schedule, read off ends before each subscription, agrees with them
-- (`denotation.Laws.Join`).  A lane's boundary is led by no join row:
-- its own lane's by its own gap, another's apart from it under distinct
-- values' second children, or nested under an end, which the earlier
-- lane's rows keep clear of (`denotation.Laws.BoundedInv`).  A lane's
-- pin settles by the lane's own pins, its subscription before the
-- connect.
module simultaneous.HorizonCc where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (<-cmp)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([_])
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; _⊕_; inside)
open import denotation.EmissionSet using (out; pin; EmissionSet; _≺_; _≼_; Reach; Truncate; module Bounded; module Joining)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Worlds using (_⊑_; Ok; InvAt; InvD; Plain; W⁼; step; inW; here; plain-ix; nest; nest⁼; ⊕-injˡ; ⊕-injʳ)
open import denotation.Laws.Cut using (inv-sub)
open import denotation.Laws.JoinInv using (ix01)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
import denotation.Laws.Join as LJ
open import simultaneous.Horizon using (Tag; free; held; module Cuts; under-child)
open import simultaneous.HorizonJoin using (module CcJ; module JoinBd; module JoinRows)
open import simultaneous.Placed using (module Placing)

module CcB {A B : Set} (m : ℕ) (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set) (Bo : Cuts.Bounded o Bdo)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  -- the subscriptions a lane is admissible at
  (Adm : Pos → Set)
  (BL : ∀ {a s} → Adm s → Cuts.Bounded (L a s) (BdL a s))
  (reach : ∀ {N a s y e} → L a s N y e → Reach (L a s N) y e)
  (pin-after : ∀ {N a s y r} → L a s N y (pin r) → s ≼ r)
  (pin-in : ∀ {N a s y r} → L a s N y (pin r) → T (inside r y))
  -- each cut under hot rows `H`, its scope's boundaries `Env`
  (H : ℕ → Pos → Set) (Env : ℕ → Pos → Tag → Set) (p : Pos)
  (ok : ∀ N → Ok (H N) p) (io : ∀ N → InvAt (H N) p (o N))
  (li : ∀ N a s → Ok (H N) s → InvAt (H N) s (L a s N))
  (adm-row : ∀ {N q a} → o N q (out a) → Adm (q ⊕ [ ix 1 ]))
  (adm-end : ∀ {N a s c e} → Adm s → L a s N c e → Adm (c ⊕ [ ix 1 ]))
  (po : Placing.Placed H Env p o Bdo)
  (pl : ∀ {a s} → Adm s → Placing.Placed H Env s (L a s) (BdL a s))
  (el : ∀ {N b g} → Env N b g → ∀ {w} → W⁼ (H N) p w → ¬ w ⊑ b)
  where

  open CcJ m o L public
  open JoinBd using (outerB; laneB; laneH)
  open JoinRows o H p io (λ N → proj₂ (ok N)) using (off-lane; root-lo; root-lv)

  MBd : ℕ → Pos → Tag → Set
  MBd N = JoinBd.JBd (o N) (BN.Indexed N) (λ _ _ → ⊥) (Bdo N) (LBd BdL N)

  module SM = Cuts Jc MBd
  module BO = Cuts.Bounded Bo

  fi : ∀ N a → InvD (H N) (fD N a)
  fi N a s oks = inv-sub proj₁ (li N a s oks)

  -- One cut's lanes.
  module At (N : ℕ) where
    open Bounded m (fD N) (o N)
    open BoundedI (ok N) m (fD N) (fi N) (io N)
    open Nths (o N) using (nth-val)

    -- A scheduled lane is admissible: at its value's second child, or
    -- at the second child of an end of an earlier one.
    adm′ : ∀ i → Acc _<_ i → ∀ {q s a} → Sub i q s a → Adm s
    adm′ i _ (nq , room _)    = adm-row (nth-val nq)
    adm′ i _ (nq , freed _ _) = adm-row (nth-val nq)
    adm′ i (acc rs) (nq , queued _ _ kc _ _) with kth-lane i kc
    ... | ending j<i (_ , _ , _ , nj , stj , ac) refl = adm-end (adm′ _ (rs j<i) (nj , stj)) (proj₁ (proj₁ ac))

    adm : ∀ {i q s a} → Sub i q s a → Adm s
    adm {i} sb = adm′ i (<-wellFounded i) sb

    -- In the world of a value's second child.
    root : ∀ {i q s a} → Sub i q s a → Σ Pos λ r → Σ A λ b → o N r (out b) × W⁼ (H N) (r ⊕ [ ix 1 ]) s
    root sb with seat* sb
    ... | seat′ _ _ _ nr rw = _ , _ , nth-val nr , rw

    -- A lane's boundary, as the join's.
    lane-mbd : ∀ {i q s a b} g → Sub i q s a → BdL a s N b g → MBd N b g
    lane-mbd free     sb bd = laneB (nth-val (proj₁ sb)) (_ , _ , proj₁ sb) (_ , _ , sb , bd) (λ ())
    lane-mbd (held r) sb bd = laneH (nth-val (proj₁ sb)) (_ , _ , proj₁ sb) (_ , _ , sb , bd) (λ ())

    -- A join row is a valueless outer row, a value's marker, or a row a
    -- lane shows: its own, or its queued end's first child.
    data Row (y : Pos) : Set where
      on   : ∀ {e} → o N y e → (∀ {a} → ¬ e ≡ out a) → Row y
      mark : ∀ {q a} → o N q (out a) → y ≡ q ⊕ [ ix 0 ] → Row y
      inl  : ∀ {i q s a} → Sub i q s a → Lr a s y → Row y

    row : ∀ {y e} → Jc N y e → Row y
    row (Joining.val x)                              = mark x refl
    row (Joining.step x)                             = on x (λ ())
    row (Joining.opin x)                             = on x (λ ())
    row (Joining.oend x _)                           = on x (λ ())
    row (Joining.opass x _)                          = on x (λ ())
    row (Joining.lane _ _ (_ , _ , sb , l) _ w)      = inl sb (lr sb (l-work l w))
    row (Joining.lend _ _ (_ , _ , sb , l) _ nQ d)   = inl sb (lr sb (l-end l nQ d))
    row (Joining.lpass _ _ (_ , _ , sb , l) _ nQ nd) = inl sb (lr sb (l-pass l nQ nd))
    row (Joining.hand _ _ (_ , _ , sb , l) _ Q)      = inl sb (lr-hand l Q refl)
    row (Joining.left _ _ (_ , _ , sb , l) _ _)      = inl sb (lr sb (l-work l tt))
    row (Joining.run () _)
    row (Joining.rend () _ _)
    row (Joining.rpass () _ _)
    row (Joining.rhand () _)

    ------------------------------------------------------------------------
    -- Gaps

    -- AN OUTER BOUNDARY: the outer's own lies under no world of its
    -- rows' children, so of no lane, its scope's under no world position.
    outer-gap : ∀ {b g y} → Bdo N b g → Row y → ¬ y ⊑ b
    outer-gap bd (on x _)      = BO.gap bd x
    outer-gap bd (mark x refl) = under-child (ix 0) (BO.gap bd x)
    outer-gap bd (inl sb l) with po bd
    ... | inj₁ own = let (_ , _ , xr , rw) = root sb in Placing.Own.under own xr plain-ix (inW (nest rw (lr-w sb l)))
    ... | inj₂ env = el env (inW (nest (inW (s-w sb)) (lr-w sb l)))

    -- One lane's own row, or its queued end's first child, under its own
    -- boundary: by its own gap, or under its end.
    same-gap : ∀ {i q s a b g y} → Sub i q s a → BdL a s N b g → Placing.Own H Env s (L a s) N b g → Lr a s y → ¬ y ⊑ b
    same-gap sb bd own (lr-row ly _)      = Cuts.Bounded.gap (BL (adm sb)) bd (proj₁ (proj₁ ly))
    same-gap sb bd own (lr-hand ac _ refl) = Placing.Own.under own (proj₁ (proj₁ ac)) plain-ix here

    -- ANOTHER LANE'S ROW: under distinct values' second children, apart;
    -- or the later nested under an end of the earlier, which the earlier
    -- lane's rows keep clear of.
    lane-gap : ∀ {i q s a b g i′ q′ s′ a′ y} → Sub i q s a → BdL a s N b g → Placing.Own H Env s (L a s) N b g
             → Sub i′ q′ s′ a′ → Lr a′ s′ y → ¬ y ⊑ b
    lane-gap {i} {i′ = i′} sb bd own sb′ l′ with <-cmp i i′
    ... | tri≈ _ refl _ with sub-fun sb sb′
    ...   | refl , refl , refl = same-gap sb bd own l′
    lane-gap {i} {i′ = i′} sb bd own sb′ l′ | tri< lt _ _ with rel lt sb sb′
    ...   | apart xr xr′ ne rw rw′ = apart-lead xr′ xr (λ eq → ne (sym eq)) (inW (nest rw′ (lr-w sb′ l′))) (nest rw (Placing.Own.world own))
    ...   | queued-in ac _ v        = Placing.Own.under own (proj₁ (proj₁ ac)) plain-ix (inW (nest v (lr-w sb′ l′)))
    lane-gap {i} {i′ = i′} sb bd own sb′ l′ | tri> _ _ gt with rel gt sb′ sb
    ...   | apart xr′ xr ne rw′ rw = apart-lead xr′ xr ne (inW (nest rw′ (lr-w sb′ l′))) (nest rw (Placing.Own.world own))
    ...   | queued-in ac′ Q v      = nest-lead sb′ ac′ Q l′ (nest v (Placing.Own.world own))

    -- A LANE'S OWN BOUNDARY, in its value's root's world: no outer row's,
    -- and no lane's.
    lane-row : ∀ {i q s a b g r b′ y} → Sub i q s a → BdL a s N b g → Placing.Own H Env s (L a s) N b g
             → o N r (out b′) → W⁼ (H N) (r ⊕ [ ix 1 ]) s → Row y → ¬ y ⊑ b
    lane-row sb bd own xr rw (on oy ne)     = root-lo xr (nest rw (Placing.Own.world own)) oy ne
    lane-row sb bd own xr rw (mark oy refl) = root-lv xr (nest rw (Placing.Own.world own)) oy
    lane-row sb bd own xr rw (inl sb′ l′)   = lane-gap sb bd own sb′ l′

    lane-gap′ : ∀ {i q s a b g y e} → Sub i q s a → BdL a s N b g → Jc N y e → ¬ y ⊑ b
    lane-gap′ sb bd j with pl (adm sb) bd
    ... | inj₁ own = let (_ , _ , xr , rw) = root sb in lane-row sb bd own xr rw (row j)
    ... | inj₂ env = el env (inW (world-v (vw j)))

    gap-m : ∀ {b g y e} → MBd N b g → Jc N y e → ¬ y ⊑ b
    gap-m (outerB bd)                   j = outer-gap bd (row j)
    gap-m (laneB _ _ (_ , _ , sb , bd) _) j = lane-gap′ sb bd j
    gap-m (laneH _ _ (_ , _ , sb , bd) _) j = lane-gap′ sb bd j

    ------------------------------------------------------------------------
    -- Placement

    -- What a plain child of a join row reaches, against an outer row's.
    outer-under : ∀ {b g x l w} → Placing.Own H Env p o N b g → Row x → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
    outer-under own (on x _)      pl v = Placing.Own.under own x pl v
    outer-under own (mark x refl) pl v = Placing.Own.under own x plain-ix (nest⁼ (inW (step here pl)) v)
    outer-under own (inl sb l)    pl v = let (_ , _ , xr , rw) = root sb in Placing.Own.under own xr plain-ix (child-in rw sb l pl v)

    -- Against a lane's own boundary: its own lane's by its own, the
    -- outer's off its root's world, another lane's apart or nested.
    own-under : ∀ {i q s a b g x l w} → Sub i q s a → Placing.Own H Env s (L a s) N b g → Lr a s x → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
    own-under sb own (lr-row lx _)      pl v = Placing.Own.under own (proj₁ (proj₁ lx)) pl v
    own-under sb own (lr-hand ac _ refl) pl v = Placing.Own.under own (proj₁ (proj₁ ac)) plain-ix (nest⁼ (inW (step here pl)) v)

    lanes-under : ∀ {i q s a b g i′ q′ s′ a′ x l w} → Sub i q s a → Placing.Own H Env s (L a s) N b g
                → Sub i′ q′ s′ a′ → Lr a′ s′ x → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
    lanes-under {i} {i′ = i′} sb own sb′ l′ pl v with <-cmp i i′
    ... | tri≈ _ refl _ with sub-fun sb sb′
    ...   | refl , refl , refl = own-under sb own l′ pl v
    lanes-under {i} {i′ = i′} sb own sb′ l′ pl v | tri< lt _ _ with rel lt sb sb′
    ...   | apart xr xr′ ne rw rw′ = apart-lead xr′ xr (λ eq → ne (sym eq)) (child-in rw′ sb′ l′ pl v) (nest rw (Placing.Own.world own))
    ...   | queued-in ac _ v₁       = Placing.Own.under own (proj₁ (proj₁ ac)) plain-ix (child-in v₁ sb′ l′ pl v)
    lanes-under {i} {i′ = i′} sb own sb′ l′ pl v | tri> _ _ gt with rel gt sb′ sb
    ...   | apart xr′ xr ne rw′ rw = apart-lead xr′ xr ne (child-in rw′ sb′ l′ pl v) (nest rw (Placing.Own.world own))
    ...   | queued-in ac′ Q v₁     = nest-under sb′ ac′ Q l′ pl v (nest v₁ (Placing.Own.world own))

    lane-under : ∀ {i q s a b g r b′ x l w} → Sub i q s a → Placing.Own H Env s (L a s) N b g
               → o N r (out b′) → W⁼ (H N) (r ⊕ [ ix 1 ]) s → Row x → Plain l → W⁼ (H N) (x ⊕ [ l ]) w → ¬ w ⊑ b
    lane-under {r = r} {x = x} sb own xr rw (on oy ne) pl v = off-lane xr oy pl v ne′ (inW (nest rw (Placing.Own.world own)))
      where
        ne′ : ∀ {l} → ¬ (x ⊕ [ l ] ≡ r ⊕ [ ix 1 ])
        ne′ eq with ⊕-injˡ x r eq
        ... | refl = ne (InvAt.func (io N) oy xr)
    lane-under {r = r} sb own xr rw (mark {q} oy refl) pl v =
      off-lane xr oy plain-ix (nest⁼ (inW (step here pl)) v) (λ eq → ix01 (⊕-injʳ q r eq)) (inW (nest rw (Placing.Own.world own)))
    lane-under sb own xr rw (inl sb′ l′) pl v = lanes-under sb own sb′ l′ pl v

    outer-own : ∀ {b g} → Placing.Own H Env p o N b g → Placing.Own H Env p Jc N b g
    outer-own own = record
      { world = Placing.Own.world own ; real = Placing.Own.real own ; holder = Placing.Own.holder own
      ; under = λ j pl v → outer-under own (row j) pl v }

    lane-own : ∀ {i q s a b g} → Sub i q s a → Placing.Own H Env s (L a s) N b g → Placing.Own H Env p Jc N b g
    lane-own sb own = record
      { world  = nest (inW (s-w sb)) (Placing.Own.world own)
      ; real   = Placing.Own.real own
      ; holder = λ eq → nest⁼ (inW (s-w sb)) (proj₁ (Placing.Own.holder own eq)) , proj₂ (Placing.Own.holder own eq)
      ; under  = λ j pl v → let (_ , _ , xr , rw) = root sb in lane-under sb own xr rw (row j) pl v }

    placed-at : ∀ {b g} → MBd N b g → Placing.Own H Env p Jc N b g ⊎ Env N b g
    placed-at (outerB bd) with po bd
    ... | inj₁ own = inj₁ (outer-own own)
    ... | inj₂ env = inj₂ env
    placed-at (laneB _ _ (_ , _ , sb , bd) _) with pl (adm sb) bd
    ... | inj₁ own = inj₁ (lane-own sb own)
    ... | inj₂ env = inj₂ env
    placed-at (laneH _ _ (_ , _ , sb , bd) _) with pl (adm sb) bd
    ... | inj₁ own = inj₁ (lane-own sb own)
    ... | inj₂ env = inj₂ env

  -- A BOUNDED MERGE'S BOUNDARIES ARE PLACED.
  placed : Placing.Placed H Env p Jc MBd
  placed {N} = At.placed-at N

  ------------------------------------------------------------------------
  -- Cuts

  held-in : ∀ {N b r} → MBd N b (held r) → r ≺ b
  held-in (outerB bd)                         = BO.held-in bd
  held-in {N} (laneH _ _ (_ , _ , sb , bd) _) = Cuts.Bounded.held-in (BL (At.adm N sb)) bd

  held-under : ∀ {N b r} → MBd N b (held r) → r ⊑ b
  held-under (outerB bd)                         = BO.held-under bd
  held-under {N} (laneH _ _ (_ , _ , sb , bd) _) = Cuts.Bounded.held-under (BL (At.adm N sb)) bd

  -- A lane read off a cut agreeing with another holds the other's rows.
  trunc-ag : ∀ {N N′ a s k} → AgreeTo k (L a s N) (L a s N′) → AgreeTo k (Truncate (L a s N)) (Truncate (L a s N′))
  trunc-ag ag = ⟨ (λ yk → (λ t → let x = proj₁ (upto ag yk) (proj₁ t) in x , reach x)
                        , (λ t → let x = proj₂ (upto ag yk) (proj₁ t) in x , reach x)) ⟩

  -- Clear to `k`, every lane subscribed there settles there.
  lanes-ag : ∀ {N N′ k} → SM.Clear N k → N ≤ N′ → LJ.Join.BoundedJ.Lanes {A} {B} k m (o N) (fD N) (fD N′)
  lanes-ag {N} {N′} {k} cl le =
    LJ.Join.BoundedJ.lanes (λ {i} {q} {s} {a} sb _ → trunc-ag {N} {N′} {a} {s} {k}
      (Cuts.Bounded.fwd (BL (At.adm N sb)) (λ {b} {g} bd → cl (At.lane-mbd N g sb bd)) le))

  -- CLEAR, SO SETTLED: the outer by its own, every lane by its own, and
  -- the schedule read off them.
  fwd : ∀ {N k} → SM.Clear N k → SM.Settled N k
  fwd {N} {k} cl {N′} le = LJ.Join.BoundedJ.agree {A} {B} k m (BO.fwd (λ bd → cl (outerB bd)) le) (lanes-ag {N} {N′} {k} cl le)

  -- PINS OF `r` SETTLE: the outer's by its own; a lane's by its own, its
  -- subscription at or before `r`, where the schedule agrees.
  fwd-pin : ∀ {N r k} → SM.Clear N r → SM.HeldClear N r k → SM.PinSettled N r k
  fwd-pin {N} {r} {k} cr hr {N′} le {y} yk = to , from
    where
      module BJ = LJ.Join.BoundedJ {A} {B} r m

      ago : AgreeTo r (o N) (o N′)
      ago = BO.fwd (λ bd → cr (outerB bd)) le

      lns = lanes-ag {N} {N′} {r} cr le

      opa = BO.fwd-pin {N} {r} {k} (λ bd → cr (outerB bd)) (λ bd → hr (outerB bd)) le {y} yk

      lpa : ∀ {i q s a} → Bounded.Sub m (fD N) (o N) i q s a → (L a s N y (pin r) → L a s N′ y (pin r)) × (L a s N′ y (pin r) → L a s N y (pin r))
      lpa sb = Cuts.Bounded.fwd-pin (BL (At.adm N sb)) {N} {r} {k} (λ {b} {g} bd → cr (At.lane-mbd N g sb bd)) (λ {b} bd → hr (At.lane-mbd N (held r) sb bd)) le {y} yk

      qr : ∀ {M i q s a} → Bounded.Sub m (fD M) (o M) i q s a → s ≼ r → q ≼ r
      qr {q = q} {s} sb sr = ≺→≼ {q} {r} (≺-≼-≺ {q} {s} {r} (BJ.starts-past (proj₂ sb)) sr)

      left→ : ∀ {q a} → o N q (out a) → Bounded.Lane m (fD N) (o N) q a y (pin r) → Jc N′ y (pin r)
      left→ x (i , s , sb , ((ly , _) , sy)) =
        Joining.left (proj₁ (upto ago (qr sb sr)) x) (i , _ , proj₁ sb′) (i , s , sb′ , ((ly′ , reach ly′) , sy)) (λ ()) (pin-in ly)
        where
          sr  = pin-after ly
          sb′ = BJ.sub-to ago lns (BJ.stem-≼ s sr) sb
          ly′ = proj₁ (lpa sb) ly

      left← : ∀ {q a} → o N′ q (out a) → Bounded.Lane m (fD N′) (o N′) q a y (pin r) → Jc N y (pin r)
      left← x′ (i , s , sb′ , ((ly′ , _) , sy)) =
        Joining.left (proj₂ (upto ago (qr sb′ sr)) x′) (i , _ , proj₁ sb) (i , s , sb , ((ly , reach ly) , sy)) (λ ()) (pin-in ly′)
        where
          sr = pin-after ly′
          sb = BJ.sub-from ago lns (BJ.stem-≼ s sr) sb′
          ly = proj₂ (lpa sb) ly′

      to : Jc N y (pin r) → Jc N′ y (pin r)
      to (Joining.opin x)         = Joining.opin (proj₁ opa x)
      to (Joining.lane x _ l _ _) = left→ x l
      to (Joining.left x _ l _ _) = left→ x l
      to (Joining.run () _)

      from : Jc N′ y (pin r) → Jc N y (pin r)
      from (Joining.opin x)         = Joining.opin (proj₂ opa x)
      from (Joining.lane x _ l _ _) = left← x l
      from (Joining.left x _ l _ _) = left← x l
      from (Joining.run () _)

  bounded : SM.Bounded
  bounded = record
    { gap = λ {N} → At.gap-m N
    ; held-in = λ {N} {b} {r} → held-in {N} {b} {r}
    ; held-under = λ {N} {b} {r} → held-under {N} {b} {r}
    ; fwd = λ {N} {k} → fwd {N} {k}
    ; fwd-pin = λ {N} {r} {k} → fwd-pin {N} {r} {k} }
