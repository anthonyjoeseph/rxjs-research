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

open import Data.Empty using (⊥)
open import Data.List using ([]; [_])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.EmissionSet using (out; pin; EmissionSet; _≺_; _≼_; At; Ended; module Joining)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≺-ext; ≺→≼; ≺-≼-≺; ≼-refl; ≼-trans)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.Horizon using (Tag; free; held; module Cuts)

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

module MergeB {A B : Set} (o : ℕ → EmissionSet A) (Bdo : ℕ → Pos → Tag → Set) (Bo : Cuts.Bounded o Bdo)
  (L : A → Pos → ℕ → EmissionSet B) (BdL : A → Pos → ℕ → Pos → Tag → Set)
  (BL : ∀ {N q a} → o N q (out a) → Cuts.Bounded (L a (q ⊕ [ ix 1 ])) (BdL a (q ⊕ [ ix 1 ])))
  (pin-after : ∀ {N M q a y r} → o N q (out a) → L a (q ⊕ [ ix 1 ]) M y (pin r) → (q ⊕ [ ix 1 ]) ≼ r)
  where

  open MergeJ o L public

  MBd : ℕ → Pos → Tag → Set
  MBd N = JoinBd.JBd (o N) (λ _ → ⊤) (λ _ _ → ⊥) (Bdo N) (λ q a → BdL a (q ⊕ [ ix 1 ]) N)

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

  postulate
    -- No merge row leads a boundary of the merge.
    gap-m : ∀ {N b g y e} → MBd N b g → Jc N y e → ¬ y ⊑ b

  bounded : SM.Bounded
  bounded = record { gap = gap-m ; held-in = λ {N} {b} {r} → held-in {N} {b} {r} ; held-under = λ {N} {b} {r} → held-under {N} {b} {r} ; fwd = fwd ; fwd-pin = λ {N} {r} {k} → fwd-pin {N} {r} {k} }
