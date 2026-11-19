{-# OPTIONS --guardedness #-}

-- A JOIN OVER CORRESPONDING PARTS CORRESPONDS: flatMap's merge, switch and
-- exhaust, a lane per outer value, none begun and none handed off.
--
-- A JOIN'S BOUNDARIES: its outer's, always; and each running lane's, kept
-- while the lane is not cut before it, a held one while the lane is not
-- cut before the connect it waits on, as a join keeps that lane's pins
-- (`JoinPair.JBd`).
--
-- A join's own rows are its outer's at their places, its lanes' at
-- theirs, and each value's marker at its first child.  So a join row
-- orders against a pair as its part's row (`JoinPair.lift`).  A boundary
-- has its part's partner: the outer's, or the lane of the value's image,
-- whose cut the policy decides alike from rows cut alike (`cut→`, `cut←`).
--
-- WHAT THE PARTS OWE, as parameters: their correspondences, a lane's for
-- each value and its image; the facts about two parts at once, that one
-- part's rows cut the other's marks alike (`outer-lane`, `lane-outer`,
-- `lane-lane`); values and their running correspond; and the gaps every
-- former's boundaries keep from its rows.
module simultaneous.HorizonJoin where

open import Data.Empty using (⊥)
open import Data.List using ([_])
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)

open import denotation.Position using (Pos; ix; _⊕_; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; out; end; skip; EmissionSet; _≺_; module Joining)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.Horizon using (Tag; free; held)
open import simultaneous.HorizonCorr using (Btw; PB; Own; OwnPut; _∪_; _∪²_; module Inter; first-child)
open import simultaneous.HorizonConn using (Mark; mark; mark-q; retarget)

module JoinPair {A B X Y : Set}
  (Lane : Pos → A → EmissionSet B) (o : EmissionSet A) (Over Runs : Pos → Set) (Cut : Pos → Pos → Set)
  (Lane* : Pos → X → EmissionSet Y) (o* : EmissionSet X) (Over* Runs* : Pos → Set) (Cut* : Pos → Pos → Set)
  (Bdo : Pos → Tag → Set) (BdL : Pos → A → Pos → Tag → Set)
  (Bdo* : Pos → Tag → Set) (BdL* : Pos → X → Pos → Tag → Set)
  -- the environment, and each part's map, late rows and placements
  (Env : Pos → Set) (EnvPut : Pos → Pos → Set)
  (φo φj : Pos → Pos) (φL : Pos → A → Pos → Pos)
  (Lo Lj : Pos → Set) (Ll : Pos → A → Pos → Set)
  (Po Pj : Pos → Pos → Set) (PL : Pos → A → Pos → Pos → Set)
  where
  module J  = Joining Lane o (λ _ _ → ⊥) Over Runs Cut (λ _ → ⊥)
  module J* = Joining Lane* o* (λ _ _ → ⊥) Over* Runs* Cut* (λ _ → ⊥)

  -- A join keeps its outer's boundaries, and a running lane's before its cut.
  data JBd : Pos → Tag → Set where
    outerB : ∀ {b g} → Bdo b g → JBd b g
    laneB  : ∀ {q a b} → o q (out a) → Runs q → BdL q a b free → ¬ Cut q b → JBd b free
    laneH  : ∀ {q a b r} → o q (out a) → Runs q → BdL q a b (held r) → ¬ Cut q r → JBd b (held r)

  data JBd* : Pos → Tag → Set where
    outerB : ∀ {b g} → Bdo* b g → JBd* b g
    laneB  : ∀ {q a b} → o* q (out a) → Runs* q → BdL* q a b free → ¬ Cut* q b → JBd* b free
    laneH  : ∀ {q a b r} → o* q (out a) → Runs* q → BdL* q a b (held r) → ¬ Cut* q r → JBd* b (held r)

  ORow : Pos → Set
  ORow = Own o Lo ∪ Env

  OPut : Pos → Pos → Set
  OPut = OwnPut o Po ∪² EnvPut

  LRow : Pos → A → Pos → Set
  LRow q a = Own (Lane q a) (Ll q a) ∪ Env

  LPut : Pos → A → Pos → Pos → Set
  LPut q a = OwnPut (Lane q a) (PL q a) ∪² EnvPut

  JRow : Pos → Set
  JRow = Own J.JoinT Lj ∪ Env

  JPut : Pos → Pos → Set
  JPut = OwnPut J.JoinT Pj ∪² EnvPut

  module IO = Inter ORow φo OPut Bdo Bdo*
  module IL (q : Pos) (a : A) (q* : Pos) (a* : X) = Inter (LRow q a) (φL q a) (LPut q a) (BdL q a) (BdL* q* a*)
  module IJ = Inter JRow φj JPut JBd JBd*

  -- Every lane's rows, cut alike.
  Lanes : Pos → Pos → Set
  Lanes z z* = ∀ {q a} → o q (out a) → Btw (Own (Lane q a) (Ll q a)) (φL q a) z z*

  LanesP : Pos → Pos → Set
  LanesP z z* = ∀ {q a} → o q (out a) → PB (OwnPut (Lane q a) (PL q a)) z z*

  module Pair
    (Co : IO.BCorr)
    -- a value's image is a value, running alike, and their lanes correspond
    (val→ : ∀ {q a} → o q (out a) → Σ X λ a* → o* (φo q) (out a*))
    (val← : ∀ {q* a*} → o* q* (out a*) → Σ Pos λ q → Σ A λ a → o q (out a) × q* ≡ φo q)
    (runs→ : ∀ {q a} → o q (out a) → Runs q → Runs* (φo q))
    (runs← : ∀ {q a} → o q (out a) → Runs* (φo q) → Runs q)
    (o-func : ∀ {q a a′} → o q (out a) → o q (out a′) → a ≡ a′)
    (CL : ∀ {q a a*} → o q (out a) → o* (φo q) (out a*) → IL.BCorr q a (φo q) a*)
    -- one map: the join reads each part's rows and the environment as they do
    (φj-outer : ∀ {k e} → o k e → φj k ≡ φo k)
    (φj-val : ∀ {q a} → o q (out a) → φj (q ⊕ [ ix 0 ]) ≡ φo q ⊕ [ ix 0 ])
    (φj-lane : ∀ {q a k e} → o q (out a) → Lane q a k e → φj k ≡ φL q a k)
    (φj-env : ∀ {k} → Env k → φj k ≡ φo k)
    (φL-env : ∀ {q a k} → Env k → φL q a k ≡ φo k)
    (nl-out : ∀ {q a} → o q (out a) → ¬ Lo q)
    (late-outer : ∀ {k} → Lo k → Lj k)
    (late-lane : ∀ {q a k e} → o q (out a) → Lane q a k e → Ll q a k → Lj k)
    (put-split : ∀ {k e l} → J.JoinT k e → Pj k l
               → (Σ (Ev A) λ e′ → o k e′ × Po k l) ⊎ (Σ Pos λ q → Σ A λ a → Σ (Ev B) λ e′ → o q (out a) × Lane q a k e′ × PL q a k l))
    (img : ∀ {k} → Own J.JoinT Lj k → Σ (Ev Y) (J*.JoinT (φj k)))
    -- no join row lies over a part's boundary, or a connect one waits on
    (gap-o  : ∀ {b g y e} → Bdo b g → J.JoinT y e → ¬ y ⊑ b)
    (gap-o* : ∀ {b g y e} → Bdo* b g → J*.JoinT y e → ¬ y ⊑ b)
    (held-o  : ∀ {b q y e} → Bdo b (held q) → J.JoinT y e → ¬ y ⊑ q)
    (held-o* : ∀ {b q y e} → Bdo* b (held q) → J*.JoinT y e → ¬ y ⊑ q)
    (gap-l  : ∀ {q a b g y e} → BdL q a b g → J.JoinT y e → ¬ y ⊑ b)
    (gap-l* : ∀ {q a b g y e} → BdL* q a b g → J*.JoinT y e → ¬ y ⊑ b)
    (held-l  : ∀ {q a b r y e} → BdL q a b (held r) → J.JoinT y e → ¬ y ⊑ r)
    (held-l* : ∀ {q a b r y e} → BdL* q a b (held r) → J*.JoinT y e → ¬ y ⊑ r)
    (held-in-l  : ∀ {q a b r} → BdL q a b (held r) → r ≺ b)
    (held-in-l* : ∀ {q a b r} → BdL* q a b (held r) → r ≺ b)
    -- a lane is cut alike, and stays cut
    (cut→ : ∀ {q a z z*} → o q (out a) → IJ.Between z z* → ¬ Cut q z → ¬ Cut* (φo q) z*)
    (cut← : ∀ {q a z z*} → o q (out a) → IJ.Between z z* → ¬ Cut* (φo q) z* → ¬ Cut q z)
    (cut-up  : ∀ {q k k′} → Cut q k → k ≺ k′ → Cut q k′)
    (cut-up* : ∀ {q k k′} → Cut* q k → k ≺ k′ → Cut* q k′)
    -- each part's rows cut the other parts' marks alike
    (outer-lane : ∀ {z z*} → Mark Bdo z → Mark Bdo* z* → IO.Between z z* → Lanes z z*)
    (outer-lane-put : ∀ {z z*} → Mark Bdo z → Mark Bdo* z* → IO.PutBefore z z* → LanesP z z*)
    (lane-outer : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
                → IL.Between q a (φo q) a* z z* → Btw (Own o Lo) φo z z*)
    (lane-outer-put : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
                    → IL.PutBefore q a (φo q) a* z z* → PB (OwnPut o Po) z z*)
    (lane-lane : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
               → IL.Between q a (φo q) a* z z* → ∀ {q′ a′} → o q′ (out a′) → ¬ q′ ≡ q → Btw (Own (Lane q′ a′) (Ll q′ a′)) (φL q′ a′) z z*)
    (lane-lane-put : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
                   → IL.PutBefore q a (φo q) a* z z* → ∀ {q′ a′} → o q′ (out a′) → ¬ q′ ≡ q → PB (OwnPut (Lane q′ a′) (PL q′ a′)) z z*)
    where
    open Inter.BCorr Co renaming (to to toO; from to fromO)

    -- A JOIN ROW ORDERS AS ITS PART'S ROW.
    lift : ∀ {z z*} → IO.Between z z* → Lanes z z*
         → (∀ {y e} → J.JoinT y e → ¬ y ⊑ z) → (∀ {y e} → J*.JoinT y e → ¬ y ⊑ z*) → IJ.Between z z*
    lift {z} {z*} bo bl ng ng* {k} (inj₂ en) = retarget {k} {z} {z*} (φj-env en) (bo (inj₂ en))
    lift {z} {z*} bo bl ng ng* (inj₁ (_ , y@(Joining.val {q} {a} x) , un , nl)) =
      retarget {q ⊕ [ ix 0 ]} {z} {z*} (φj-val x)
        (first-child {q} {φo q} {z} {z*} (bo (inj₁ (out a , x , _ , nl-out x))) (ng y)
          (subst (λ w → ¬ w ⊑ z*) (φj-val x) (ng* (proj₂ (img (_ , y , un , nl))))))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (_ , Joining.step x , _ , nl)) =
      retarget {k} {z} {z*} (φj-outer x) (bo (inj₁ (skip , x , _ , λ l → nl (late-outer l))))
    lift bo bl ng ng* (inj₁ (_ , Joining.opin _ , () , _))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (_ , Joining.oend x _ , _ , nl)) =
      retarget {k} {z} {z*} (φj-outer x) (bo (inj₁ (end , x , _ , λ l → nl (late-outer l))))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (_ , Joining.opass x _ , _ , nl)) =
      retarget {k} {z} {z*} (φj-outer x) (bo (inj₁ (end , x , _ , λ l → nl (late-outer l))))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (e , Joining.lane x _ y _ _ , un , nl)) =
      retarget {k} {z} {z*} (φj-lane x y) (bl x (e , y , un , λ l → nl (late-lane x y l)))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (_ , Joining.lend x _ y _ _ _ , _ , nl)) =
      retarget {k} {z} {z*} (φj-lane x y) (bl x (end , y , _ , λ l → nl (late-lane x y l)))
    lift {z} {z*} bo bl ng ng* {k} (inj₁ (_ , Joining.lpass x _ y _ _ _ , _ , nl)) =
      retarget {k} {z} {z*} (φj-lane x y) (bl x (end , y , _ , λ l → nl (late-lane x y l)))
    lift bo bl ng ng* (inj₁ (_ , Joining.hand _ _ _ _ () , _ , _))
    lift bo bl ng ng* (inj₁ (_ , Joining.left _ _ _ _ _ , () , _))
    lift bo bl ng ng* (inj₁ (_ , Joining.run () _ , _ , _))
    lift bo bl ng ng* (inj₁ (_ , Joining.rend () _ _ , _ , _))
    lift bo bl ng ng* (inj₁ (_ , Joining.rpass () _ _ , _ , _))
    lift bo bl ng ng* (inj₁ (_ , Joining.rhand () _ , _ , _))

    -- A late join row is its outer's or a lane's, placed as there.
    putJ : ∀ {z z*} → IO.PutBefore z z* → LanesP z z* → IJ.PutBefore z z*
    putJ po pl (inj₂ x) kz = po (inj₂ x) kz
    putJ po pl (inj₁ ((e , y) , p)) kz with put-split y p
    ... | inj₁ (e′ , x , p′) = po (inj₁ ((e′ , x) , p′)) kz
    ... | inj₂ (q , a , e′ , x , y′ , p′) = pl x ((e′ , y′) , p′) kz

    -- At a lane's mark: its own rows, and every other lane's.
    lanes-at : ∀ {q a z z*} → o q (out a) → Btw (Own (Lane q a) (Ll q a)) (φL q a) z z*
             → (∀ {q′ a′} → o q′ (out a′) → ¬ q′ ≡ q → Btw (Own (Lane q′ a′) (Ll q′ a′)) (φL q′ a′) z z*) → Lanes z z*
    lanes-at {q} x own other {q′} x′ with q′ ≟ᵖ q
    ... | no ne = other x′ ne
    ... | yes refl with o-func x′ x
    ...   | refl = own

    lanes-at-put : ∀ {q a z z*} → o q (out a) → PB (OwnPut (Lane q a) (PL q a)) z z*
                 → (∀ {q′ a′} → o q′ (out a′) → ¬ q′ ≡ q → PB (OwnPut (Lane q′ a′) (PL q′ a′)) z z*) → LanesP z z*
    lanes-at-put {q} x own other {q′} x′ with q′ ≟ᵖ q
    ... | no ne = other x′ ne
    ... | yes refl with o-func x′ x
    ...   | refl = own

    liftO : ∀ {z z*} → Mark Bdo z → Mark Bdo* z* → IO.Between z z*
          → (∀ {y e} → J.JoinT y e → ¬ y ⊑ z) → (∀ {y e} → J*.JoinT y e → ¬ y ⊑ z*) → IJ.Between z z*
    liftO m m* btw = lift btw (outer-lane m m* btw)

    liftL : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
          → IL.Between q a (φo q) a* z z*
          → (∀ {y e} → J.JoinT y e → ¬ y ⊑ z) → (∀ {y e} → J*.JoinT y e → ¬ y ⊑ z*) → IJ.Between z z*
    liftL {q} {a} {a*} {z} {z*} x x* m m* btw =
      lift (btw-o) (lanes-at x (λ r → btw (inj₁ r)) (lane-lane x x* m m* btw))
      where
        btw-o : IO.Between z z*
        btw-o (inj₁ r) = lane-outer x x* m m* btw r
        btw-o {k} (inj₂ en) = retarget {k} {z} {z*} (sym (φL-env en)) (btw (inj₂ en))

    putL : ∀ {q a a* z z*} → o q (out a) → o* (φo q) (out a*) → Mark (BdL q a) z → Mark (BdL* (φo q) a*) z*
         → IL.PutBefore q a (φo q) a* z z* → IJ.PutBefore z z*
    putL x x* m m* pb =
      putJ (λ { (inj₁ p) → lane-outer-put x x* m m* pb p ; (inj₂ p) → pb (inj₂ p) })
           (lanes-at-put x (λ p → pb (inj₁ p)) (lane-lane-put x x* m m* pb))

    tagO→ : ∀ {b b* g g*} → Bdo b g → Bdo* b* g* → IO.TagTo g g* → IJ.TagTo g g*
    tagO→ _  _   IO.plain-free      = IJ.plain-free
    tagO→ bd bd* (IO.both-held btw) = IJ.both-held (liftO (mark-q bd) (mark-q bd*) btw (held-o bd) (held-o* bd*))

    tagO← : ∀ {b b* g g*} → Bdo b g → Bdo* b* g* → IO.TagFrom g g* → IJ.TagFrom g g*
    tagO← _  _   IO.elab-free       = IJ.elab-free
    tagO← bd bd* (IO.both-held btw) = IJ.both-held (liftO (mark-q bd) (mark-q bd*) btw (held-o bd) (held-o* bd*))

    to : ∀ {b g} → JBd b g → Σ Pos λ b* → Σ Tag λ g* → JBd* b* g* × IJ.Between b b* × IJ.TagTo g g*
    to (outerB bd) with toO bd
    ... | b* , g* , bd* , btw , tt = b* , g* , outerB bd* , liftO (mark bd) (mark bd*) btw (gap-o bd) (gap-o* bd*) , tagO→ bd bd* tt
    to (laneB {q} {a} {b} x rn bd nc) with val→ x
    ... | a* , x* with Inter.BCorr.to (CL x x*) bd
    ...   | b* , free , bd* , btw , _ =
      b* , free , laneB x* (runs→ x rn) bd* (cut→ x jb nc) , jb , IJ.plain-free
      where jb = liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*)
    ...   | b* , held r* , bd* , btw , _ =
      b* , held r* , laneH x* (runs→ x rn) bd* (λ c → cut→ x jb nc (cut-up* c (held-in-l* bd*))) , jb , IJ.plain-free
      where jb = liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*)
    to (laneH {q} {a} {b} {r} x rn bd nc) with val→ x
    ... | a* , x* with Inter.BCorr.to (CL x x*) bd
    ...   | b* , _ , bd* , btw , IL.both-held {q* = r*} btwr =
      b* , held r* , laneH x* (runs→ x rn) bd* (cut→ x jr nc)
      , liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*) , IJ.both-held jr
      where jr = liftL x x* (mark-q bd) (mark-q bd*) btwr (held-l bd) (held-l* bd*)

    from : ∀ {b* g*} → JBd* b* g* → Σ Pos λ b → Σ Tag λ g → JBd b g × IJ.Between b b* × IJ.PutBefore b b* × IJ.TagFrom g g*
    from (outerB bd*) with fromO bd*
    ... | b , g , bd , btw , pb , tf =
      b , g , outerB bd , liftO (mark bd) (mark bd*) btw (gap-o bd) (gap-o* bd*)
      , putJ pb (outer-lane-put (mark bd) (mark bd*) pb) , tagO← bd bd* tf
    from (laneB {a = a*} x* rn* bd* nc*) with val← x*
    ... | q , a , x , refl with Inter.BCorr.from (CL x x*) bd*
    ...   | b , free , bd , btw , pb , _ =
      b , free , laneB x (runs← x rn*) bd (cut← x jb nc*) , jb , putL x x* (mark bd) (mark bd*) pb , IJ.elab-free
      where jb = liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*)
    ...   | b , held r , bd , btw , pb , _ =
      b , held r , laneH x (runs← x rn*) bd (λ c → cut← x jb nc* (cut-up c (held-in-l bd))) , jb , putL x x* (mark bd) (mark bd*) pb , IJ.elab-free
      where jb = liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*)
    from (laneH {a = a*} x* rn* bd* nc*) with val← x*
    ... | q , a , x , refl with Inter.BCorr.from (CL x x*) bd*
    ...   | b , _ , bd , btw , pb , IL.both-held {q = r} btwr =
      b , held r , laneH x (runs← x rn*) bd (cut← x jr nc*)
      , liftL x x* (mark bd) (mark bd*) btw (gap-l bd) (gap-l* bd*) , putL x x* (mark bd) (mark bd*) pb , IJ.both-held jr
      where jr = liftL x x* (mark-q bd) (mark-q bd*) btwr (held-l bd) (held-l* bd*)

    corr : IJ.BCorr
    corr = record { to = to ; from = from }
