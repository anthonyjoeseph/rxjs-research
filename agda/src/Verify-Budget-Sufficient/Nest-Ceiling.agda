-- THE LEVEL CEILING, AND IT IS A SHELF RATHER THAN A FACE.  Everything
-- here is arithmetic on the descent ledger: what a level costs, what a
-- frame's descent buys back, and the one place the ledger's domination
-- is a theorem.  It sits in its own module because it is in no mutual
-- block with the walk that spends it, and because the walk's module was
-- already the tower's most expensive.
module Verify-Budget-Sufficient.Nest-Ceiling where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-assoc; +-suc; +-mono-≤; +-monoʳ-≤;
  *-mono-≤; m≤m⊔n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

open import Rx.Evaluator using (opIterD; sLvlD-suc; lvls; dLvl; dCapᶜ; dWalkᶜ; regAt)
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; frameStep-0; opIterD-mono; opIterD-infl; sizeCount; sizeCount-body; cDel-body;
  lvls-add; lvls-mono; dWalkᶜ-mono; dCapᶜ-mono)
open import Verify-Budget-Sufficient.Op-Budget using (opIterD-dominated-at)
open import Verify-Budget-Sufficient.Caps-Chain using (op-desc; op-step-entry; quad-arith)

-- THE CEILING, CARRIED RELATIVELY -- what the walk owes and cannot
-- produce.  A level is only meaningful under a ceiling, and the
-- proven domination of the descent ledger is stated at level ZERO: it
-- says the whole instant's descent from the root fits in the caps
-- count.  Read at a level already reached, the same claim is false --
-- a walk standing at the ceiling still has a descent in front of it --
-- so the honest invariant is the REMAINING budget rather than the
-- level.  That is one implication per node, and it composes: a child
-- one frame down spends one operator of the parent's ledger.
CeilD : (c : Caps) (d Lv k m : ℕ) → Set
CeilD c d Lv k m =
  ∀ (L′ : ℕ) →
    Lv + L′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) d k m Lv →
    Lv + L′ ≤ sizeCount c d ⊔ Caps.cSize c

-- AND IT DESCENDS BY ONE OPERATOR, which is the whole reason the
-- relative form is the one carried.  A child sits one frame down with
-- a smaller closure budget and one operator fewer; `op-desc` is the
-- ledger equation saying a sweep at the successor level with the
-- operator unspent sits under the sweep with it spent, and the two
-- monotonicities put the child's own measures under the parent's.
-- AND THE LEVEL THE RECEIPT IS HELD AT IS ITSELF UNDER THE CEILING,
-- which is the reading a walk needs when it reports at the level it
-- ARRIVED at rather than at one it climbed to.  It is the receipt at
-- no further climb, and it is separate because the receipt is stated
-- relatively -- `Lv + L'` -- so the nil case is an arithmetic step
-- rather than an instance.
ceil-here : ∀ (c : Caps) (d Lv k m : ℕ) →
  CeilD c d Lv k m →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c
ceil-here c d Lv k m hceil =
  subst (_≤ sizeCount c d ⊔ Caps.cSize c) (+-identityʳ Lv)
   (hceil 0
    (subst (_≤ opIterD (Caps.cSize c) (Caps.cWid c) d k m Lv)
           (sym (+-identityʳ Lv))
           (opIterD-infl (Caps.cSize c) (Caps.cWid c) d k m Lv)))

ceil-step : ∀ (c : Caps) (d Lv k k′ m m′ : ℕ) → 2 ≤ Caps.cSize c →
  k′ ≤ k → suc m′ ≤ m → CeilD c d Lv k m → CeilD c d (suc Lv) k′ m′
ceil-step c d Lv k k′ m m′ 2≤S hk hm H L′ hL =
  subst (λ x → x ≤ sizeCount c d ⊔ Caps.cSize c) (+-suc Lv L′)
    (H (suc L′)
       (subst (λ x → x ≤ opIterD (Caps.cSize c) (Caps.cWid c) d k m Lv)
              (sym (+-suc Lv L′))
              (≤-trans hL
                 (≤-trans (opIterD-mono m′ m′ d d k′ k 2≤S ≤-refl ≤-refl ≤-refl
                             ≤-refl hk ≤-refl)
                    (≤-trans (op-desc (Caps.cSize c) (Caps.cWid c) d k m′ Lv 2≤S)
                             (opIterD-mono (suc m′) m d d k k 2≤S ≤-refl ≤-refl
                                ≤-refl ≤-refl ≤-refl hm))))))

-- AND IT WEAKENS IN BOTH MEASURES, which is the direction that looks
-- backwards and is not: a bigger closure budget or a longer operator
-- chain makes the LEDGER bigger, so the implication's hypothesis gets
-- weaker and the statement gets stronger.  Every arm therefore reads
-- its child's ceiling off a coarser one.
ceil-le : ∀ (c : Caps) (d Lv k k′ m m′ : ℕ) → 2 ≤ Caps.cSize c →
  k′ ≤ k → m′ ≤ m → CeilD c d Lv k m → CeilD c d Lv k′ m′
ceil-le c d Lv k k′ m m′ 2≤S hk hm H L′ hL =
  H L′ (≤-trans hL (opIterD-mono m′ m d d k′ k 2≤S ≤-refl ≤-refl ≤-refl
                      ≤-refl hk hm))

-- AND ONE STEP CROSSES LEVELS WITHOUT PAYING PER LEVEL, which is the
-- shape the relative descent above cannot have.  Any edge that enters a
-- FRESH subscribe is charged by the ledger as a new entry rather than as
-- a chain edge, so the level advances by whatever receipt the edge costs
-- -- and the operator index is MINTED at the arrival level's own size cap
-- instead of descending.  The one premise is that the receipt fits the
-- quadratic room the level opens, which is what `op-step-entry` states;
-- everything that jumps a level is an instance of this rather than a
-- copy of its proof.
ceil-entry-step : ∀ (c : Caps) (d Lv k m r : ℕ) → 2 ≤ Caps.cSize c →
  Lv + r ≤ suc (Lv + suc (Caps.cSize (frameStep Lv c))
                   * suc (Caps.cSize (frameStep Lv c))) →
  CeilD c d Lv (suc k) (suc m) →
  CeilD c d (Lv + r) k (suc (Caps.cSize (frameStep (Lv + r) c)))
ceil-entry-step c d Lv k m r 2≤S fits H L′ hL =
  subst (λ x → x ≤ sizeCount c d ⊔ Caps.cSize c)
        (sym (+-assoc Lv r L′))
    (H (r + L′)
       (op-step-entry (Caps.cSize c) (Caps.cWid c) d (suc k) m Lv r L′ 2≤S fits
          (≤-trans hL
             (≤-reflexive
                (sym (sLvlD-suc (Caps.cSize c) (Caps.cWid c) d k (Lv + r)))))))

-- AND A μ IS ONE OF THEM: it subscribes a LARGER term, so the receipt is
-- the quadratic the unfolding costs and the room is exactly the room the
-- step above opens.  Nothing here is about μ except the receipt.
ceil-mu : ∀ (c : Caps) (d Lv k m m₀ : ℕ) → 2 ≤ Caps.cSize c →
  m₀ ≤ Caps.cSize (frameStep Lv c) →
  CeilD c d Lv (suc k) (suc m) →
  CeilD c d (Lv + (m₀ + suc (m₀ * m₀))) k
    (suc (Caps.cSize (frameStep (Lv + (m₀ + suc (m₀ * m₀))) c)))
ceil-mu c d Lv k m m₀ 2≤S hm₀ H =
  ceil-entry-step c d Lv k m (m₀ + suc (m₀ * m₀)) 2≤S
    (≤-trans (+-monoʳ-≤ Lv
                (≤-trans (+-mono-≤ hm₀ (s≤s (*-mono-≤ hm₀ hm₀))) (quad-arith B)))
             (n≤1+n (Lv + suc B * suc B)))
    H
  where
  B = Caps.cSize (frameStep Lv c)

-- WHAT A LEVEL HAS LEFT, and it is the receipt the refuted drain
-- conjunct was standing in for and failing to carry.  A term subscribed
-- at a level is dominated by the cascade's own delivery walk read FROM
-- that level -- the budget module's bound at an arbitrary level, which
-- was always stated there and only ever spent at zero -- so what a
-- ceiling costs is that walk fitting under the count.  A bare level
-- bound cannot say it, which is why the flat form was refutable.
--
-- AND THE GAS IS THE TERM'S OWN, WHICH IS WHAT MAKES THIS SUPPLYABLE.
-- At the whole cascade's gas the receipt is FALSE above the bottom and
-- needs no witness: the delivery budget read at a higher level is the
-- larger one and the ladder from there is longer, so both sides move
-- the wrong way at once.  What the domination actually consumes is four
-- plus the term's OPERATOR COUNT -- a syntactic quantity, fixed before
-- any level exists and small where the cascade's own gas is the size
-- cap.  So the receipt is asked for per subscribed term rather than per
-- level, and a queue's head asks it of its own head.
RoomG : Caps → ℕ → ℕ → ℕ → Set
RoomG c d Lv g =
  lvls (Caps.cSize c) (Caps.cWid c) d Lv
    (dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g Lv)
    ≤ sizeCount c d ⊔ Caps.cSize c

ceil-room : ∀ (c : Caps) (d Lv k m : ℕ) → 2 ≤ Caps.cSize c →
  3 + k ≤ Caps.cSize c → m ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  RoomG c d Lv (4 + k) →
  CeilD c d Lv k m
ceil-room c d Lv k m 2≤S hk hm 1≤R room L′ hL =
  ≤-trans hL
    (≤-trans (opIterD-dominated-at (Caps.cSize c) (Caps.cWid c) d k m
                (Caps.cReg c) Lv 2≤S hk hm 1≤R)
             room)

-- AND THE PARKED TERM ASKS IT AT THE LEVEL IT WAS PARKED AT, which is
-- the only cap anything holds about it.  A queue's entry arrived at a
-- frame the walk had already stepped into and was written to the node
-- table there, so the store predicate re-establishes its size one
-- level up at every park and the base reading is not available at any
-- queue at all.  Both premises therefore move to the stepped cap, and
-- what has to hold is that the domination survives the move: the
-- count on the right carries `4 + k` too, so raising the ceiling on
-- `k` raises the budget it is measured against, and the question is
-- whether it raises it by enough.
--
-- AND IT IS NOT A WEAKENING OF THE ROW ABOVE, which stays at the base
-- cap for the terms that can be read there -- an entry the cascade
-- subscribes directly is one, and pays nothing for it.
-- REFUTED: `Refuted.Drain-Queue-Flat.drain-room-flat-absurd`, which
--   is the base reading being unavailable to a queue.

-- and the zero level is not part of the question: the step is the
-- identity there, so that clause IS the row above and the leaf is
-- everything past it
postulate
  ceil-park-suc : ∀ (c : Caps) (d Lv k m : ℕ) → 2 ≤ Caps.cSize c →
    3 + k ≤ Caps.cSize (frameStep (suc Lv) c) →
    m ≤ Caps.cSize (frameStep (suc Lv) c) → 1 ≤ Caps.cReg c →
    RoomG c d (suc Lv) (4 + k) →
    CeilD c d (suc Lv) k m

ceil-park : ∀ (c : Caps) (d Lv k m : ℕ) → 2 ≤ Caps.cSize c →
  3 + k ≤ Caps.cSize (frameStep Lv c) →
  m ≤ Caps.cSize (frameStep Lv c) → 1 ≤ Caps.cReg c →
  RoomG c d Lv (4 + k) →
  CeilD c d Lv k m
ceil-park c d zero k m 2≤S hk hm 1≤R room =
  ceil-room c d 0 k m 2≤S
    (subst (λ x → 3 + k ≤ Caps.cSize x) (frameStep-0 c) hk)
    (subst (λ x → m ≤ Caps.cSize x) (frameStep-0 c) hm) 1≤R room
ceil-park c d (suc Lv) k m 2≤S hk hm 1≤R room =
  ceil-park-suc c d Lv k m 2≤S hk hm 1≤R room

-- AND THE RECEIPT DESCENDS THE WALK EXACTLY, WHICH IS WHY IT IS ASKED
-- FOR AND NOT PROBED.  Neither side of the room can be instantiated:
-- both are levels in the delivery ladder, and the ladder outruns
-- computation at its own smallest legal instance -- the right-hand side
-- alone, at the two-slot cap with one registration and no depth, does
-- not finish.  So no probe and no harness row can reach this statement,
-- which is a coverage boundary rather than a gap in the sweeping.
--
-- WHAT REPLACES A ROW IS THAT THE WALK'S OWN RECURRENCE CARRIES IT.  A
-- position of the delivery walk spends `w + suc (dCapᶜ … at the level
-- w restarts reach)`, and `w + suc C` is `suc w + C`, so splitting the
-- count at `suc w` turns the budget read from that level into the walk
-- read from the base -- an EQUALITY, not a bound.  A level the walk
-- reaches therefore inherits its room from the base's, one gas up, and
-- the bottom is the entry.
room-step : ∀ (S W R d g J i : ℕ) →
  lvls S W d (lvls S W d J (suc (dWalkᶜ S W R d g J i)))
      (dCapᶜ S W R d g (lvls S W d J (suc (dWalkᶜ S W R d g J i))))
    ≡ lvls S W d J (dWalkᶜ S W R d g J (suc i))
room-step S W R d g J i =
  sym (trans (cong (lvls S W d J) (+-suc w C)) (lvls-add S W d J (suc w) C))
  where
  w = dWalkᶜ S W R d g J i
  C = dCapᶜ S W R d g (lvls S W d J (suc w))

room-descend : ∀ (c : Caps) (d g J i : ℕ) → 2 ≤ Caps.cSize c →
  suc i ≤ regAt (Caps.cSize c) (Caps.cReg c) J →
  RoomG c d J (suc g) →
  RoomG c d (lvls (Caps.cSize c) (Caps.cWid c) d J
              (suc (dWalkᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J i))) g
room-descend c d g J i 2≤S hi room =
  ≤-trans (≤-reflexive (room-step S W R d g J i))
  (≤-trans (lvls-mono (dWalkᶜ S W R d g J (suc i)) (dWalkᶜ S W R d g J (regAt S R J))
              2≤S ≤-refl ≤-refl ≤-refl
              (dWalkᶜ-mono {S} {S} {W} {W} {R} {R} {J} {J} {d}
                 g g (suc i) (regAt S R J) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hi))
           room)
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c

-- A LEVEL THE CASCADE ACTUALLY REACHES, TOGETHER WITH WHAT IT HAS LEFT.
-- The bottom is reached with the whole dispatch gas; a position of the
-- delivery walk from a reached level reaches the level that position
-- lands on, with one gas less -- which is the walk recurrence read as a
-- relation rather than as a number.  Carrying the gas is the point: it
-- is what a level bound cannot say and what makes the room derivable
-- instead of assumed.
-- THE LEVEL THE `i`-TH CHAIN OF A ROUND IS ENTERED AT.  The walk's
-- ledger `dWalkᶜ … i` is what the round has spent before this chain,
-- and one restart past that is where the chain begins.
Ent : Caps → ℕ → ℕ → ℕ → ℕ → ℕ
Ent c d J g i =
  lvls (Caps.cSize c) (Caps.cWid c) d J
    (dWalkᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J i)

Pos : Caps → ℕ → ℕ → ℕ → ℕ → ℕ
Pos c d J g i = dLvl (Caps.cSize c) (Caps.cWid c) d (Ent c d J g i)

data Reached (c : Caps) (d : ℕ) : ℕ → ℕ → Set where
  base : Reached c d 0 (suc (Caps.cSize c))
  walk : ∀ (J g i : ℕ) →
    suc i ≤ regAt (Caps.cSize c) (Caps.cReg c) J →
    Reached c d J (suc g) →
    Reached c d (Pos c d J g i) g

-- AND A REACHED LEVEL HAS ITS ROOM, which is what the relation was for:
-- the bottom by the two bodies, every other level by the walk step.
reached-room : ∀ (c : Caps) (d Lv g : ℕ) → 2 ≤ Caps.cSize c →
  Reached c d Lv g → RoomG c d Lv g
reached-room c d .0 .(suc (Caps.cSize c)) 2≤S base =
  ≤-trans (≤-reflexive (sym (trans (sizeCount-body c d)
                                   (cong (lvls (Caps.cSize c) (Caps.cWid c) d 0)
                                         (cDel-body c d)))))
          (m≤m⊔n (sizeCount c d) (Caps.cSize c))
reached-room c d _ g 2≤S (walk J g′ i hi r) =
  room-descend c d g′ J i 2≤S hi (reached-room c d J (suc g′) 2≤S r)

-- AND LESS GAS IS LESS ROOM, so a term asks for what it costs rather
-- than for what the level happens to hold.
room-gas : ∀ (c : Caps) (d Lv g g′ : ℕ) → 2 ≤ Caps.cSize c → g′ ≤ g →
  RoomG c d Lv g → RoomG c d Lv g′
room-gas c d Lv g g′ 2≤S hg room =
  ≤-trans (lvls-mono (dCapᶜ S W R d g′ Lv) (dCapᶜ S W R d g Lv)
             2≤S ≤-refl ≤-refl ≤-refl
             (dCapᶜ-mono {S} {S} {W} {W} {R} {R} {Lv} {Lv} {d}
                g′ g 2≤S ≤-refl ≤-refl ≤-refl hg ≤-refl))
          room
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c

-- ONE CHAIN OF A ROUND ADVANCES THE POSITION BY ITS OWN BUDGET, and
-- the fold's actual climb is under it exactly when the chain's
-- deliveries are.  `dWalkᶜ` at a `suc` is the ledger plus one restart
-- plus the cap read AT the chain's own level, which is the same
-- `lvls-add` split the cascade fold already makes per chain -- so the
-- two ladders differ only in the count, and the residue is one
-- comparison of a delivery total against the budget at that level.
ent-step : ∀ (c : Caps) (d J g i D : ℕ) → 2 ≤ Caps.cSize c →
  D ≤ dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g (Pos c d J g i) →
  lvls (Caps.cSize c) (Caps.cWid c) d (Ent c d J g i) (suc D)
    ≤ Ent c d J g (suc i)
ent-step c d J g i D 2≤S hD =
  ≤-trans (lvls-mono (suc D) (suc C) 2≤S ≤-refl ≤-refl ≤-refl (s≤s hD))
          (≤-reflexive (sym (lvls-add S W d J w (suc C))))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c
  w = dWalkᶜ S W R d g J i
  C = dCapᶜ S W R d g (Pos c d J g i)


-- THE WALK'S LEVEL IS BOUNDED BY A DELIVERY POSITION, NOT EQUAL TO ONE.
-- A chain advances its level by one `fLvlD` charge per frame, while the
-- cascade's walk advances by whole `dLvl` restarts, so the levels a
-- chain visits sit BETWEEN two positions the walk lands on.  Room is
-- monotone the useful way: both the ladder from a level and the budget
-- read at it grow with the level, so a receipt at the position ABOVE
-- covers every level under it, and the reaching obligation is a `≤`.
room-le : ∀ (c : Caps) (d Lv Lv′ g : ℕ) → 2 ≤ Caps.cSize c → Lv ≤ Lv′ →
  RoomG c d Lv′ g → RoomG c d Lv g
room-le c d Lv Lv′ g 2≤S hLv room =
  ≤-trans (lvls-mono (dCapᶜ S W R d g Lv) (dCapᶜ S W R d g Lv′)
             2≤S ≤-refl ≤-refl hLv
             (dCapᶜ-mono {S} {S} {W} {W} {R} {R} {Lv} {Lv′} {d}
                g g 2≤S ≤-refl ≤-refl ≤-refl ≤-refl hLv))
          room
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c
