-- THE LEVEL CEILING, AND IT IS A SHELF RATHER THAN A FACE.  Everything
-- here is arithmetic on the descent ledger: what a level costs, what a
-- frame's descent buys back, and the one place the ledger's domination
-- is a theorem.  It sits in its own module because it is in no mutual
-- block with the walk that spends it, and because the walk's module was
-- already the tower's most expensive.
module Verify-Budget-Sufficient.Nest-Ceiling where

open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-assoc; +-suc; +-mono-≤; +-monoʳ-≤; *-mono-≤)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Rx.Evaluator using (opIterD; sLvlD-suc; lvls; dCapᶜ)
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; opIterD-mono; sizeCount)
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
