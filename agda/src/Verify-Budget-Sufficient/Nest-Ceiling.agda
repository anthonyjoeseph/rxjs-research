-- THE LEVEL CEILING, AND IT IS A SHELF RATHER THAN A FACE.  Everything
-- here is arithmetic on the descent ledger: what a level costs, what a
-- frame's descent buys back, and the one place the ledger's domination
-- is a theorem.  It sits in its own module because it is in no mutual
-- block with the walk that spends it, and because the walk's module was
-- already the tower's most expensive.
module Verify-Budget-Sufficient.Nest-Ceiling where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-assoc; +-suc; m≤m⊔n;
  +-mono-≤; +-monoʳ-≤; *-mono-≤)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Rx.Evaluator using (opIterD; sLvlD-suc)
open import Verify-Budget-Sufficient.Caps using
  (Caps; frameStep; frameStep-0; opIterD-mono; sizeCount; sizeCount-body)
open import Verify-Budget-Sufficient.Op-Budget using (opIterD-dominated)
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

-- AND AT LEVEL ZERO THE CEILING IS A THEOREM, WHICH IS WHAT THE WHOLE
-- RELATIVE FORM WAS FOR.  The descent ledger read from the bottom is
-- dominated by the caps count -- that is the proven inequality this
-- development already spends at the entry -- and the ceiling is that
-- inequality with the implication wrapped round it.  So a consumer
-- carrying the ceiling as an assumption is carrying something it could
-- have derived from two size bounds and the two entry facts every face
-- of this walk already has in its ambient bundle.
ceil-entry : ∀ (c : Caps) (d k m : ℕ) → 2 ≤ Caps.cSize c →
  3 + k ≤ Caps.cSize c → m ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  CeilD c d 0 k m
ceil-entry c d k m 2≤S hk hm 1≤R L′ hL =
  ≤-trans hL
    (≤-trans (≤-trans (opIterD-dominated (Caps.cSize c) (Caps.cWid c) d k m
                         (Caps.cReg c) 2≤S hk hm 1≤R)
                      (≤-reflexive (sym (sizeCount-body c d))))
             (m≤m⊔n (sizeCount c d) (Caps.cSize c)))


-- THE CEILING A LEVEL CARRIES, and it is a PACKAGE rather than a
-- ceiling.  A walk standing at a level has to be able to MINT a ceiling
-- for a term it has just taken off a queue, at that term's own measures
-- and not at the ones its parent happened to be descending -- which is
-- what the relative form one section up cannot do, since every one of
-- its steps consumes a measure the parent chose.  Quantifying the
-- measures over the level's own size cap is what makes minting
-- possible, and it costs nothing at the bottom: the two premises are
-- exactly the entry theorem's, so level zero IS the entry theorem.
record CeilAt (c : Caps) (d Lv : ℕ) : Set where
  constructor ceilAt
  field
    mint : ∀ (k m : ℕ) →
      3 + k ≤ Caps.cSize (frameStep Lv c) →
      m ≤ Caps.cSize (frameStep Lv c) →
      CeilD c d Lv k m

ceilAt-entry : ∀ (c : Caps) (d : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  CeilAt c d 0
ceilAt-entry c d 2≤S 1≤R = ceilAt λ k m hk hm →
  ceil-entry c d k m 2≤S
    (subst (λ x → 3 + k ≤ Caps.cSize x) (frameStep-0 c) hk)
    (subst (λ x → m ≤ Caps.cSize x) (frameStep-0 c) hm) 1≤R

-- AND AT A POSITIVE LEVEL IT IS NOT PROVEN, which is the whole of what
-- this leaf owes and the whole of what the refuted drain conjunct was
-- standing in for.  The package has to serve measures under the level's
-- OWN cap, which grows with the level, while the ladder's rounds are
-- consumed by climbing to it -- so it asks for more room after the
-- climb than before, and the level alone is the wrong thing to ask it
-- of.
--
-- WHAT THE HONEST FORM PROBABLY CARRIES IS THE REMAINING BUDGET.  The
-- ledger's own proven machinery prices a sweep from an arbitrary level
-- against a receipt saying how much of the ladder that level has already
-- spent, rather than against the level alone; `walk-paid` and
-- `climb-paid` in the budget module are stated exactly that way, and
-- the entry theorem below is their instance at a level that has spent
-- nothing.  A hypothesis bounding the level by the count cannot say
-- that the climb left room, which is where a refutation would come
-- from -- and the level ladder does reach the count.
postulate
  ceilAt-suc : ∀ (c : Caps) (d Lv : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
    suc Lv ≤ sizeCount c d ⊔ Caps.cSize c →
    CeilAt c d (suc Lv)

-- AND THE PACKAGE AT ANY LEVEL THE LADDER ADMITS, which is the form
-- every level-indexed face wants: each already carries the level bound,
-- so nothing has to be threaded to reach a mint.
ceilAt-any : ∀ (c : Caps) (d Lv : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  CeilAt c d Lv
ceilAt-any c d zero    2≤S 1≤R hlv = ceilAt-entry c d 2≤S 1≤R
ceilAt-any c d (suc Lv) 2≤S 1≤R hlv = ceilAt-suc c d Lv 2≤S 1≤R hlv
