------------------------------------------------------------------
-- THE NEST WALK'S GRANT, AND WHAT MAKES IT A DIFFERENT NUMBER AT
-- EVERY LEVEL OF THE DESCENT.
--
-- The shared statement one module over used to grant a FIXED bound:
-- the same number at the parent and at the child, so a head whose
-- frame substitutes into the values passing through it had nothing to
-- pay its factor out of.  What repairs that is a grant keyed to the
-- SIZE still to be descended -- one that shrinks at every head, so the
-- room the head needs is exactly the room the size released.
--
-- IT TAKES A NUMBER AND NOT AN EXPRESSION, which is what keeps it
-- arithmetic: the descent's two directions differ only in a `ℕ`, and a
-- monotonicity lemma stated over that `ℕ` serves heads at unrelated
-- types.  The caller supplies the size.
--
-- AND IT IS SEALED, because it lands in a CONCLUSION the walk carries
-- through every recursive call: a transparent body would put a double
-- exponential inside every application of every statement mentioning
-- it.  The lemmas below are the whole interface.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Cap where

open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
   +-monoʳ-≤; +-monoˡ-≤; *-identityˡ; *-identityʳ; *-assoc; *-distribˡ-+; *-distribʳ-+;
   +-identityʳ; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Verify-Budget-Sufficient.Caps using (1≤pow≤)

-- ITERATING A BASE OF AT LEAST ONE ONLY GROWS, and the stdlib's own
-- form of this asks for a `NonZero` instance the caller here cannot
-- produce -- the base is a power, not a numeral.  One induction on the
-- `≤` is cheaper than manufacturing the instance.
pow-mono-exp : ∀ (F : ℕ) → 1 ≤ F → ∀ {m m′ : ℕ} → m ≤ m′ → F ^ m ≤ F ^ m′
pow-mono-exp F 1≤F {m′ = m′} z≤n     = 1≤pow≤ F m′ 1≤F
pow-mono-exp F 1≤F           (s≤s le) = *-monoʳ-≤ F (pow-mono-exp F 1≤F le)

abstract
  -- THE GRANT AT A DESCENT OF SIZE `m`, over a base `S`, a burst width
  -- `W`, the program's nesting unit `U` and the descent's own depth
  -- `B`.  One factor per level, and one unit per level beside it.
  nestB : (S W U B m : ℕ) → ℕ
  nestB S W U B m = ((2 ^ S) ^ suc W) ^ m * (B + suc m * U)

  -- A DESCENT NEVER GROWS, so this is the whole of what a head spends
  -- to move its child's grant up to its own.
  nestB-mono : ∀ (S W U B : ℕ) {m m′ : ℕ} → m ≤ m′ →
    nestB S W U B m ≤ nestB S W U B m′
  nestB-mono S W U B le =
    *-mono-≤ (pow-mono-exp ((2 ^ S) ^ suc W) 1≤F le)
             (+-monoʳ-≤ B (*-monoˡ-≤ U (s≤s le)))
    where
    1≤F : 1 ≤ ((2 ^ S) ^ suc W)
    1≤F = 1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n))

  -- THE GRANT'S FACTOR, NAMED SEPARATELY BECAUSE THE FRAME LAYER
  -- SPENDS IT WITHOUT THE REST.  Once the descent has been flattened at
  -- the cap, everything above it carries one factor and one widened
  -- unit, and both are functions of the caps alone.
  nestFac : (S W : ℕ) → ℕ
  nestFac S W = ((2 ^ S) ^ suc W) ^ S

  nestFac-def : ∀ (S W : ℕ) → nestFac S W ≡ ((2 ^ S) ^ suc W) ^ S
  nestFac-def S W = refl

  1≤nestFac : ∀ (S W : ℕ) → 1 ≤ nestFac S W
  1≤nestFac S W =
    1≤pow≤ ((2 ^ S) ^ suc W) S (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n)))

  -- THE UNIT THE FRAME LAYER CARRIES, which is the program's own unit
  -- once per level the descent may have spent it at.  Named so that the
  -- walk above can be stated over one opaque summand rather than
  -- re-deriving the count at every arm.
  nestU : (S U : ℕ) → ℕ
  nestU S U = suc S * U

  -- and the grant at the cap IS the frame layer's shape, which is what
  -- lets the drain hand its result straight up
  nestB-at : ∀ (S W U B : ℕ) → nestB S W U B S ≤ nestFac S W * (B + nestU S U)
  nestB-at S W U B = ≤-refl

  nestU-base : ∀ (S U : ℕ) → U ≤ nestU S U
  nestU-base S U = m≤m+n U (S * U)

  -- THE LEAF HEADS' WHOLE OBLIGATION: a subscribe that installs
  -- nothing and emits nothing is under its own grant at every size.
  nestB-base : ∀ (S W U B m : ℕ) → B ≤ nestB S W U B m
  nestB-base S W U B m =
    ≤-trans (m≤m+n B (suc m * U))
            (≤-trans (≤-reflexive (sym (*-identityˡ (B + suc m * U))))
                     (*-monoˡ-≤ (B + suc m * U)
                        (1≤pow≤ ((2 ^ S) ^ suc W) m
                           (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n))))))

  -- DOUBLING A POWER OF TWO IS ONE STEP OF ITS EXPONENT, and the step
  -- is available because a head is at least one node bigger than the
  -- function it installs.
  pow2-dbl : ∀ (S k : ℕ) → suc k ≤ S → 2 ^ k + 2 ^ k ≤ 2 ^ S
  pow2-dbl S k hk =
    ≤-trans (≤-reflexive (cong (2 ^ k +_) (sym (+-identityʳ (2 ^ k)))))
            (pow-mono-exp 2 (s≤s z≤n) hk)

  -- ONE LEVEL OF THE KEY BUYS ONE FRAME, which is the whole reason the
  -- grant is keyed on the term's size: a substituting frame charges two
  -- to its own size, the head that installs it is at least one node
  -- bigger than what it descends into, and the room a level releases is
  -- a full copy of the per-frame factor.  The `+ B` is the frame's own
  -- additive charge, which is under the depth the grant was opened at.
  nestB-frame : ∀ (S W U B m k m′ : ℕ) → suc k ≤ S → suc m ≤ m′ →
    2 ^ k * (B + nestB S W U B m) ≤ nestB S W U B m′
  nestB-frame S W U B m k m′ hk hm =
    ≤-trans (*-monoʳ-≤ (2 ^ k) (+-monoˡ-≤ (nestB S W U B m) (nestB-base S W U B m)))
    (≤-trans (≤-reflexive
               (trans (*-distribˡ-+ (2 ^ k) (nestB S W U B m) (nestB S W U B m))
                      (sym (*-distribʳ-+ (nestB S W U B m) (2 ^ k) (2 ^ k)))))
    (≤-trans (*-monoˡ-≤ (nestB S W U B m) (pow2-dbl S k hk))
    (≤-trans (*-monoˡ-≤ (nestB S W U B m)
               (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ S))))
                        (*-monoʳ-≤ (2 ^ S) (1≤pow≤ (2 ^ S) W (1≤pow≤ 2 S (s≤s z≤n))))))
    (≤-trans (≤-reflexive
               (sym (*-assoc ((2 ^ S) ^ suc W) (((2 ^ S) ^ suc W) ^ m)
                             (B + suc m * U))))
             (*-mono-≤ (pow-mono-exp ((2 ^ S) ^ suc W)
                          (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n))) hm)
                       (+-monoʳ-≤ B
                         (*-monoˡ-≤ U (≤-trans hm (n≤1+n m′)))))))))
