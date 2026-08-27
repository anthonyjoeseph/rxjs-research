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

open import Data.Nat using (ℕ; suc; pred; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
   +-monoʳ-≤; +-monoˡ-≤; *-identityˡ; *-identityʳ; *-assoc; *-distribˡ-+; *-distribʳ-+;
   +-identityʳ; n≤1+n; m≤n+m; pred-mono-≤; +-suc; ^-distribˡ-+-*; +-mono-≤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Verify-Budget-Sufficient.Caps using (1≤pow≤)

-- ITERATING A BASE OF AT LEAST ONE ONLY GROWS, and the stdlib's own
-- form of this asks for a `NonZero` instance the caller here cannot
-- produce -- the base is a power, not a numeral.  One induction on the
-- `≤` is cheaper than manufacturing the instance.
pow-mono-exp : ∀ (F : ℕ) → 1 ≤ F → ∀ {m m′ : ℕ} → m ≤ m′ → F ^ m ≤ F ^ m′
pow-mono-exp F 1≤F {m′ = m′} z≤n     = 1≤pow≤ F m′ 1≤F
pow-mono-exp F 1≤F           (s≤s le) = *-monoʳ-≤ F (pow-mono-exp F 1≤F le)

-- THE ARRIVAL'S OWN GRANT, and it is deliberately NOT sealed.  The
-- sealing rule is about a body that reaches the caps recurrence and so
-- lands in every premise that names it; this is one multiplication,
-- and its consumers read it against a `nestB`-shaped frame charge that
-- can only be discharged by unfolding both sides.
arrD : ℕ → ℕ → ℕ → ℕ
arrD U B m = 2 ^ pred m * (U + B)

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

  -- THE PROGRAM'S UNIT IS UNDER EVERY GRANT, one copy per level and at
  -- least one level always present.
  nestB-unit : ∀ (S W U B m : ℕ) → U ≤ nestB S W U B m
  nestB-unit S W U B m =
    ≤-trans (m≤m+n U (m * U))
    (≤-trans (m≤n+m (suc m * U) B)
    (≤-trans (≤-reflexive (sym (*-identityˡ (B + suc m * U))))
             (*-monoˡ-≤ (B + suc m * U)
                (1≤pow≤ ((2 ^ S) ^ suc W) m
                   (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n)))))))

  -- ONE LEVEL OF THE KEY BUYS A DOUBLING, which is the form a descent
  -- read against its ARRIVAL wants rather than against the depth the
  -- grant was opened at.  A substituting frame may name its payload
  -- twice, so what it delivers is two copies of what it received; a
  -- level of the key is a full copy of the per-frame factor, and `2 ^ S`
  -- covers the doubling with the frame's own factor still to spare.
  nestB-frame-dbl : ∀ (S W U B m k m′ : ℕ) → suc k ≤ S → suc m ≤ m′ →
    2 ^ k * (nestB S W U B m + nestB S W U B m) ≤ nestB S W U B m′
  nestB-frame-dbl S W U B m k m′ hk hm =
    ≤-trans step1 (≤-trans step2 (≤-trans step3 (≤-trans step4 step5)))
    where
    N : ℕ
    N = nestB S W U B m
    step1 : 2 ^ k * (N + N) ≤ (2 ^ k + 2 ^ k) * N
    step1 = ≤-reflexive (trans (*-distribˡ-+ (2 ^ k) N N)
                               (sym (*-distribʳ-+ N (2 ^ k) (2 ^ k))))
    step2 : (2 ^ k + 2 ^ k) * N ≤ 2 ^ S * N
    step2 = *-monoˡ-≤ N (pow2-dbl S k hk)
    step3 : 2 ^ S * N ≤ ((2 ^ S) ^ suc W) * N
    step3 = *-monoˡ-≤ N
              (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ S))))
                       (*-monoʳ-≤ (2 ^ S)
                          (1≤pow≤ (2 ^ S) W (1≤pow≤ 2 S (s≤s z≤n)))))
    step4 : ((2 ^ S) ^ suc W) * N
              ≤ ((2 ^ S) ^ suc W) ^ suc m * (B + suc m * U)
    step4 = ≤-reflexive (sym (*-assoc ((2 ^ S) ^ suc W)
                                      (((2 ^ S) ^ suc W) ^ m) (B + suc m * U)))
    step5 : ((2 ^ S) ^ suc W) ^ suc m * (B + suc m * U) ≤ nestB S W U B m′
    step5 = *-mono-≤ (pow-mono-exp ((2 ^ S) ^ suc W)
                        (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n))) hm)
                     (+-monoʳ-≤ B (*-monoˡ-≤ U (≤-trans hm (n≤1+n m′))))

  -- ONE LEVEL OF THE KEY BUYS ONE FRAME, which is the whole reason the
  -- grant is keyed on the term's size: a substituting frame charges two
  -- to its own size, the head that installs it is at least one node
  -- bigger than what it descends into, and the room a level releases is
  -- a full copy of the per-frame factor.  The `+ B` is the frame's own
  -- additive charge, which is under the depth the grant was opened at.
  nestB-frame : ∀ (S W U B m k m′ : ℕ) → suc k ≤ S → suc m ≤ m′ →
    2 ^ k * (B + nestB S W U B m) ≤ nestB S W U B m′
  nestB-frame S W U B m k m′ hk hm =
    ≤-trans (*-monoʳ-≤ (2 ^ k)
               (+-monoˡ-≤ (nestB S W U B m) (nestB-base S W U B m)))
            (nestB-frame-dbl S W U B m k m′ hk hm)

  -- THE SAME LAW WITHOUT A CAP, which is what a bound tight in the
  -- ARRIVAL costs and what it buys.  `arrD` charges two per unit of
  -- term size rather than a whole per-level factor, so a frame of
  -- local size `k` sitting above a subterm of size `m` lands at
  -- `suc (k + m)` and the doubling that the extra `suc (k + m) - m`
  -- units release is EXACTLY the frame's charge -- no slack, and no
  -- premise relating `k` to any cap.  That is the difference the
  -- consume steps spend: `nestB-frame` must be told `suc k ≤ S`
  -- because its per-level factor is fixed by the cap and the frame's
  -- size is not, while here the exponent and the size are the same
  -- quantity.  The one thing it needs is that a subterm's size is
  -- POSITIVE, which every clause of `syncSizeᵉ` gives.
  arrD-mono : ∀ (U B m m′ : ℕ) → m ≤ m′ → arrD U B m ≤ arrD U B m′
  arrD-mono U B m m′ hm =
    *-monoˡ-≤ (U + B) (pow-mono-exp 2 (s≤s z≤n) (pred-mono-≤ hm))

  arrD-frame : ∀ (U B m k : ℕ) → 1 ≤ m → B ≤ U + B →
    2 ^ k * (B + arrD U B m) ≤ arrD U B (suc (k + m))
  arrD-frame U B (suc m) k _ hB =
    ≤-trans (≤-reflexive (*-distribˡ-+ (2 ^ k) B (arrD U B (suc m))))
            (≤-trans (+-mono-≤ lo hi) dbl)
    where
    lo : 2 ^ k * B ≤ 2 ^ (k + m) * (U + B)
    lo = *-mono-≤ (pow-mono-exp 2 (s≤s z≤n) (m≤m+n k m)) hB
    hi : 2 ^ k * arrD U B (suc m) ≤ 2 ^ (k + m) * (U + B)
    hi = ≤-reflexive (trans (sym (*-assoc (2 ^ k) (2 ^ m) (U + B)))
                            (cong (_* (U + B)) (sym (^-distribˡ-+-* 2 k m))))
    two : 2 ^ (k + suc m) ≡ 2 ^ (k + m) + 2 ^ (k + m)
    two = trans (cong (2 ^_) (+-suc k m))
                (cong (2 ^ (k + m) +_) (+-identityʳ (2 ^ (k + m))))
    dbl : 2 ^ (k + m) * (U + B) + 2 ^ (k + m) * (U + B)
            ≤ arrD U B (suc (k + suc m))
    dbl = ≤-reflexive
            (trans (sym (*-distribʳ-+ (U + B) (2 ^ (k + m)) (2 ^ (k + m))))
                   (cong (_* (U + B)) (sym two)))

  -- and the FLAT head, where there is no subterm to have a size: a
  -- one-shot emits its own terms and nothing descends, so the whole
  -- charge is the head's own and the grant it lands in is the head's
  -- own size.
  arrD-flat : ∀ (U B k : ℕ) → 2 ^ k * B ≤ arrD U B (suc k)
  arrD-flat U B k = *-monoʳ-≤ (2 ^ k) (m≤n+m B U)
