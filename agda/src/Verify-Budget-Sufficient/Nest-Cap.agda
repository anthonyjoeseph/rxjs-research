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
   +-identityʳ; n≤1+n; m≤n+m; pred-mono-≤; +-suc; ^-distribˡ-+-*; +-mono-≤;
   *-suc; *-comm; ^-*-assoc; ^-monoʳ-≤; ^-monoˡ-≤; +-comm; pred[n]≤n)
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

  -- AND THE CAP ONLY EVER GROWS TOO, which is the half the LEVEL
  -- needs: a clause reporting its grant at one instant's cap answers a
  -- parent reading the same grant at a later one.  Every occurrence of
  -- the base sits under a `2 ^`, so the whole tower is monotone in it
  -- and the unit side does not mention it at all.
  nestB-monoS : ∀ {S S′ : ℕ} → S ≤ S′ → ∀ (W U B m : ℕ) →
    nestB S W U B m ≤ nestB S′ W U B m
  nestB-monoS hS W U B m =
    *-monoˡ-≤ (B + suc m * U)
      (^-monoˡ-≤ m (^-monoˡ-≤ (suc W) (pow-mono-exp 2 (s≤s z≤n) hS)))

  -- THE GRANT'S FACTOR, NAMED SEPARATELY BECAUSE THE FRAME LAYER
  -- SPENDS IT WITHOUT THE REST.  Once the descent has been flattened at
  -- the cap, everything above it carries one factor and one widened
  -- unit, and both are functions of the caps alone.
  -- THE ARR FACE'S GRANT SITS INSIDE THE CAP-KEYED ONE AT ONE LAYER,
  -- which is what lets a head proven against the telescope-read key
  -- answer the cap-keyed statement.  The arr grant doubles once per
  -- unit of the key and the cap-keyed grant doubles the CAP that many
  -- times per layer, so a key the cap dominates is dominated exponent
  -- and all; the unit side is the arr grant's `U + B` against a layer's
  -- `B + 2U`, which is the same two summands with one to spare.
  arrD≤nestB : ∀ (S W U B k : ℕ) → k ≤ S → arrD U B (suc W * k) ≤ nestB S W U B 1
  arrD≤nestB S W U B k hk = *-mono-≤ pow unit
    where
    pow : 2 ^ pred (suc W * k) ≤ ((2 ^ S) ^ suc W) ^ 1
    pow = ≤-trans (^-monoʳ-≤ 2
                    (≤-trans (pred[n]≤n {suc W * k})
                             (≤-trans (*-monoʳ-≤ (suc W) hk)
                                      (≤-reflexive (*-comm (suc W) S)))))
                  (≤-reflexive
                    (sym (trans (*-identityʳ ((2 ^ S) ^ suc W))
                                (^-*-assoc 2 S (suc W)))))

    unit : U + B ≤ B + suc 1 * U
    unit = ≤-trans (≤-reflexive (+-comm U B)) (+-monoʳ-≤ B (m≤m+n U (U + 0)))

  nestFac : (S W : ℕ) → ℕ
  nestFac S W = ((2 ^ S) ^ suc W) ^ S

  nestFac-def : ∀ (S W : ℕ) → nestFac S W ≡ ((2 ^ S) ^ suc W) ^ S
  nestFac-def S W = refl

  1≤nestFac : ∀ (S W : ℕ) → 1 ≤ nestFac S W
  1≤nestFac S W =
    1≤pow≤ ((2 ^ S) ^ suc W) S (1≤pow≤ (2 ^ S) (suc W) (1≤pow≤ 2 S (s≤s z≤n)))

  -- AND THE FACTOR GROWS WITH THE CAP, which is what a clause reporting
  -- its charge at one LEVEL owes a parent reading the same charge at a
  -- later one.  The cap occurs twice -- inside the base's own power and
  -- as the outer exponent -- and both occurrences are increasing, so
  -- the two widenings compose rather than fight.
  nestFac-monoS : ∀ {S S′ : ℕ} → S ≤ S′ → ∀ (W : ℕ) → nestFac S W ≤ nestFac S′ W
  nestFac-monoS {S} {S′} hS W =
    ≤-trans (^-monoˡ-≤ S (^-monoˡ-≤ (suc W) (pow-mono-exp 2 (s≤s z≤n) hS)))
            (pow-mono-exp ((2 ^ S′) ^ suc W)
              (1≤pow≤ (2 ^ S′) (suc W) (1≤pow≤ 2 S′ (s≤s z≤n))) hS)

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

  -- and the unit grows with the size it is priced at, which a consumer
  -- pricing one face at the bare cap and another at a wider one has to
  -- spend to put the two side by side
  nestU-mono : ∀ (S S′ U : ℕ) → S ≤ S′ → nestU S U ≤ nestU S′ U
  nestU-mono S S′ U h = *-monoˡ-≤ U (s≤s h)

  -- AND THE UNIT HAS ROOM FOR ONE WHOLE SIZE ON TOP OF ITS BASE, which
  -- is what a consumer holding a bound in one currency and owing it in
  -- a wider one spends: the price is a MULTIPLE of the base, so any
  -- rider within the size fits beside a base that is itself at least
  -- one.
  nestU-room : ∀ (S U x : ℕ) → 1 ≤ U → x ≤ S → U + x ≤ nestU S U
  nestU-room S U x 1≤U h =
    +-monoʳ-≤ U (≤-trans h (≤-trans (≤-reflexive (sym (*-identityʳ S)))
                                    (*-monoʳ-≤ S 1≤U)))

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

  -- WHAT A SLOT HEAD SPENDS TO HAND OFF TO ITS DEFINITION.  The
  -- descent on the definition is granted the whole UNIT as its
  -- additive term -- the telescope's nesting is a summand of the unit,
  -- so the definition's own depth is inside it however the caller's
  -- `B` is shaped -- and the one step of key the slot's closure buys
  -- over the definition's is worth exactly the factor of two that
  -- doubling the additive term costs.
  arrD-slot : ∀ (U B m : ℕ) → 1 ≤ m → arrD U U m ≤ arrD U B (suc m)
  arrD-slot U B (suc k) _ =
    ≤-trans (*-monoʳ-≤ (2 ^ k) (+-mono-≤ (m≤m+n U B) (m≤m+n U B)))
            (≤-reflexive eq)
    where
    eq : 2 ^ k * ((U + B) + (U + B)) ≡ 2 ^ suc k * (U + B)
    eq = trans (*-distribˡ-+ (2 ^ k) (U + B) (U + B))
               (sym (trans (*-assoc 2 (2 ^ k) (U + B))
                           (cong (λ z → 2 ^ k * (U + B) + z)
                                 (+-identityʳ (2 ^ k * (U + B))))))

  -- AND THE SAME FOUR AT A KEY READ OVER THE BURST'S WIDTH, which is
  -- the shape the arr-keyed walk takes once its statement reads the
  -- width at all.  A fold multiplies the delivered depth once per
  -- value while the key gains only what the value costs to write, so
  -- a grant read at the arrival alone loses a factor per value; read
  -- at `suc W` copies of the key it does not, because the key already
  -- contains the step's own duplication count and a doubling per copy
  -- outruns a duplication per value.
  --
  -- THEY ARE WRAPPERS AND NOT A SECOND FAMILY: each is its unscaled
  -- sibling followed by one `arrD-mono`, and the scaling factor is
  -- what pays for that step.  Keeping them here rather than at the
  -- call sites is what leaves the walk's clauses reading as they did.
  arrDW-mono : ∀ (U B W m m′ : ℕ) → m ≤ m′ →
    arrD U B (suc W * m) ≤ arrD U B (suc W * m′)
  arrDW-mono U B W m m′ hm =
    arrD-mono U B (suc W * m) (suc W * m′) (*-monoʳ-≤ (suc W) hm)

  1≤suc : ∀ (W : ℕ) → 1 ≤ suc W
  1≤suc W = s≤s z≤n

  arrDW-pos : ∀ (W m : ℕ) → 1 ≤ m → 1 ≤ suc W * m
  arrDW-pos W m hm = *-mono-≤ {1} {suc W} {1} {m} (1≤suc W) hm

  arrDW-key : ∀ (W m : ℕ) → m ≤ suc W * m
  arrDW-key W m = m≤m+n m (W * m)

  arrDW-bump : ∀ (W m : ℕ) → suc (suc W * m) ≤ suc W * suc m
  arrDW-bump W m =
    ≤-trans (+-monoˡ-≤ (suc W * m) (1≤suc W))
            (≤-reflexive (sym (*-suc (suc W) m)))

  arrDW-flat : ∀ (U B W k j : ℕ) → k ≤ suc W * j →
    2 ^ k * B ≤ arrD U B (suc W * suc j)
  arrDW-flat U B W k j hk =
    ≤-trans (arrD-flat U B k)
            (arrD-mono U B (suc k) (suc W * suc j)
              (≤-trans (s≤s hk) (arrDW-bump W j)))

  arrDW-slot : ∀ (U B W m : ℕ) → 1 ≤ m →
    arrD U U (suc W * m) ≤ arrD U B (suc W * suc m)
  arrDW-slot U B W m hm =
    ≤-trans (arrD-slot U B (suc W * m) (arrDW-pos W m hm))
            (arrD-mono U B (suc (suc W * m)) (suc W * suc m) (arrDW-bump W m))

  arrDW-frame : ∀ (U B W m k j : ℕ) → 1 ≤ m → B ≤ U + B → k ≤ suc W * j →
    2 ^ k * (B + arrD U B (suc W * m)) ≤ arrD U B (suc W * suc (j + m))
  arrDW-frame U B W m k j hm hB hk =
    ≤-trans (arrD-frame U B (suc W * m) k (arrDW-pos W m hm) hB)
            (arrD-mono U B (suc (k + suc W * m)) (suc W * suc (j + m)) step)
    where
    dist : suc W * suc (j + m) ≡ suc W + (suc W * j + suc W * m)
    dist = trans (*-suc (suc W) (j + m))
                 (cong (suc W +_) (*-distribˡ-+ (suc W) j m))
    step : suc (k + suc W * m) ≤ suc W * suc (j + m)
    step = ≤-trans (s≤s (+-monoˡ-≤ (suc W * m) hk))
                   (≤-trans (+-monoˡ-≤ (suc W * j + suc W * m) (1≤suc W))
                            (≤-reflexive (sym dist)))

  -- THE PER-LEVEL FACTOR IS ALREADY A WIDTH'S WORTH, which is what
  -- lets a frame charge read against a WIDENED key still fit.  The
  -- cap-keyed grant iterates `2 ^ S` once per unit of width before it
  -- iterates it once per level, so the two exponents commute and a
  -- grant at cap `S` and width `W` IS a grant at cap `suc W * S` and
  -- width zero.  Everything below is that observation spent.
  nestB-swap : ∀ (S W U B m : ℕ) → nestB S W U B m ≡ nestB (suc W * S) 0 U B m
  nestB-swap S W U B m = cong (λ z → z ^ m * (B + suc m * U)) eq
    where
    eq : (2 ^ S) ^ suc W ≡ (2 ^ (suc W * S)) ^ suc 0
    eq = trans (^-*-assoc 2 S (suc W))
               (trans (cong (2 ^_) (*-comm S (suc W)))
                      (sym (*-identityʳ (2 ^ (suc W * S)))))

  -- AND THE FRAME LAW AT THAT WIDER LEDGER.  A descent whose key is
  -- read over the burst's width spends an exponent up to `suc W * S`
  -- rather than `S`, and the sibling below is the same statement with
  -- the width folded into the cap.
  nestB-frame-dblW : ∀ (S W U B m k m′ : ℕ) → suc k ≤ suc W * S → suc m ≤ m′ →
    2 ^ k * (nestB S W U B m + nestB S W U B m) ≤ nestB S W U B m′
  nestB-frame-dblW S W U B m k m′ hk hm
    rewrite nestB-swap S W U B m | nestB-swap S W U B m′ =
    nestB-frame-dbl (suc W * S) 0 U B m k m′ hk hm
