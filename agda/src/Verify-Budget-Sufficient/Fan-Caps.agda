-- THE FAN-OUT ALLOWANCES AND THE CAPS A DELIVERY IS PRICED AGAINST.
-- These are functions of the caps and a dispatch gas ALONE -- no path,
-- no store, no measure -- which is why they sit below the measures
-- tower rather than beside the delivery measures that spend them: the
-- instant's own budget is stated in them, and the budget is defined
-- before any path is measured.
--
-- ONE LEVEL admits at most `cReg` chains; each contributes its own
-- caps-priced charge (a length's worth of frames, or a cap-squared's
-- worth of size or depth) plus whatever the next level's sinks may
-- spend.  `fanSq` serves both the size-sum and the depth currencies,
-- whose per-path budgets coincide.  The `suc` sits INSIDE the length
-- product deliberately: a fold summing one `suc` per admitted path
-- does not fit under `cReg * (cSize + fanLen g)`, and does fit under
-- this, which is what lets the telescope survive with no length factor.
module Verify-Budget-Sufficient.Fan-Caps where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m;
   +-mono-≤; +-monoʳ-≤; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
   *-assoc; *-identityˡ; *-distribʳ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Verify-Budget-Sufficient.Caps using (Caps)

-- SEALED, and this is not optional: these bodies reach a RECURRENCE,
-- and the quantities they define sit inside the instant's budget --
-- which is a PREMISE of every statement the walk and the cascade are
-- stated over.  Transparent, one unfolding of the budget drags the
-- whole fan recurrence into every one of those call sites; the module
-- that consumes the budget last went from a dev check well inside the
-- loop's budget to one the budget KILLED, twice, and came back the
-- moment the seal went on.  Consumers need the recurrence's two
-- base cases and the square's shape, and those are exported as
-- equations proven in here rather than as a transparent body.
abstract
  fanLen : ℕ → Caps → ℕ
  fanLen zero    c = 0
  fanLen (suc g) c = Caps.cReg c * suc (Caps.cSize c + fanLen g c)

  fanSq : ℕ → Caps → ℕ
  fanSq zero    c = 0
  fanSq (suc g) c = Caps.cReg c * (Caps.cSize c * Caps.cSize c + fanSq g c)



  -- THE TWO CAPS A DELIVERY IS PRICED AGAINST, which are the path caps
  -- plus one fan allowance each.  A consumer that used to read the size
  -- cap off `Caps` reads one of these instead, and the whole content of
  -- the sink-aware currency is that the difference is not zero: a share
  -- sink hands its value to every admitted registration, and the path
  -- measures charge that nothing at all.
  delSize : ℕ → Caps → ℕ
  delSize g c = Caps.cSize c + fanLen g c

  delSq : ℕ → Caps → ℕ
  delSq g c = delSize g c * delSize g c

  -- AND THE SQUARE COVERS BOTH SUMMANDS IT REPLACES, which is the one
  -- arithmetic fact the exponent side needs and the reason the delivery
  -- caps are a cap and a SQUARE rather than two independent riders.  The
  -- depth recurrence lives under the length recurrence's square because
  -- each level of the fan multiplies where the length merely adds -- so
  -- a registry that admits at least one entry cannot make the depth
  -- currency outrun the length currency's square.
  sq-split : ∀ x y → x * x + y * y ≤ (x + y) * (x + y)
  sq-split x y =
    ≤-trans (+-mono-≤ (*-monoʳ-≤ x (m≤m+n x y)) (*-monoʳ-≤ y (m≤n+m y x)))
            (≤-reflexive (sym (*-distribʳ-+ (x + y) x y)))

  fanSq≤fanLen² : (g : ℕ) (c : Caps) → 1 ≤ Caps.cReg c →
    fanSq g c ≤ fanLen g c * fanLen g c
  fanSq≤fanLen² zero    c 1≤R = z≤n
  fanSq≤fanLen² (suc g) c 1≤R =
    ≤-trans (*-monoʳ-≤ (Caps.cReg c)
              (≤-trans (+-monoʳ-≤ (Caps.cSize c * Caps.cSize c) (fanSq≤fanLen² g c 1≤R))
                       (≤-trans (sq-split (Caps.cSize c) (fanLen g c))
                                (*-mono-≤ (n≤1+n (Caps.cSize c + fanLen g c))
                                          (n≤1+n (Caps.cSize c + fanLen g c))))))
            grow
    where
    Z : ℕ
    Z = suc (Caps.cSize c + fanLen g c)

    grow : Caps.cReg c * (Z * Z) ≤ (Caps.cReg c * Z) * (Caps.cReg c * Z)
    grow = ≤-trans (*-monoʳ-≤ (Caps.cReg c)
                     (*-monoʳ-≤ Z (≤-trans (≤-reflexive (sym (*-identityˡ Z)))
                                           (*-monoˡ-≤ Z 1≤R))))
                   (≤-reflexive (sym (*-assoc (Caps.cReg c) Z (Caps.cReg c * Z))))

  delSize-cap : (g : ℕ) (c : Caps) → Caps.cSize c ≤ delSize g c
  delSize-cap g c = m≤m+n (Caps.cSize c) (fanLen g c)

  delSq-cap : (g : ℕ) (c : Caps) → 1 ≤ Caps.cReg c →
    Caps.cSize c * Caps.cSize c + fanSq g c ≤ delSq g c
  delSq-cap g c 1≤R =
    ≤-trans (+-monoʳ-≤ (Caps.cSize c * Caps.cSize c) (fanSq≤fanLen² g c 1≤R))
            (sq-split (Caps.cSize c) (fanLen g c))

  cSize≤delSq : (g : ℕ) (c : Caps) → 1 ≤ Caps.cSize c → Caps.cSize c ≤ delSq g c
  cSize≤delSq g c 1≤S =
    ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (Caps.cSize c))))
                     (*-monoˡ-≤ (Caps.cSize c) 1≤S))
            (*-mono-≤ (delSize-cap g c) (delSize-cap g c))

  fanLen-zero : (c : Caps) → fanLen zero c ≡ 0
  fanLen-zero c = refl

  fanLen-suc : (g : ℕ) (c : Caps) →
    fanLen (suc g) c ≡ Caps.cReg c * suc (Caps.cSize c + fanLen g c)
  fanLen-suc g c = refl

  fanSq-suc : (g : ℕ) (c : Caps) →
    fanSq (suc g) c ≡ Caps.cReg c * (Caps.cSize c * Caps.cSize c + fanSq g c)
  fanSq-suc g c = refl

  fanSq-zero : (c : Caps) → fanSq zero c ≡ 0
  fanSq-zero c = refl

  delSq-def : (g : ℕ) (c : Caps) → delSq g c ≡ delSize g c * delSize g c
  delSq-def g c = refl

  delSize-def : (g : ℕ) (c : Caps) → delSize g c ≡ Caps.cSize c + fanLen g c
  delSize-def g c = refl

