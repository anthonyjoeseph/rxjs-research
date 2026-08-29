-- ══════════════════════════════════════════════════════════════════
-- THE FRAME STEP DOES NOT COMPOSE, so a level cannot be absorbed into
-- the cap the frame machinery is re-entered at.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  A walk's caps facts arrive at a STEPPED cap
-- while the receipt that consumes them is stated at a bare one, so the
-- cheap repair is to re-enter the frame result with its cap parameter
-- instantiated at the stepped cap and read the answer back against the
-- level the two together should make.  That costs no restatement at
-- all: one instantiation and one ordering.
--
-- WHY IT CANNOT WORK.  The step is not additive in its count.  Its
-- width component ITERATES an exponential whose BASE is the size
-- component, and stepping raises the size, so a second step taken at
-- the stepped cap runs its exponential at the RAISED base -- one tower
-- storey per level, against a flat count that runs every iteration at
-- the original.  At the smallest cap this development admits, one level
-- either side already puts the composed width five orders of magnitude
-- over the flat one, and two levels puts it past four thousand digits.
--
-- SO THE LEVEL HAS TO BE THREADED, which is what the frame face beside
-- this one already does: it takes the invariant at the stepped cap,
-- reports its own increment, and restates at the SUM.  Re-entering at a
-- stepped cap is the shortcut that avoids that discipline, and this is
-- the arithmetic that refuses it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Compose where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-refl)
open import Data.Product using (proj₁)

open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep; _⊑ᶜ_)

-- the smallest cap this development admits: two size, one width, one
-- registry.  Nothing about the counterexample needs a larger one --
-- the gap is already five orders of magnitude on the width here.
c₀ : Caps
c₀ = caps 2 1 1

-- STATED WITH THE SIDE CONDITION THE REAL LEMMA WOULD CARRY, so the
-- refutation reaches the conditioned form and not merely the bare one.
FrameStepCompose : Set
FrameStepCompose = ∀ (c : Caps) (Lv j : ℕ) → 2 ≤ Caps.cSize c →
  frameStep j (frameStep Lv c) ⊑ᶜ frameStep (Lv + j) c

-- ONE LEVEL EITHER SIDE IS ENOUGH: the composed size is 210 where the
-- flat one is 42, so the ordering's first component is already false.
frameStep-compose-absurd : FrameStepCompose → ⊥
frameStep-compose-absurd pr = ≤⇒≤ᵇ (proj₁ (pr c₀ 1 1 ≤-refl))
