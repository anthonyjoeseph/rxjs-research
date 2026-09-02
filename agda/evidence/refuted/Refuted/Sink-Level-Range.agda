-- ══════════════════════════════════════════════════════════════════
-- ONE SINK HOP ASKS FOR A LEVEL RANGE THE AFFORDABILITY ROUTE CANNOT
-- REACH, so the ledger cannot be repaired by widening the walked
-- side's budget.  The walk stands at a level and hands its values to
-- chains it finds in the REGISTRY; those chains are read at the level
-- the walk has reached, so one of them may be as long as the SIZE
-- bound at that level -- and the levels its own frames then consume
-- are that many.  The range the affordability is stated over is a cap
-- SQUARED plus a cap; the range one hop asks for is an exponential of
-- the cap.  They cross at the smallest cap the invariant admits.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID, and it is not a statement in `src`: it is
-- the arithmetic every repair on the walked side has to have.  A chain
-- legal at the level reading, entered at a level the affordability
-- covers, lands inside the same range.  Nothing weaker suffices --
-- the hop's conclusion is owed at the fanned-into chain's OWN frames,
-- so the ledger has to survive their count.
--
-- WHERE IT BREAKS.  A level multiplies the size by `S·(1+2s)`, so the
-- reading at one level above the floor is already the best part of two
-- hundred at a cap of eight, while the whole affordable range there is
-- seventy-two.  A single registered chain legal at that reading is
-- therefore twice the range on its own, before any nesting.  The gap
-- is not an artifact of the range's slack either: sharpening the
-- exponent to what the walk factor genuinely pays for buys a constant
-- factor, and the reading is an EXPONENTIAL of the level -- so the two
-- separate at every cap and diverge as the cap grows.
--
-- SO THE REPAIR IS NOT A NUMBER, AND IT IS NOT A LEDGER EITHER.  Two
-- ways out were available.  The walk's charge could climb to a tower
-- whose height is the dispatch gas, which is what nesting the hop
-- costs -- but this instant's fuel affords an exponential of the cap
-- and no exponent is a tower.  Or the registry's LENGTH ledger could
-- stop being read off its size ledger, so a fan-out adds levels
-- additively; the registry probes point that way, measuring registered
-- length flat across a step while the size conjunct grows.  What
-- closes it is which observable is registered: a subscribing frame
-- registers the value flowing down the PATH, not the arrival, so the
-- operator count it contributes is the derived value's -- and that is
-- the quantity the size ledger has been inflating all along.  A second
-- number tracks the first rather than escaping it.
--
-- WHAT IS OWED IS THEREFORE A MECHANISM.  The walk carries a receipt
-- about the path it is on and a sink spends it on paths it is not on;
-- every bridge tried has been one cap large enough to cover both, and
-- the crossing is what that costs.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Sink-Level-Range where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤⇒≤ᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; natᵗ)
open import Rx.Evaluator using (Path; root; _↠_; take-f; iterSize)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Refuted.Demand-Programs using (Γ₂)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
SinkRangeFits : Set
SinkRangeFits = ∀ {n} {Γ : Ctx n} (S j : ℕ) (p : Path Γ natᵗ natᵗ) →
  8 ≤ S →
  j ≤ S * S + S →
  pathSz? (iterSize S j S) p ≡ true →
  j + pathLen p ≤ S * S + S

-- a chain of plain relays, so every frame costs the size reading
-- nothing and only the LENGTH conjunct is under test
takes : ℕ → Path Γ₂ natᵗ natᵗ
takes zero    = root
takes (suc k) = take-f 0 ↠ takes k

-- the longest chain the reading one level above the floor admits
chain : Path Γ₂ natᵗ natᵗ
chain = takes 136

-- THE TWO QUANTITIES THAT CROSS.  The size reading at one level, which
-- is what the registry is priced by there …
reading≡ : iterSize 8 1 8 ≡ 136
reading≡ = refl

-- … and the whole range the affordability route is stated over
range≡ : 8 * 8 + 8 ≡ 72
range≡ = refl

len≡ : pathLen chain ≡ 136
len≡ = refl

-- BOTH PREMISES HOLD AT THE WITNESS, so what fails is the statement.
-- The cap is the smallest the caps invariant admits, and the entry
-- level is one -- the first level at which a fan-out is possible at all
8≤S : 8 ≤ 8
8≤S = ≤-refl

j≤range : 1 ≤ 8 * 8 + 8
j≤range = s≤s z≤n

legal : pathSz? (iterSize 8 1 8) chain ≡ true
legal = refl

-- and the conclusion is `137 ≤ 72`, whose boolean reading is `false`
sink-level-range-absurd : SinkRangeFits → ⊥
sink-level-range-absurd pr = ≤⇒≤ᵇ (pr {Γ = Γ₂} 8 1 chain 8≤S j≤range legal)
