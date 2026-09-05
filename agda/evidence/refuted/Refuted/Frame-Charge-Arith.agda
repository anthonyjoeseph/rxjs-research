-- ══════════════════════════════════════════════════════════════════
-- ONE FRAME'S ALLOWANCE ALREADY EXCEEDS THE LEDGER'S PER-FRAME
-- CHARGE, SO NO COUNT REPAIRS THE CHAIN DOOR.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  The cascade's position ledger buys one
-- `frameCh` at the entry cap per frame of a chain, and the record the
-- delivery walk is stated over bounds a frame's LANDING LEVEL by one
-- refreshed per-frame rung and by nothing else.  For the ledger's
-- charge to be sourced at all, that rung has to sit under it.  Both
-- sides are closed functions of the cap, the width and the level, so
-- the question is decidable as arithmetic and needs no program.
--
-- WHERE IT BREAKS, AND IT IS NOT AT THE ENTRY.  At level zero the rung
-- does fit: the charge is quadratic in the cap and the rung reads the
-- cap once.  ONE LEVEL IN it reads a fold TOWER and a geometric size
-- where the charge reads neither, and the two cross immediately -- at
-- the floor the caps package forces, a rung of 8907 against a charge
-- of 72.  So the gap is not in how many frames a chain is charged for:
-- a chain of ONE frame is already over.
--
-- AND NO CAP REPAIRS IT, which is what makes this a statement about the
-- ledger rather than about a chosen cap.  The charge grows with the
-- SQUARE of the cap and the rung with a tower in it, so raising the cap
-- widens the gap rather than closing it: at 64 the charge buys 4160 and
-- the rung reads over thirty-three million.
--
-- AND IT HOLDS AT EVERY DEPTH FUEL, by a PROVEN lower bound rather than
-- by taking the fuel at the value that happens to compute.  `fLvl≤fLvlD`
-- puts the refreshed rung above the frame's own receipt at every fuel,
-- and the receipt alone is already past the charge -- so the row says
-- nothing about which fuel a run reaches.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Charge-Arith where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤; ≤-trans)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Evaluator using (fLvl; fLvlD; widAt; sizeAt)
open import Verify-Budget-Sufficient.Caps using (fLvl≤fLvlD)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (frameCh)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  It is the sourcing
-- obligation the cascade's ledger puts on the walk record: the one
-- per-frame bound the record carries, held under the one per-frame
-- charge the ledger buys.  The level is taken away from the entry,
-- which is where the ledger spends every frame after the first.
----------------------------------------------------------------------
FrameChargeFits : Set
FrameChargeFits = ∀ (S W d J : ℕ) → 8 ≤ S → 1 ≤ W → 1 ≤ J →
  fLvlD S W d J ≤ J + frameCh S S

----------------------------------------------------------------------
-- THE FIGURES THE FIRST ROW TURNS ON, at the cap floor and a width of
-- one: the level's size reading, its fold reading, the frame receipt
-- those two buy, and what the ledger hands one frame.
----------------------------------------------------------------------
figures : List ℕ
figures = sizeAt 8 1 ∷ widAt 8 1 1 ∷ fLvl 8 1 1 ∷ frameCh 8 8 ∷ []

figures≡ : figures ≡ 136 ∷ 64 ∷ 8907 ∷ 72 ∷ []
figures≡ = refl

-- LOAD-BEARING: the receipt is over the charge by two orders, and the
-- crossing is decided by COMPUTATION on both sides -- the ladder never
-- has to normalise, since the proven lower bound is what carries the
-- fuel.  It would be satisfiable at `J = 0`, where the fold reading is
-- the bare width and the size reading the bare cap.
frame-charge-absurd : FrameChargeFits → (d : ℕ) → ⊥
frame-charge-absurd pr d =
  ≤⇒≤ᵇ (≤-trans (fLvl≤fLvlD 8 1 d 1)
                (pr 8 1 d 1 (≤ᵇ⇒≤ 8 8 tt) (s≤s z≤n) (s≤s z≤n)))

----------------------------------------------------------------------
-- AND THE GAP OPENS WITH THE CAP, which is the row that makes the
-- first one a statement about the ledger.  Eight times the cap buys
-- the charge sixty-four times as much and the receipt nearly four
-- thousand times as much, so there is no threshold above which the
-- product catches up.
----------------------------------------------------------------------
figuresWide : List ℕ
figuresWide = sizeAt 64 1 ∷ widAt 64 1 1 ∷ fLvl 64 1 1 ∷ frameCh 64 64 ∷ []

figuresWide≡ : figuresWide ≡ 8256 ∷ 4096 ∷ 33828931 ∷ 4160 ∷ []
figuresWide≡ = refl

-- LOAD-BEARING: it is the RATIO that carries the claim, and the ratio
-- moved from 123 to 8130 across one octave of the cap.  It would fail
-- to say anything new if the two figures had grown together.
frame-charge-wide-absurd : FrameChargeFits → (d : ℕ) → ⊥
frame-charge-wide-absurd pr d =
  ≤⇒≤ᵇ (≤-trans (fLvl≤fLvlD 64 1 d 1)
                (pr 64 1 d 1 (≤ᵇ⇒≤ 8 64 tt) (s≤s z≤n) (s≤s z≤n)))

----------------------------------------------------------------------
-- WHAT THIS DOES NOT SHOW.  The rung is an UPPER bound on where a
-- frame lands, so what is refuted is that the record SOURCES the
-- charge, not that a real frame climbs past it.  Four of the five
-- frame kinds land far under the rung and are priced by the charge
-- already; the fifth SUBSCRIBES, and the evaluator's own budget states
-- outright that no closed form in the cap, the width and the level
-- closes the loop between a frame and the subscribes it runs.  So the
-- residue this row leaves is not a gap in the arithmetic but the
-- mechanism question recorded at `chain-walk-szOK`.
----------------------------------------------------------------------
