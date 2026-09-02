-- ══════════════════════════════════════════════════════════════════
-- THE ONLY CEILING THE DEVELOPMENT HAS ON THE NODE TABLE SITS ABOVE
-- THE BUDGET THE WALK RUNS ON, so the frame fits that reach past their
-- own values cannot be paid for by routing that ceiling down to them.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE ROUTE SAID.  Two frame fits ask for a number above one
-- entry of `EvalSt.nodes`, and the walk that reaches them reads no
-- store at all -- so the repair looked like routing rather than
-- invention: `nestOK?` is `storeNestMax` under `nestCapAt`, a sibling
-- on this same face already takes it as a premise, and every producer
-- therefore owes only what it owes already.  On that reading the whole
-- residue is ONE arithmetic fit, `nestCapAt` against `nestWalkAt` at
-- the same instant.
--
-- WHERE IT BREAKS.  The two are separate recurrences and the cap is
-- the faster one, at the same index rather than eventually.  One
-- instant multiplies the cap by `nestFacAt`, whose exponent is a
-- burst SQUARED times a register width times `delSq` of the caps at
-- the instant after -- and `delSize` dominates the size cap, so that
-- exponent is at least four times the walk's own, which is a cube of
-- the size cap and nothing else.  So one instant of the cap already
-- carries an exponential of the walk's whole exponent, while the walk
-- has only its second factor to answer with, and that factor is
-- linear in the size cap over a wrap sum the size cap itself bounds.
--
-- THE FLOORS ARE THE DEVELOPMENT'S OWN, which is what makes the
-- crossing a fact about the route rather than about a choice of
-- numbers: `2≤capsAt-size` and `1≤capsAt-reg` for the size and the
-- register width, `1≤nestBurstAt` for the burst, `delSize-cap` for the
-- deletion size, and `slotWrapSum≤size` for the wrap sum at a slot
-- vocabulary the cap covers.  The witness below is every one of them
-- at equality.
--
-- AND NO AXIS RESCUES IT, WHICH IS WHY ONE ROW SETTLES IT.  Raising
-- the deletion size, the burst, the register width or the previous
-- instant's cap moves the LEFT side alone; raising the size cap moves
-- both exponents, the left one four times as fast; and raising the
-- unit adds one to the right while multiplying the left, since the
-- previous cap is at least the unit.  Every direction the route could
-- be widened in widens the gap.
--
-- WHAT IS OWED INSTEAD.  Not a bigger ceiling and not a routed one: a
-- number denominated in what the walk affords.  The fits ask for the
-- depth of the ONE entry a frame names, which is a per-node fact, and
-- a global maximum over the table was only ever the nearest thing to
-- hand.  So the residue is a field on the invariant record -- a
-- ceiling every writer of a node establishes and every reader spends
-- -- and it has to be stated in the walk's currency rather than in the
-- caps face's, since this is the second ceiling in that currency to
-- cross the same budget.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Cap-Walk-Cross where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤⇒≤ᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Both currencies
-- are sealed and both read `capsAt`, which does not return at any
-- program, so the obligation is stated over the quantities the two
-- closed forms are built from and the floors each of those carries.
-- `prev` is the cap at the instant before, `dS` the deletion size at
-- the instant after, `B` the burst, `W` the register width, `C` the
-- size cap, `unit` the program's nesting unit and `wrap` its slot
-- wrap sum.
----------------------------------------------------------------------
CapUnderWalk : Set
CapUnderWalk = ∀ (C B W unit wrap prev dS : ℕ) →
  2 ≤ C →
  1 ≤ B →
  1 ≤ W →
  1 ≤ unit →
  unit ≤ prev →
  C ≤ dS →
  wrap ≤ C * (2 ^ C * C) →
  2 ^ (suc B * suc B * (suc dS * (W * (dS * dS)))) * prev
    ≤ 2 ^ suc (C * (C * C) + C * C) * (unit + C + C * wrap)

----------------------------------------------------------------------
-- THE WITNESS, AT EVERY FLOOR AT ONCE.  The size cap is the smallest
-- the caps invariant admits, the burst and the register width are
-- theirs, the deletion size is the size cap itself, and the wrap sum
-- is the largest the slot bound allows at that cap -- so the right
-- side is taken at its most generous and the left at its least.
----------------------------------------------------------------------

2≤C : 2 ≤ 2
2≤C = ≤-refl

1≤B : 1 ≤ 1
1≤B = ≤-refl

1≤W : 1 ≤ 1
1≤W = ≤-refl

1≤unit : 1 ≤ 1
1≤unit = ≤-refl

unit≤prev : 1 ≤ 1
unit≤prev = ≤-refl

C≤dS : 2 ≤ 2
C≤dS = ≤-refl

wrap≤bound : 16 ≤ 2 * (2 ^ 2 * 2)
wrap≤bound = ≤-refl

----------------------------------------------------------------------
-- THE TWO QUANTITIES THAT CROSS, pinned before the ordering is taken,
-- so a repair moving either side fails here naming the number rather
-- than turning the crossing into an equality.
----------------------------------------------------------------------

capSide : ℕ
capSide = 2 ^ (suc 1 * suc 1 * (suc 2 * (1 * (2 * 2)))) * 1

walkSide : ℕ
walkSide = 2 ^ suc (2 * (2 * 2) + 2 * 2) * (1 + 2 + 2 * 16)

capSide≡ : capSide ≡ 281474976710656
capSide≡ = refl

walkSide≡ : walkSide ≡ 286720
walkSide≡ = refl

cap-walk-cross-absurd : CapUnderWalk → ⊥
cap-walk-cross-absurd pr =
  ≤⇒≤ᵇ (pr 2 1 1 1 16 1 2 2≤C 1≤B 1≤W 1≤unit unit≤prev C≤dS wrap≤bound)
