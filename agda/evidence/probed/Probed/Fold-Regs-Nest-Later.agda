-- THE SPINE AT AN ARRIVAL THAT IS NOT THE FIRST.  Every row taken
-- over this family so far reads the door at its easiest moment: the
-- harness takes `sched-next` once, so the state the reading is made
-- against is the one the subscribe left behind, with the registry as
-- short as it will ever be and no chain having yet run.  That is the
-- cheapest arrival to instantiate and the least informative, because
-- the quantity in question is a maximum over the registry's paths and
-- the registry is what a delivery lengthens.

-- WHY A LATER ARRIVAL COULD SAY SOMETHING THE FIRST CANNOT.  The exit
-- column is read off the registry the fold leaves, and the entry
-- column off the registry it was handed.  At the first arrival those
-- two are separated by one cascade over a registry the subscribe
-- built; at the second they are separated by one cascade over a
-- registry a cascade has already grown.  If the frame step is the
-- right currency the separation is stable in the arrival; if it is
-- not, the gap opens exactly here, and no amount of height at the
-- first arrival would show it.

-- WHAT THE SCRIPT SUPPLIES.  The outer slot carries three emissions,
-- so the second and third arrivals exist without touching the
-- harness's program family or its caps -- the rows stay comparable to
-- the ones already taken, which is the whole reason for reusing the
-- reading rather than writing a second one.

-- WHAT WOULD REFUTE, AND WHAT WOULD NOT.  The verdict digit alone.
-- The three maxima are pinned so that a repair moving either cap
-- fails here naming the number, but a maximum that grew with the
-- arrival is not itself a finding: the reading asks whether the exit
-- fits ONE frame step of the two caps in hand, and all three columns
-- are free to climb together. A stage digit below three says the run
-- never reached the door and the row is evidence about nothing.

-- WHAT IS NOT COVERED.  One height, below the crossover, and one
-- program family.  The rows say the entry cap reaches a fixed point
-- of the delivery and that the exit does not follow it up; they say
-- nothing about a height at which the walked path outgrows the
-- frame's syntax, which is where the sibling above the crossover
-- reads and where a delivery cuts the longer of the two columns.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Nest-Later where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Evaluator using (Sched; EvalSt; sched-next; cascade)
open import Probed.Fold-Regs-Nest-Spine using (Γ₃; prog; sub; read; pack)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

----------------------------------------------------------------------
-- ADVANCING THE DOOR.  One arrival consumed and its cascade run to
-- completion, which is what distinguishes this from the harness's own
-- reading: that one latches and folds without ever committing the
-- result, so it can be taken repeatedly at one arrival and never
-- reaches the next.  An exhausted schedule returns the state
-- unchanged, which the stage digit then reports as a one.
----------------------------------------------------------------------

step : {e : Closed Γ₃ natᵗ} → Sched Γ₃ × EvalSt e → Sched Γ₃ × EvalSt e
step (sd , st) with sched-next sd
... | inj₁ _       = sd , st
... | inj₂ (a , s) = let r = cascade a 1 s st
                     in proj₁ (proj₂ r) , proj₂ (proj₂ r)

----------------------------------------------------------------------
-- THE ROWS.  Held at the height the sibling grid reads below the
-- crossover, so the arrival is the only axis that moves and a
-- difference cannot be attributed to the program.
----------------------------------------------------------------------

n0 : Closed Γ₃ natᵗ
n0 = prog 2 6

-- the second arrival: one cascade has run, so the registry the fold
-- is handed is one delivery longer than any row taken so far
second : ℕ
second = pack (read n0 (step (sub n0)))

row-second : second ≡ 31191913
row-second = refl

-- and the third, which is what says the entry cap has SETTLED rather
-- than merely moved once
third : ℕ
third = pack (read n0 (step (step (sub n0))))

row-third : third ≡ 31191913
row-third = refl

----------------------------------------------------------------------
-- WHAT THE TWO ROWS SAY, READ BESIDE THE GRID'S AT THIS HEIGHT.  The
-- path cap and the exit hold across every arrival; the ENTRY cap
-- climbs once, from the value the first
-- arrival was handed to the value that arrival left, and then does
-- not move again.  So the fold's own registrations are standing in
-- the premise by the second arrival -- the state the reading is made
-- against is a fixed point of the delivery, not a state the subscribe
-- happens to have produced -- and the step is being spent against
-- something the run produced rather than against the shape.
--
-- AND THE SEPARATION IS WHAT SURVIVES.  The exit does not rise with
-- the entry, so the grant is not merely tracking its own hypothesis:
-- one frame step of the settled caps still clears the exit with room,
-- and it clears it at the arrival where the walked path has been cut
-- by a delivery, which is the reading no row on this leaf had.
----------------------------------------------------------------------

-- AND THE TIE TO THE STATEMENT, held at the point this family shares.
-- The rows above are the READING; `foldTie` is what holds them to
-- `foldPath-regsLen` as it now reads, so a restatement of the target
-- breaks here rather than leaving the reading green about text that is
-- gone.  What the point covers, and what it does not, is stated where
-- it is paid for: `Probed.Fold-Regs-Row`.
foldTie : Confirms
  (foldPath-regsLen {e = e₀} gp 3 1 0 0 pth vls evs₀ fin₀ sd₀ st₀ 1 2
     le1 le2 pv pp pr)
foldTie = foldRow
