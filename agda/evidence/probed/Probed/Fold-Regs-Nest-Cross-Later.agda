-- THE SPINE ABOVE THE CROSSOVER, AT AN ARRIVAL THAT IS NOT THE FIRST.
-- Two rows of this family are read at right angles and neither one
-- reaches here.  `Probed.Fold-Regs-Nest-Cross` drives the HEIGHT past
-- the point where the walked path outgrows the nesting frame, so the
-- caps stop being pinned at the frame's syntax and start tracking the
-- spine -- but it reads the door once, against the registry the
-- subscribe left.  `Probed.Fold-Regs-Nest-Later` drives the ARRIVAL,
-- but at a height below the crossover, where both caps are pinned at
-- the frame's own syntax and a delivery therefore moves neither.

-- WHY THE CORNER IS THE ONE WORTH SPENDING A PROGRAM ON.  Above the
-- crossover the caps are driven by the SPINE, and a delivery is the
-- one event that cuts the spine.  So this is the single stretch in
-- which an arrival can LOWER the column the grant is quadratic in
-- while the exit it has to clear is linear in that same column and
-- was produced by a longer spine.  Everywhere else the two move
-- together or neither moves, which is why no row so far could have
-- seen it.

-- WHICH ROW BEARS WEIGHT, AND WHAT WOULD REFUTE.  Both rows are
-- LOAD-BEARING and by the verdict digit alone, exactly as in the two
-- siblings: the caps cannot refute by moving, since raising either
-- enlarges `sizeStep S B` and weakens the premise it gates at once.
-- A stage digit below three would say the run never reached the door
-- and the row is evidence about nothing rather than a red -- both
-- read three.

-- WHAT IS NOT COVERED, AND WHAT IT COSTS.  One height above the
-- crossover and one program family, and the arrivals are the outer
-- slot's three emissions, so a fourth is not available without moving
-- the harness the sibling rows share.  The price of the corner is the
-- reason not to reach further: it multiplies the crossover height
-- against a second cascade, so this module alone is several times the
-- whole rest of the probe tree, and `make probed` is a gate step
-- rather than a side loop.  A row past the third buys a repetition of
-- a fixed point these two already pin exactly.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Nest-Cross-Later where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Probed.Fold-Regs-Nest-Spine using (Γ₃; prog; sub; read; pack)
open import Probed.Fold-Regs-Nest-Later using (step)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

-- the sibling's height, so the arrival is the only axis that moves
n3 : Closed Γ₃ natᵗ
n3 = prog 2 13

-- the second arrival: one cascade has run over a spine the subscribe
-- built, so the registry the fold is handed is one delivery longer
-- and the walked path has been cut by that delivery
crossSecond : ℕ
crossSecond = pack (read n3 (step (sub n3)))

row-cross-second : crossSecond ≡ 31404015
row-cross-second = refl

-- and the third, which is what says the entry cap has SETTLED above
-- the crossover rather than merely moved once -- it reads IDENTICAL
-- to the second, every digit, so the fixed point is exact and not a
-- trend still running
crossThird : ℕ
crossThird = pack (read n3 (step (step (sub n3))))

row-cross-third : crossThird ≡ 31404015
row-cross-third = refl

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
