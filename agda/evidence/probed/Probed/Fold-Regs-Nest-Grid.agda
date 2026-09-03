-- THE SPINE BELOW THE CROSSOVER, WHERE THE CAPS ARE PINNED AND ONLY
-- THE EXIT MOVES.  The family, the axis and what would refute are in
-- the harness these rows spend, `Probed.Fold-Regs-Nest-Spine`; the
-- stretch this module reads is the one in which the walked path is
-- still shorter than the nesting frame's own syntax, so both caps sit
-- held at that syntax while the registered exit climbs with the
-- height.  That is the only stretch in which a taller spine is not
-- answered by a larger grant, and so the only one in which a crossing
-- could hide.  Whether it ends is the sibling row,
-- `Probed.Fold-Regs-Nest-Cross`.

-- WHICH ROWS BEAR WEIGHT.  Both are LOAD-BEARING in the verdict
-- digit, which is the reading and is a conjunction over EVERY chain
-- the arrival matches rather than over the head of the registry's
-- list, so one long registration cannot hide behind a short one
-- listed first.  The cap digits are load-bearing too: a verdict that
-- passed on a least-budget search running off its fuel would show up
-- as a wrong number rather than a green, and the margins are only
-- legible against the caps that bought them.  The stage digit is
-- DEGENERATE and guards against reading either row over a run that
-- never got to the door.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Nest-Grid where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)

open import Probed.Fold-Regs-Nest-Spine using (Γ₃; prog; rowOf)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

n0 n1 : Closed Γ₃ natᵗ
n0 = prog 2 6
n1 = prog 2 10

row0 : rowOf n0 ≡ 31191313
row0 = refl

row1 : rowOf n1 ≡ 31311313
row1 = refl

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
