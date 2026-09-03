-- THE SPINE ABOVE THE CROSSOVER.  Its sibling
-- `Probed.Fold-Regs-Nest-Grid` reads the nesting spine at heights
-- where both caps sit pinned at the nesting frame's own syntax while
-- the registered exit grows with the height -- the one stretch in
-- which the grant is momentarily constant in the height and a
-- crossing could hide.  The cap is a MAXIMUM over that syntax and the
-- walked path's length, so the stretch ends: past the height at which
-- the spine outgrows the frame, the cap rises with the height and the
-- grant, being quadratic in the caps, rises with its square while the
-- exit rises linearly.  This module is the row that says the stretch
-- does end, and it is a separate module because a program above the
-- crossover is a whole evaluation and the module holding the pinned
-- stretch is already paying for two.

-- WHAT WOULD REFUTE.  Only the exit column.  Raising either cap
-- enlarges `sizeStep S B` and weakens the premise it gates at the
-- same time, so no instantiation of a cap can produce a
-- counterexample and the row is read at each cap's own least.  The
-- height is the one measure-side axis here, which is why it is the
-- one being driven, and an exit outrunning one frame step at any
-- height is a witness against the restated leaf exactly as this
-- family was against the doubling.

-- WHICH ROW BEARS WEIGHT.  `cross` is LOAD-BEARING in all of its
-- digits.  The verdict digit is the reading and is a conjunction over
-- EVERY chain the arrival matches, so one long registration cannot
-- hide behind a short one listed first; the cap digits are what make
-- the margin legible and what would expose a least-budget search that
-- ran off its fuel; and the stage digit guards against reading any of
-- it over a run that never reached the door.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Nest-Cross where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)

open import Probed.Fold-Regs-Nest-Spine using (Γ₃; prog; rowOf)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

-- one height above the crossover: the walked path is longer than the
-- nesting frame's syntax, so the caps track the spine rather than the
-- frame
n3 : Closed Γ₃ natᵗ
n3 = prog 2 13

cross : rowOf n3 ≡ 31401515
cross = refl

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
