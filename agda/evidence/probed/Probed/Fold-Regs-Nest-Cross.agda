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

-- one height above the crossover: the walked path is longer than the
-- nesting frame's syntax, so the caps track the spine rather than the
-- frame
n3 : Closed Γ₃ natᵗ
n3 = prog 2 13

cross : rowOf n3 ≡ 31401515
cross = refl
