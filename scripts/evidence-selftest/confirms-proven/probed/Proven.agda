
-- THE SHAPE THE WHITELIST USED TO REFUSE, and refusing it is what made the
-- rule unsatisfiable: a conclusion this tower SEALS does not reduce at any
-- point, so no numeral can ever be taken against it and only a proven
-- weakening reaches the statement at all.  The row's type is still generated
-- from the target, and the body names nothing unproven.
-- TARGET: live-one @b6f6f3
-- TARGET: live-two @000000
module Proven where
row : Confirms (live-one 3)
row = ≤-trans (≤ᵇ⇒≤ _ _ tt) (m≤m+n _ _)
lifted : Confirms (proj₂ (live-two prog 0))
lifted = intro prog (≤ᵇ⇒≤ _ _ tt)
  where
  helper = tt
