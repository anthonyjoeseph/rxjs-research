-- Eight is one past the cap, and the eighth has not told anyone something
-- the seventh did not while the ledger row stays open.
-- TARGET: live-one @b6f6f3
module CapOver6 where
row : Confirms (live-one 6)
row = refl
