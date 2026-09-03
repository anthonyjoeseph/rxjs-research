-- Seven receipts on one target is the boundary and is LEGAL: a coverage
-- lattice over one statement is what the cap leaves room for.
-- TARGET: live-one @b6f6f3
module CapAt1 where
row : Confirms (live-one 1)
row = refl
