-- E5: the stamp resolves, and to a statement that has since been rewritten
-- under the same name -- which is the one shape E2 cannot see.
-- TARGET: live-one @000000
module Stale where
row : Confirms (live-one 3)
row = refl
