-- The consolidation dodge: four targets in one file.  Merging probe files
-- is the cheap repair that satisfies a file count and changes nothing, so
-- the cap is over DECLARATIONS and this still fires.
-- TARGET: live-one @b6f6f3
-- TARGET: live-one @b6f6f3
-- TARGET: live-one @b6f6f3
-- TARGET: live-one @b6f6f3
module CapConsA where
row : Confirms (live-one 1)
row = refl
