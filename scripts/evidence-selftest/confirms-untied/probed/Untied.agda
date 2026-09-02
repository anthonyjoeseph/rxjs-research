-- E7's second: the term under `Confirms` is a function OVER the target, and
-- a function returns whatever type it likes -- the tie is gone.
-- TARGET: live-one @b6f6f3
module Untied where
row : Confirms (weaken (live-one 3))
row = refl
