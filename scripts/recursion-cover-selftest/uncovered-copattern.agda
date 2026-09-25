-- a cycle closed only through a copattern clause: `walkRP`'s body is
-- written as `fold (walkRP ...) = ...`, so read by its head token it
-- belongs to the field and the edge back to `walk` is invisible.

walk : Set
walkRP : Set

walk = walkRP
fold (walkRP x) = walk
