-- FIXTURE for `make imports-selftest`: the module the PHANTOM rows import
-- from.  It has to be a real file in this tree, because the check can only ask
-- "does M's own text contain this name?" of an M it can read.  Every
-- `Fixture.*` module named in this tree names no file and is skipped
-- wholesale, which is what the exact phantom count pins: were the check to
-- guess at a module it cannot read, every one of those would fire.
module Phantom-Src where

-- `hidden` appears in THIS declaration and nowhere else in the file, so
-- Phantom-Src does not export it -- a `public` re-export would, and those are
-- illegal.  So the check must excise import declarations before reading a
-- module's tokens; a whole-file read calls `hidden` exported and misses the
-- row.  The `renaming` is what keeps the row honest: it puts this declaration
-- outside the USE check, so `hidden` earns no dead-import finding and the
-- phantom row in Phantom.agda is the only thing that can fire on it.
--
-- AND `borrowed` IS THE SAME NAME SPENT, which is what the token reading is
-- blind to and the shape that actually reached CI.  `hidden` fires either way
-- -- excised from the tokens, it is also absent from them -- so it cannot pin
-- the arm that asks whether this module IMPORTS the name.  A name used in the
-- body is a body token, so the token reading calls it exported and only that
-- arm is left; mutate the arm away and this row is the one that goes quiet.
open import Fixture.Deep using (hidden; borrowed) renaming (deep to shallow)

real-thing : Set
real-thing = Set

spends-it : Set
spends-it = borrowed

module Sub-Mod where
  inner : Set
  inner = Set
