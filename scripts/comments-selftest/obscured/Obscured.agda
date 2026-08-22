-- FIXTURE: a marker DOUBLED into the comment text.  `blocks` strips exactly
-- one `--`, so the word lands in the text rather than in marker position and
-- every other check here reads it as prose -- the ordering rule lets it stand
-- mid-block and the reference pass never validates the sha it names.  Three
-- were live in `agda/src` when this fixture was written.
module Obscured where

-- -- RECOVERY: git show 725296e:agda/src/Some/Thing.agda restores the kit.
-- and this flush-left line is what the ordering rule would have caught, had
-- it been able to see the marker above at all
postulate obscured-one : Set
