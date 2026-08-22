-- FIXTURE: two receipts a strict pattern walks straight past, and this is the
-- half of E3 that is not about tense at all.  A near miss must be REPORTED,
-- because the alternative is a check that counts zero and reads as tidy --
-- which is exactly how the date requirement rotted after `comments-check`
-- outlawed dates in source comments.
module NearMiss where

-- -- PROBED: an OBSCURED marker.  The doubled dash puts the word inside the
-- comment TEXT, so every checker in this repo reads it as prose -- including
-- the ordering rule that would otherwise force it to the end of its block.
postulate live-one : Set

-- PROBED (Probed.Root, `make probed`) with no colon at all, the marker
-- trailing a parenthetical instead
postulate live-two : Set
