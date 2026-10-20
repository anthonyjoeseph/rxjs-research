module RefBad where

-- WHAT THIS LEAF OWES.  The reference below names nothing, and cannot
-- become valid by accident: a sha of all f's is not an object.
--
-- RECOVERY: git show ffffffffff restores it.
postulate leaf : Set
