module RefBad where

-- WHAT THIS LEAF OWES.  Both references below name nothing.  Neither can
-- become valid by accident: a name nothing declares stays undeclared, and a
-- sha of all f's is not an object.
--
-- TWIN: `no-such-lemma-exists-anywhere` is claimed as the proven counterpart.
-- RECOVERY: git show ffffffffff restores it.
postulate leaf : Set
