module RefBad where

-- WHAT THIS LEAF OWES.  Every reference below names nothing.  None can
-- become valid by accident: a name nothing declares stays undeclared, a
-- sha of all f's is not an object, and no Makefile declares the target.
--
-- TWIN: `no-such-lemma-exists-anywhere` is claimed as the proven counterpart.
-- PROBED: make qc-no-such-sweep QC='1 10 3' swept the region.
-- RECOVERY: git show ffffffffff restores it.
postulate leaf : Set
