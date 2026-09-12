module RefOk where

-- WHAT THIS LEAF OWES.  Every reference below resolves, and each is written
-- BACKTICKED or DOTTED, which is what makes it read as a reference at all.
--
-- REFUTED: the unconditional form is killed at git show 919f115 — the sha
--   form, which is what a marker carries once `src` can no longer STATE the
--   route and the witness has correctly been deleted.
-- TWIN: `≺-wellFounded` is the proven counterpart whose clauses correspond one
--   for one, and `rootWitness` is the staging half of the same argument.
-- RECOVERY: git show 2984f1e575d8699e8ce78975e23c530d803fc911 restores the predecessor and its whole cone.
postulate leaf : Set
