module LineRef where

-- WHAT THIS LEAF OWES.  Two citation forms, and both are what the sixth
-- check exists for: the path-and-colon one below, and the prose one.
-- The mirror is Wet.agda:4125, and the arithmetic it spends is at
-- line 1920 of the same file.
postulate leaf : Set

-- AND NOT THE EXTENSIONLESS FORM, WHICH CANNOT LIVE IN A STATIC FIXTURE.
-- That form fires only when the prefix is a module the real trees declare,
-- which is what keeps it precise -- and it is why a fixture writing one by
-- hand goes quietly dead the day that module is deleted, reporting a tidy
-- PASS for a check that has stopped being exercised.  It has happened once.
-- The recipe generates that fixture from a stem it reads off the tree.
postulate not-extensionless : Set

-- AND THE APPROXIMATE FORM, which is the near miss the two above walked
-- past: a tilde-number alone in its parentheses (~882).
-- A reader is sent to one directly (see below, ~6307).
-- And one counts ~1200 lines BELOW.
postulate approximate : Set
