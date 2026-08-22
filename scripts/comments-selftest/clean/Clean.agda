module Clean where

-- WHAT THIS LEAF OWES.  The bound is over the staged environment, so the
-- arithmetic is a telescope rather than a fold.
--
-- SEALED, and this is not optional: the row is consumed transitively by the
-- spine, so unsealing it costs three multi-hour rebuilds.  Undated, and a
-- durable rationale rather than a record of when the seal went on -- which is
-- exactly why SEALED is off the historical-marker list.
--
--   ASSEMBLED here reads as a continuation, indented, and must not fire.
--   MEASURED likewise.
--
-- REFUTED: `Refuted.Depth-Hop.depth-hop-∀V-absurd` kills the ∀ V form at V = 0.
-- PROBED: every clause of the currency, both `Slot` constructors, all four
--   `*All`s -- nine rows with no margin.  Not reached: a state deep in a
--   cascade, and the `caseᵗ` clause.
-- RECOVERY: git show 853c49e7ca7d24 restores the width walk and its cone.
------------------------------------------------------------------
postulate leaf : Set

-- AND A NUMERAL IS NOT A CITATION.  The refold bound is V = 4, twenty
-- units of gas suffice, the depth came out 21 against 20, and the row at
-- line 2 of the series is degenerate -- none of which addresses a reader
-- to a position in a file, so the sixth check must stay silent here.
postulate numerals : Set

-- AND A SIGNAL IS NOT A LINE NUMBER EITHER.  Two Killed:9 builds is a
-- reaper's exit status, and Bug:14 names no module this tree declares --
-- so the prefix is required to be a real module basename, which is what
-- keeps the sixth check from being a rule people route around.
postulate signals : Set
