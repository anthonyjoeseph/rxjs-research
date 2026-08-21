-- FIXTURE for the JOINT orphan guard, half one.  Together with Guard-Two-B
-- this is the case a per-edge guard gets WRONG: each of the two unused imports
-- of `Guard-Shared` is individually redundant, because deleting either leaves
-- the other reaching it.  Delete BOTH -- which is exactly what `--fix` does --
-- and the module is orphaned.  Both must be held back as WIRING findings.
module Guard-Two-A where

open import Guard-Shared using (shared-thing)

two-a-anchor : Set
two-a-anchor = Set
