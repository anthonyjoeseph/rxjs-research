-- FIXTURE for the ORPHAN GUARD.  This file imports `Guard-Leaf` and never
-- spends the name, so it is a dead import by the letter of the rule -- but it
-- is also the ONLY route from the claim root to `Guard-Leaf`, so deleting it
-- would hide that module from the build entirely.  The checker must report it
-- as WIRING rather than DEAD, and `--fix` must leave the line untouched.
module Guard-Root where

open import Guard-Leaf using (leaf-thing)

root-anchor : Set
root-anchor = Set
