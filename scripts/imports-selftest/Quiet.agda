-- FIXTURE for `make imports-selftest`: nothing in this file may be reported.
module Quiet where

open import Fixture.Precise using () renaming (only to only-precise)
open import Fixture.Mixfix using (_∷_; _++_)
open import Fixture.Section using (_*_; _hop_via_onto_)
open import Fixture.Renamed using (old) renaming (old to new)
import Fixture.Qualified as Q
open import Fixture.Solver using (module Solver-Mod)

alive : Set
alive = (x ∷ xs) ++ ys

qualified-use : Set
qualified-use = Q.something

renamed-use : Set
renamed-use = new

-- `using () renaming (…)` is the MOST precise form there is -- it takes nothing
-- and names exactly what it respells -- so the blanket rule must never fire on
-- it.  A bare `renaming` with no `using` is the opposite and does fire; see
-- Fires.agda.  (A bare `open import` used to live in this file as a must-not-fire
-- row for the USE check, which still skips it as undecidable.  It moved to
-- Fires.agda when the blanket rule arrived: the use check skipping a declaration
-- no longer means nothing reports it.)
precise-use : Set
precise-use = only-precise

-- A MODULE is imported as `module M`, and the name it binds is `M` -- so the
-- keyword must come off before the use search.  It did not, and every such
-- import read as dead: no token can equal `module M`, and the use that pays
-- for it is a module application (`open M ...`), which is not an import
-- declaration and so was never looked at.  `make imports-fix` deleted 18 of
-- these and broke the build.
open Solver-Mod using (solve)

module-use : Set
module-use = solve

-- A MIXFIX SPENT AS A SECTION.  `_` does not separate Agda tokens, so a
-- section is ONE token carrying the underscores -- `*_`, not `*` -- and an
-- atom-equality test over raw tokens calls `_*_` unused while this file
-- multiplies right here.  That is the checker's worst failure mode: a false
-- positive deletes a live import, and the build dies far from the edit with
-- `NoParseForApplication ... Operators used in the grammar: None`, naming the
-- USE and never the deleted import.  It cost 507 live names in one --fix run.
-- The multi-hole row is the one that decides the repair: splitting the TOKEN
-- on `_` handles `hop_via_onto_`, while stripping the underscores out of it
-- does not.  Its holes are named to collide with NOTHING -- an earlier
-- spelling used `at_from_as_`, and the atom `as` matched the `as` keyword that
-- `import M as Q` leaves in the body, so the row passed against a checker that
-- could not see it.  A row that cannot fail is not a row.
section-use : Set
section-use = cong (two *_) (x hop_via_onto_)
