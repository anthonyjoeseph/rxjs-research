-- FIXTURE for `make imports-selftest`: nothing in this file may be reported.
module Quiet where

open import Fixture.Precise using () renaming (only to only-precise)
open import Fixture.Mixfix using (_∷_; _++_)
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
