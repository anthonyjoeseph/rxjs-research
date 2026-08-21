-- FIXTURE for `make imports-selftest`.  Every import here is named for the
-- verdict it must get; the selftest asserts BOTH directions, because a checker
-- that fires on everything and a checker that fires on nothing both go green
-- against a fixture that only tests one of them.
--
-- The one below is the shape that motivated the whole checker: the name appears
-- in this comment and nowhere else, so a checker that forgets to strip comments
-- calls dead-in-comment-only USED and misses it.
module Fires where

open import Fixture.Plain using (dead-plain)
open import Fixture.Doc using (dead-in-comment-only)
open import Fixture.Wide using (dead-wide-a; dead-wide-b;
                               dead-wide-c)
open import Fixture.Live using (live-used; dead-beside-live)
open import Fixture.Token using (T)

-- THE BLANKET ROWS.  Neither has a `using` list, so each takes every name its
-- module has and this file's real dependencies are written down nowhere.  Both
-- must be reported BLANKET and neither DEAD: the use check cannot decide them
-- (it has no export list to compare against), which is exactly why a separate
-- rule is needed rather than a smarter use check.  A bare `renaming` is blanket
-- too -- it takes everything and respells some of it.  The `public` counterpart
-- is NOT, and lives in Quiet.agda.
open import Fixture.Bare
open import Fixture.BareRenaming renaming (there to here)

-- THE RE-EXPORT ROWS.  `public` is illegal outright (Anthony): it makes names
-- reachable from a module that did not define them, so every consumer downstream
-- depends on a fact written down nowhere in its own file.  BOTH must fire -- the
-- named one too, because naming what you re-export does not tell a consumer
-- where the name came from.  `Fixture.BarePublic` earns two findings, RE-EXPORT
-- and BLANKET, since it also names nothing.
open import Fixture.Reexport using (unused-but-public) public
open import Fixture.BarePublic public

-- `dead-in-comment-only` is discussed here and used nowhere.

alive : Set
alive = live-used T-rue
