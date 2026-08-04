------------------------------------------------------------------
-- WHERE THE 35 MINUTES GOES.  A module that defines NOTHING and imports
-- exactly what .Subscribe-Face imports.
--
-- `agda --profile=definitions` on .Subscribe-Face reports a total of
-- 2,136,727 ms of which 2,120,924 ms — 99.3% — is "Miscellaneous".  Every
-- named definition in the file, all thirteen clique members and their
-- `where` bindings together, accounts for ~15.8 SECONDS.  So the module's
-- CONTENT is not what costs; something not attributed to any definition
-- is.
--
-- That rules out the obvious remedy before we spend a day on it: cutting
-- the module into smaller pieces cannot divide a cost that its
-- definitions are not paying, and if the cost is per-module import
-- overhead then splitting MULTIPLIES it — every new module deserialises
-- the same import graph again.
--
-- This probe separates the two candidates.  It has the same import block
-- as .Subscribe-Face and no definitions at all:
--
--   · if it checks in SECONDS, the cost is .Subscribe-Face's own
--     whole-module analyses — termination/coverage over the 13-member
--     SCC being the prime suspect, since a call-matrix composition over
--     hundreds of clauses is exactly the kind of work that is
--     attributed to no single definition
--   · if it takes MINUTES, the cost is importing .Caps-Face (6700+
--     lines) and friends, and the fix is the IMPORT GRAPH, not the
--     module's size
------------------------------------------------------------------
module Import-Cost-Probe where

open import Data.Nat using (ℕ; zero; suc)

open import Rx.Exp
open import Rx.Evaluator
open import Verify-Budget-Sufficient.Caps
open import Verify-Budget-Sufficient.Caps-Nest
open import Verify-Budget-Sufficient.Caps-Sadd
open import Verify-Budget-Sufficient.Caps-Chain
open import Verify-Budget-Sufficient.Caps-Face

-- one trivial definition, so the module is not empty
probe-nothing : ℕ
probe-nothing = zero
