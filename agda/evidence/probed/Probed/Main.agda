-- THE PROBE ROOT.  `make probed` checks this module, and `make wiring-probed`
-- holds every file in this tree to having a route home from here — the same
-- law `src/Main.agda` carries, and the reason the probes no longer need a
-- MODULE_ROOTS entry each.
--
-- WHY THAT MATTERS AND IS NOT BOOKKEEPING.  A MODULE_ROOTS entry is a
-- reachability SEED inside the PROOF's own scan: it declares "start here too",
-- so the probe and everything under it counted as wired while nothing in the
-- proof consumed any of it.  That is how a probe came to look reachable from
-- Main when Main could not reach it and `make gate-heavy` never compiled it.  A
-- root-based claim cannot self-certify; a name-based exemption always can.
--
-- A probe module is normally held up ENTIRELY BY ITS PINS — a wall of
-- anonymous `_ : lhs ≡ rhs` rows, each checked by the typechecker and named by
-- nobody — so `using ()` is the correct and expected clause here.  It is not
-- an omission: it says this module's content is its pins.  See EVIDENCE.md.
--
-- What is worth recovering from the fifty-one expired files is the
-- HARNESS rather than any verdict — the real-evaluator plumbing, the
-- program families, and the coverage boundaries recorded at the foot of
-- several of them — since a green on a bound this development no longer
-- states says nothing about the descent that replaced it.
--
-- RECOVERY: git show 3abdafa1:agda/evidence/probed/Probed/Stuck-Branches.agda
--   holds the harness that built a flattener's hop by hand from the
--   relation's constructors, which a probe of a flattener arm wants back.
-- RECOVERY: git show 919f115:agda/evidence/probed/Probed/
-- RECOVERY: git show 3a3bd405:agda/evidence/probed/Probed/Connect-Count.agda
-- RECOVERY: git show 15e6c229:agda/evidence/probed/Probed/MergeMap-Empty.agda
--   and `.../Share-Channel.agda` hold real-evaluator harnesses -- a
--   slot-free root at `Ctx 0`, and a five-way share reading -- but each
--   instantiates a DEFINITION rather than a live statement, so neither
--   could declare a target.  The harnesses are what is worth recovering.
module Probed.Main where

-- THE APPARATUS IS CLAIMED FROM THE ROOT rather than from whichever
-- file happens to spend it: E7 refuses a `-- TARGET:` with no `Confirms`
-- row and E6 refuses a `-- FORK:` that does not inhabit `Separates`, so
-- both belong to the tree and a tree with nothing open still owes them.
open import Probed.Apparatus using (Confirms; Separates)
open import Probed.Left-To-Right using ()
open import Probed.Timing-Correct using ()
open import Probed.Timed-Faithful using ()
open import Probed.Batchable using ()
open import Probed.Opening using ()
open import Probed.Map-Step using ()
open import Probed.Unfold using ()
open import Probed.Walk-Leaves using ()
