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
-- WHY THE TREE IS EMPTY.  A probe expires with its target, and every
-- statement this tree was written against was a reading of a MEASURE —
-- a budget's grant, a frame's carried figure, a depth read off the
-- program text.  None of them is stateable now, so the rows would be
-- evidence about a machine that is gone and E2 expires every one of
-- them.  What replaced the measure has not been instantiated at
-- anything yet, which is the single largest unmanaged risk in the
-- repo and the next thing this tree is for.
--
-- AND TWO FURTHER GENERATIONS EXPIRED THE SAME WAY, WHICH IS WHAT SAYS
-- THE MECHANISM IS THE RIGHT ONE RATHER THAN AN OVERHEAD.  Six files
-- were written against a drain premise that READ a registry against the
-- program, and that reading is refuted in every form it was tried; nine
-- more instantiated the CARRIED bound a frame was held to, and the whole
-- apparatus of a carried figure went when the descent stopped being
-- ordered by a syntactic seed.  Every one of those rows was green to the
-- last day and said nothing about the statement that replaced it — which
-- is exactly the silent death E2 exists to make loud.
--
-- What is worth recovering from the fifty-one expired files is the
-- HARNESS rather than any verdict — the real-evaluator plumbing, the
-- program families, and the coverage boundaries recorded at the foot of
-- several of them — since a green on a bound this development no longer
-- states says nothing about the descent that replaced it.
--
-- RECOVERY: git show 919f115:agda/evidence/probed/Probed/
-- RECOVERY: git show 3a3bd405:agda/evidence/probed/Probed/Connect-Count.agda
module Probed.Main where

-- THE APPARATUS IS CLAIMED FROM THE ROOT rather than from whichever
-- file happens to spend it: E7 refuses a `-- TARGET:` with no `Confirms`
-- row and E6 refuses a `-- FORK:` that does not inhabit `Separates`, so
-- both belong to the tree and a tree with nothing open still owes them.
open import Probed.Apparatus using (Confirms; Separates)

-- THE REMAINING LEAVES OF THE REDUCIBILITY BODY.  Every row is NAMED
-- and claimed here rather than pinned anonymously: a `Confirms` row's
-- type is generated from its target, so the name is the only handle the
-- reachability law has on it.
open import Probed.Reducible-Arms using
  (row-live-merge; row-live-queue; row-live-switch; row-live-exhaust)

-- THE SUBSTITUTION LEAVES THE CARRIED ENVIRONMENT COSTS.  Claimed
-- from the root for the same reason the arms are: a `Confirms` row's
-- type is generated from its target, so the name is the only handle.
open import Probed.Substitution-Leaves using (row-evalStrm)
