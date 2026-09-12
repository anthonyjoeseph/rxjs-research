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
-- WHY THE TREE IS SMALL.  A probe expires with its target, and the
-- statements this tree was written against were the budget's: a grant,
-- a nest store, a walk maximum, a caps arithmetic priced in gas.  None
-- of them is stateable now, so the rows are evidence about a machine
-- that is gone and E2 expires every one of them.  What survived that
-- was the one probe whose target is a live well-formedness postulate;
-- `Probed.Descent` is the first written against the machine that
-- replaced them.
--
-- What is worth recovering from the forty-two expired files is the
-- HARNESS rather than any verdict — the real-evaluator plumbing, the
-- program families, and the coverage boundaries recorded at the foot of
-- several of them — since a green on a bound this development no longer
-- states says nothing about the descent that replaced it.
--
-- RECOVERY: git show 919f115:agda/evidence/probed/Probed/
module Probed.Main where

open import Probed.Root
  using (cellP1; rowP1; cellP4; rowP4; cellP7; rowP7; cellS2; rowS2)

open import Probed.Descent
  using (descP1; descP2; descP3; descP4; descP5;
         descP6; descP7; descP8; descP9; descP10;
         descP11; descP12; fitP1; fitP3; fitP12)

open import Probed.Fuel-Growth
  using (drF)

open import Probed.Cascade-Growth
  using (drC)

open import Probed.Fit-Preserved
  using (fpQ1₁; fpQ1₂; fpQ1₃; fpQ2₁; fpQ2₂; fpQ2₃; fpQ3₁; fpQ3₂; fpQ3₃;
         fpDrain)

open import Probed.Operator-Root
  using (opRoot)

open import Probed.Delivery-Count
  using (exponent-fork)

open import Probed.Slot-Defer
  using (slot-fork)

open import Probed.Swapped-Exponent
  using (measure-fork)

open import Probed.Step-Fold
  using (step-fold-fork)

open import Probed.Plug-Priced
  using (plug-priced-fork)

open import Probed.Clause-Sweep
  using (clause-sweep-fork)
