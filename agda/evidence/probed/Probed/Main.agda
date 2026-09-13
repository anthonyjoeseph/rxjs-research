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
         descP11; descP12; fitP1; fitP3; fitP12;
         fitP9; fitP10; fitP9L; fitP9H; fitP13H)

open import Probed.Fuel-Growth
  using (drF)

open import Probed.Entry-Fit
  using (regs₆; term₆; fitLate; fit24; survives; fitFold;
         regs₂; term₂; fitDiscards)

-- the dry rows are claimed beside the fit rows on purpose: they are the
-- ASSEMBLY's conclusion rather than the leaf's, and the leaf held at
-- this shape once while the conclusion did not
open import Probed.Gate-Constant
  using (carried₁; carried₂; carried₃; term₁; term₂; term₃;
         fitGate₁; fitGate₂; fitGate₃; dry₁; dry₂; dry₃)

open import Probed.Fit-Preserved
  using (fpQ1₁; fpQ1₂; fpQ1₃; fpQ2₁; fpQ2₂; fpQ2₃; fpQ3₁; fpQ3₂; fpQ3₃;
         fpDrain)

open import Probed.Operator-Root
  using (opRoot)

open import Probed.Carried-Leaf
  using (ofFlat; ofNest; scanFlat; scanNest; rate; packed-is; packed2L-is;
         recurRow)

-- the two pinned figures are claimed beside the rows because the store
-- half and the payload half come back EQUAL at every point, and a
-- repair that separated them would leave the rows green saying nothing
open import Probed.Fold-Burst
  using (rate₁; rate₄; layers₃; product; queued; nested;
         oneLayer-is; twoLayer-is)

open import Probed.Drain-Arrival
  using (daM6₁; daM6₂; daM24₁; daM24₂; daL₁; daL₂; daL₃; daDrain)

-- the four pinned figures are claimed beside the rows because the
-- payload half and the store half are what make either conjunct
-- comparable at all: a repair that sent either to zero would leave
-- every row green having compared nothing
open import Probed.Take-Frame
  using (takeCut₁; takeEdge₂; takePass; takeDeep;
         cut₁-is; edge₂-is; pass-is; deep-is)

open import Probed.Hop-Edge
  using (hopRow₁; hopRow₂; hopRow₃; hopRowP; hopRowS; hopRowE;
         packed₁-is; packed₂-is; packed₃-is; packedP-is; packedS-is;
         packedE-is)

-- the six figures are claimed beside the rows because two independent
-- tightnesses are what make the rows mean anything: the GROWING rows
-- return exactly their bound, and what every row is HANDED equals the
-- source's own reading, so a repair loosening either end would leave the
-- rows green over a comparison with margin nobody had checked
open import Probed.Map-Frame
  using (mapGrow₀; mapShed₀; mapKeep₀; mapGrow₁; mapShed₁; mapKeep₁;
         grow₀-is; shed₀-is; keep₀-is; grow₁-is; shed₁-is; keep₁-is)

-- the two-readings identities are claimed alongside the rows because
-- they are what the rows rest on rather than what the rows show: they
-- say a queue cannot hold something deeper than the source that emitted
-- it, so the only falsifiable half left is the frame's own write, and a
-- repair separating the two readings would leave these rows green over
-- a park branch nobody had checked again
open import Probed.Hop-Store
  using (stRow₀; stRow₁; stRow₂; q0-is; q1-is; q2-is;
         same₀; same₁; same₂)

-- the two readings are claimed AHEAD of the rows here, inverting the
-- usual order, because the rows are degenerate in their conjuncts and
-- say so: what could have failed is the gate's reading being a constant
-- while the body under it is not, and a repair that made the gate track
-- its body would leave both rows green with nothing separating them
open import Probed.Defer-Blind
  using (body-reads; gate-reads; open-is; gated-is; openRow; gatedRow)

-- the sweep figures are claimed beside the fork because the separation
-- alone would not say the margin is nil: the fork says the two rules
-- disagree at one arrival, and the sweep says the winning rank is the
-- least one that works there, so a rule supplying more than it needs
-- could not hide behind the same green
open import Probed.Arrival-Spend
  using (deepFork; packed₁-is; packed₃-is; packed₄-is; packed₅-is;
         packed₆-is; packed₇-is; packed₈-is; flat-reads)
