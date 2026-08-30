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
module Probed.Main where

open import Probed.Root using ()
open import Probed.Cascade-Chain-Count
  using (Ch22-fits; Ch1-fits; ChU-fits; ChC-fits;
         Dup1-fits; Dup4-fits;
         S22-fits; S1-fits; SU-fits; SC-fits;
         SW-fits; ChW-fits; ChW2-fits; Adv-fits;
         Tie22-fits; Tie1-fits; TieU-fits; TieC-fits; TieW-fits; TieC4-fits)
open import Probed.Scan-Burst-Nest
  using (premises; scanBursts≡; scanEmits≡; fits₁₃; fits₁₄; flat≡; flat-fails)
open import Probed.Burst-Nest-Unit
  using (figures≡; okM; okS; okX; deferFigs≡; strongFigs≡; strongFits; strongHeads; richFigs≡; richFits)
open import Probed.Cascade-Store-Components
  using (U-parts; C-parts; F-parts)
open import Probed.Burst-Nest-Level
  using (row8≡; row16≡)
open import Probed.Sync-Factor
  using (dupSync≡6; dupOut≡2; dupA-holds;
         dupOut₃≡6; dupB-holds;
         hidSync≡4; hidSize≡9; hidOut≡0;
         mixOut≡3; mixD-holds)
open import Probed.PushVals-Caps
  using (burstLens≡; capsM-1; capsM-2; capsM-0; capsS-1; capsS-2;
         capsX-1; capsX-2; heads≡; entry≡; entryFace≡; headsClos≡; left-starved≡; census≡;
         burstOne≡; lenSh≡; capsSh-2; lenShS≡; capsShS-2; lenShX≡; capsShX-2;
         leavesM-1; leavesM-2; leavesM-0; leavesS-1; leavesS-2;
         leavesX-1; leavesX-2; leavesSh; leavesShS; leavesShX;
         axesFlat≡; axesNest≡;
         burstsM≡; burstsS≡; burstsX≡; burstsSh≡; burstsShS≡; burstsShX≡;
         burstsG≡; burstsA≡)
open import Probed.Chain-Step-Live-Nest
  using (sides≡; fits; attack≡; aFits; two≡; twoFits; mapped≡; mapFits)
open import Probed.Thru-Step-Indexed
  using (burstLen≡1; figures≡; hypAtZero; valAtOne; marginM≡;
         tightFigures≡; valTight; nestedFigures≡; premN≡; fitN1; fitN2; fitN3;
         residueFigures≡; resN1; resN2; resN3)

open import Probed.Scan-Arr-Clos-Key
  using (premises; keys≡; widths≡; fit0; fit7; fit13; fit14)

open import Probed.Scan-Arr-Margin
  using (delivered≡; deliveredHi≡; keys≡; widths≡; sizes≡; premises;
         fit0; fit4; fit8)


open import Probed.Thru-Arr-Slot
  using (burst≡; keys≡; delivered≡; unit≡; fitM; fitS; fitX; margin₃≡)

open import Probed.Depth-Sighted
  using (rootFigs≡; delivFigs≡; axisFigs≡; farFigs≡; partsFigs≡; sizeFigs≡; thirdFigs≡;
         third2Figs≡; cornerFigs≡; rootWideFigs≡; seedFigs≡)


open import Probed.Step-Frame-Clos-Fold
  using (caps≡; readings≡; capOK₃; capOK₃′; flat₃; step₃; flat₁₂; step₁₂;
         valsOK; pathOK; chargeOK)
open import Probed.Step-Frame-Clos-Inner
  using (readingsⁱ≡; capOKⁱ; argOKⁱ; valsOKⁱ; pathOKⁱ; degⁱ; flat₈ⁱ; step₈ⁱ;
         chargeOKⁱ)
open import Probed.Step-Frame-Clos-Wrap
  using (readingsʷ≡; capOKʷ; argOKʷ; valsOKʷ; pathOKʷ; deg₄ʷ; flat₈ʷ; step₈ʷ;
         chargeOKʷ)
open import Probed.Step-Frame-Level
  using (argOK₄; argOK₁₆; pathOK₄; pathOK₁₆; pathOK₆₇; deg-base;
         flat₄; step₄; flat₁₆; step₁₆; flat₆₇; step₆₇;
         floors≡; rebuilds≡; worst≡)
