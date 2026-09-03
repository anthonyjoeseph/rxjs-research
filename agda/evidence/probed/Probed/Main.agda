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

open import Probed.Root
  using (cellP1; rowP1; cellP4; rowP4; cellP7; rowP7; cellS2; rowS2)
open import Probed.Cascade-Chain-Count
  using (Ch22-fits; Ch1-fits; ChU-fits; ChC-fits;
         Dup1-fits; Dup4-fits;
         S22-fits; S1-fits; SU-fits; SC-fits;
         SW-fits; ChW-fits; ChW2-fits; Adv-fits;
         Tie22-fits; Tie1-fits; TieU-fits; TieC-fits; TieW-fits; TieC4-fits;
         tieSyn)
open import Probed.Scan-Burst-Nest
  using (premises; scanBursts≡; scanEmits≡; fits₁₃; fits₁₄; flat≡; flat-fails;
         tie₁₃; tie₁₄)
open import Probed.Burst-Nest-Unit
  using (figures≡; okM; okS; okX; liveM; nodesM; regsM; deferFigs≡; strongFigs≡; strongFits;
         strongHeads; richFigs≡; richFits)
open import Probed.Cascade-Store-Components
  using (U-parts; C-parts; F-parts; tieRegs)
open import Probed.Burst-Nest-Ladder
  using (ladder1≡; ladder2≡; ladder3≡; ladderFlat≡; flatFace; flatRow)
open import Probed.Sync-Factor
  using (dupSync≡6; dupOut≡2; dupA-holds;
         dupOut₃≡6; dupB-holds;
         hidSync≡4; hidSize≡9; hidOut≡0;
         mixOut≡3; mixD-holds;
         dupRowA; dupRowB; mixRowD)
open import Probed.PushVals-Caps
  using (burstLens≡; capsM-1; capsM-2; capsM-0; capsS-1; capsS-2;
         capsX-1; capsX-2; heads≡; entry≡; entryFace≡; headsClos≡; left-starved≡; census≡;
         burstOne≡; lenSh≡; capsSh-2; lenShS≡; capsShS-2; lenShX≡; capsShX-2;
         leavesM-1; leavesM-2; leavesM-0; leavesS-1; leavesS-2;
         leavesX-1; leavesX-2; leavesSh; leavesShS; leavesShX;
         axesFlat≡; axesNest≡;
         burstsM≡; burstsS≡; burstsX≡; burstsSh≡; burstsShS≡; burstsShX≡;
         burstsG≡; burstsA≡;
         tieM; tieS; tieX)
open import Probed.Chain-Step-Abs-Charge
  using (figures≡; fits; figuresB≡; fitsB; tieFigs≡; tieNodes1; tieNodes3)
open import Probed.Chain-Step-Live-Deferred
  using (figures≡; fits; tieFigs≡; tieLive1; tieLive3)
open import Probed.Chain-Step-Live-Nest
  using (sides≡; fits; attack≡; aFits; two≡; twoFits; mapped≡; mapFits;
         liveRow; attackRow; twoRow; mapRow)
open import Probed.Thru-Step-Indexed
  using (burstLen≡1; figures≡; hypAtZero; valAtOne; marginM≡;
         tightFigures≡; valTight; nestedFigures≡; premN≡; fitN1; fitN2; fitN3;
         residueFigures≡; resN1; resN2; resN3;
         tsRowM; tsRowS; tsRowX)

open import Probed.Scan-Arr-Clos-Key
  using (premises; keys≡; widths≡; fit0; fit7; fit13; fit14; tie13; tie14)

open import Probed.Scan-Arr-Margin
  using (delivered≡; deliveredHi≡; keys≡; widths≡; sizes≡; premises;
         fit0; fit4; fit8; tie8)


open import Probed.Thru-Arr-Slot
  using (burst≡; keys≡; delivered≡; unit≡; fitM; fitS; fitX; margin₃≡;
         tieArr≡; tieRowM; tieRowS; tieRowX)

open import Probed.Sight-All-Stream
  using (fitDup; sides≡; fitN₁; fitN₂; fitN₃; layers≡; exps≡; tieDup; tieN₃)
open import Probed.Sight-Thru-Val
  using (fitRef; sidesRef≡; grantRef₀≡; grantRef₁≡;
         grantFlat≡; delFlat≡; fitFlat; storeFlat; storeRef; storeFigs≡;
         fitOwn; grantHid≡; delHid≡; dupCols≡; dupDepth≡;
         storeParkFigs≡; grantParkFigs≡; storePark; store2Figs≡; store2;
         tieFlat; tiePark)

open import Probed.Depth-Sighted
  using (rootFigs≡; delivFigs≡; axisFigs≡; farFigs≡; partsFigs≡; sizeFigs≡; thirdFigs≡;
         third2Figs≡; cornerFigs≡; rootWideFigs≡; seedFigs≡;
         rootRow≡; rootWideRow≡; seedRow≡; dblFigs≡; dblLongFigs≡;
         chainDesc≡; chainRow; farDesc≡; farChainRow;
         walkFigs≡; walkRow≡; tieWalk1; tieWalk4)
open import Probed.Sight-Fit-Width
  using (figures≡; oldRow≡; newRow≡; tie12; tie13; tie16)

open import Probed.Burst-OutW
  using (readout≡; tieOf; tieMerge; tieSwitch; deeper≡; tieScan; tieScanκ;
  chained≡; tieChain; tieTwice)

open import Probed.Chain-Step-Regs-Level
  using (reaches; figures₁; figures₂; figures₃; figures₄; figures₆; figures₈;
         one-per-level; under-inner; foldTie)

open import Probed.Chain-Step-Regs-Second
  using (reaches; figuresC; figuresSw; figuresEx; figuresDp;
         no-longer-than-control; cut-happened; no-shrink; foldTie)

open import Probed.Chain-Step-Regs-Ops
  using (reaches; syntaxes; figS0; figS1; figS2; figM0; figM1; figM2;
         mergeGrowth; switchGrowth; fits; held-flat; survivors; foldTie)

open import Probed.Chain-Step-Regs-Read
  using (reaches; budgets; budgets′; duplicates; fits; foldTie)

open import Probed.Fold-Regs-Two-Caps
  using (reaches; figures; figures′; separates; fits; foldTie)

open import Probed.Fold-Regs-Nest-Cross
  using (cross; foldTie)

open import Probed.Frame-Drain-Live
  using (beforeLive; beforeSlots;
         figures0; figures1; figures2; figures3; figures4;
         tieLive1; tieLive4)

open import Probed.Fan-Regs-Registry
  using (counts; regsS; marginK; marginK′; regsK; lensK)

open import Probed.Fold-Regs-Row using (censusIs; foldRow)

open import Probed.Fold-Width-Reach
  using (separates; admittedRow≡; census≡; widths≡; width2≡; outruns; agrees;
         entry≡; sizesAgree; driven≡; crossesRun)
