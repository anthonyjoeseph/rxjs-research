-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make gate-heavy` compiles `src/Main.agda`, which cannot
-- import this tree, and `make wiring` scans `agda/src` only.
--
-- Naming each witness here is what keeps this tree honest: a refutation
-- that is not listed is not checked, exactly as in src/Main.agda.
module Refuted.Main where

open import Refuted.Caps-Face
  using (caps-frame-boundary-absurd; reach-via-size-absurd;
         scan-count-under-ceiling-absurd; wid≤size-absurd)
open import Refuted.Anchor
  using (g0-hasAtLeast-absurd; walk-hyps-absurd; hop-anchor-absurd;
         round3b-ledger-reset-absurd; round3-old-ell-absurd;
         round3-anchor-indexed-absurd)
open import Refuted.Wet
  using (wet-ceiling-absurd; wet-ell-absurd)
open import Refuted.Hop-Drag
  using (hop-drag-absurd)
open import Refuted.Cut-Through
  using (cutThrough-close-bound-dying-absurd; cutThrough-live-dying-absurd)
open import Refuted.MergeAll-Drain
  using (mergeAllDrain-nodry-nestBud-absurd; thruConsume-nodry-nestBud-absurd)
open import Refuted.Thru-Loop
  using (thruConsume-nodry-loop-absurd)
open import Refuted.Inner-Nodry
  using (inner-nodry-inv-regLen-absurd)
open import Refuted.Nest-Depth-One
  using (descent≡81; oneSyn≡74; nest-one-syn-absurd)
open import Refuted.Cascade-Deliv-Depth
  using (descent≡49; perDeliv≡44; val-hyp; cascade-deliv-depth-absurd)
open import Refuted.Cascade-Nest-PerDeliv
  using (grown≡48; perDeliv≡35; store-val-hyp; cascade-nest-perDeliv-absurd)
open import Refuted.Chain-Step-Nodes
  using (grown≡22; charge≡15; chainStep-nodes-absurd)
open import Refuted.Share-Sink-Nodes
  using (grown≡3; charge≡1; share-sink-nodes-absurd)
open import Refuted.Apply-Fn-Nest
  using (subbed≡2; oneWrap≡1; applyFn-nest-absurd)
open import Refuted.Step-Frame-Nest-Dup
  using (dup≡80; perFrame≡40; stepFrame-nest-dup-absurd)
open import Refuted.Thru-Subscribe-Nest
  using (emitted≡80; perValue≡41; stepFrame-nodes-thru-absurd;
         parent≡41; stepFrame-nodes-at-thru-absurd)
open import Refuted.Scan-Fold-Burst
  using (fold≡65; charge≡64; scan-fold-burst-absurd)
open import Refuted.Inner-Drain-Share-Nest
  using (delivered≡40; charged≡0; capsPin;
         stepFrame-nodes-inner-share-absurd; unit≡41)
open import Refuted.Inner-Drain-Nest
  using (drained≡80; queued≡40; stepFrame-nodes-inner-absurd;
         parent≡40; stepFrame-nodes-at-inner-absurd;
         drained₃≡120; queued₃≡40; unitCharge≡82;
         stepFrame-nodes-inner-unit-absurd)
