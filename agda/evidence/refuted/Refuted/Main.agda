-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make agda` compiles `src/Main.agda`, which cannot
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
open import Refuted.Concat-Drain
  using (concatDrain-nodry-nestBud-absurd; thruConsume-nodry-nestBud-absurd)
open import Refuted.Thru-Loop
  using (thruConsume-nodry-loop-absurd)
open import Refuted.Inner-Nodry
  using (inner-nodry-inv-regLen-absurd)
open import Refuted.Nest-Depth-One
  using (descent≡21; oneSyn≡19; nest-one-syn-absurd)
