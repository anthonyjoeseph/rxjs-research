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
open import Probed.Cascade-Nest-Store
  using (U-chains; U-descent; U-holds;
         C-chains; C-descent; C-holds;
         F-chains; F-descent; F-holds)
open import Probed.Cascade-Chain-Count
  using (Ch22-fits; Ch1-fits; ChU-fits; ChC-fits;
         Dup1-fits; Dup4-fits;
         S22-fits; S1-fits; SU-fits; SC-fits;
         SW-fits; ChW-fits; ChW2-fits; Adv-fits;
         Tie22-fits; Tie1-fits; TieU-fits; TieC-fits; TieW-fits; TieC4-fits;
         Sh1-fits; Sh3-fits; ShCh3-fits)
open import Probed.Scan-Burst-Nest
  using (premises; scanBursts≡; scanEmits≡; fits₁₃; fits₁₄; flat≡; flat-fails)
open import Probed.Subscribe-Nest
  using (premises₁; premises₂; premises₃;
         fits₁; fits₂; fits₃;
         sizes≡; bases≡; bursts≡; emits≡;
         spend₁; spend₂; spend₃;
         premThru; burstThru≡; fitsThru; thruFigs≡; spendThru;
         premInner; readInner≡; spendInner;
         premDeep; readDeep≡; spendDeep;
         premDeeper; readDeeper≡; spendDeeper)
open import Probed.Subscribe-Nest-Wrap
  using (premM; premS; premX; bursts≡; nodes≡;
         emits≡; emitsS≡; emitsX≡; base≡; fitsM; fitsS; fitsX)
open import Probed.Chain-Caps-Flat
  using (U-row; C-row; F-row)
open import Probed.Cascade-Store-Components
  using (U-parts; C-parts; F-parts)
open import Probed.Sync-Factor
  using (dupSync≡6; dupOut≡2; dupA-holds;
         dupOut₃≡6; dupB-holds;
         hidSync≡4; hidSize≡9; hidOut≡0;
         mixOut≡3; mixD-holds)
