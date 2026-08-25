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
open import Probed.Cascade-Mint-Base
  using (U-mint; U-charge; U-fits;
         C-mint; C-charge; C-fits;
         F-mint; F-charge; F-fits;
         U-pw; U-pw-fits; C-pw; C-pw-fits; F-pw; F-pw-fits;
         F2-mint; F3-mint; F4-mint; F2-pw; F3-pw;
         F18-pw-fits; F18-fits; F18-base; F3-base;
         B22-mint; B22-base; B22-fits;
         P22-charge; P22-fits; P1-charge; P1-fits; N22-fits)
