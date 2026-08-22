-- FIXTURE: a receipt INSIDE a `postulate` block, so the marker is
-- INDENTED and the `postulate` keyword is ABOVE it rather than below.
-- Both halves of the check had to move for this: the marker regex was
-- anchored at column 0, and the subject scan only entered block mode on
-- a `postulate` line it met AFTER the receipt.  Together those made an
-- indented receipt a SILENT SKIP — not a finding, not a subject, just
-- absent from the count — which is the one outcome E3 exists to
-- prevent.  Found because a real receipt was written this way and the
-- receipt total did not move.
--
-- The marker here is wrong on purpose: `sibling-one` is not on the
-- ledger this fixture is run with, so a `PROBED` receipt over it must
-- be reported as no longer a postulate.
module Indented where

postulate
  live-one : Set

  -- PROBED: covered the two hot shapes.
  sibling-one : Set
