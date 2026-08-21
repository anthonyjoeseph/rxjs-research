-- FIXTURE: an INVENTED marker.  It must be a finding, not a silent skip: a
-- marker the check does not know is a receipt it cannot audit.  Two real
-- receipts in this repo were spelled `PROBED-GREEN`.
module Unknown where

-- PROBED-GREEN 2026-01-01: covered the two hot shapes.
postulate
  live-one : Set
