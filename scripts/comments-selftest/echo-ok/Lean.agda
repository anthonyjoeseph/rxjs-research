module Lean where

-- THE MUST-NOT DIRECTION, pinning the two precision properties that make the
-- fifth check usable.  (1) A word only counts against a section the block
-- ACTUALLY HAS.  This block has no coverage section, so saying that a K = 4
-- probe reached the near-degenerate rows and no further is the only place
-- that fact could live, and it has to stay legal.  (2) A marker line and its
-- indented continuations are not explanation, so a section whose own text
-- names its own subject cannot fire the check against itself.
-- REFUTED: `caps-frame-boundary-absurd` — the refutation is adversarial in
--   the stored state, so the unconditional form is the false one.
postulate lean : Set
