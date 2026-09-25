-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make gate-heavy` compiles `src/Main.agda`, which cannot
-- import this tree, and `make wiring` scans `agda/src` only.
--
-- Naming each witness here is what keeps this tree honest: a refutation
-- that is not listed is not checked, exactly as in src/Main.agda.
--
-- WHY THE TREE IS ONE FILE.  A refutation dies when `src` can no
-- longer STATE what it kills, and what this tree spent its life killing
-- was a NUMBER — a depth read off the program text, a store, a burst
-- length reserved against, an unconnected count, an entry triple.  The
-- descent is no longer denominated in any of them, and the measures
-- themselves are deleted, so those witnesses are false of nothing.
-- That is how a refutation is meant to die, and it is the reason this
-- tree is checked rather than filed: the day the statements went, the
-- check went red and said so.
--
-- WHAT SURVIVES IS THE ONE THAT IS ABOUT THE EVALUATOR RATHER THAN
-- ABOUT A MEASURE, and it is the floor under everything that replaced
-- them: the only domain predicate this evaluator could USE is `⊤`.
-- Combined with the whole family above — no reading fixed before a run
-- bounds what the run emits — it rules out both of the obvious
-- descents, which is why a candidate recursing on the TYPE is the
-- shape that is left.
--
-- RECOVERY: git show 919f115:agda/evidence/refuted/Refuted/
-- RECOVERY: git show 64c568e2:agda/evidence/refuted/Refuted/ holds the ten
--   witnesses that died with the measures — the depth climb, the burst
--   length, the store, the connect arithmetic, the template drop.  Each
--   was true when written; what transfers is the adversarial program
--   family, never the conclusion drawn from it.
-- RECOVERY: git show ba1285b:agda/evidence/refuted/Refuted/Dry-Wrap.agda
module Refuted.Main where

-- THE REPAIR THE WHOLE DELETED FAMILY INVITED, killed in its own
-- currency rather than in arithmetic.  If no number fixed before a run
-- can bound what the run emits, the move is to stop denominating the
-- descent in a number
-- at all and carry a domain predicate -- and the only shape of one this
-- evaluator could USE, since it cases on the term and needs the child's
-- proof, is the structural one, which is `⊤`.  `sub-total` is claimed
-- beside the refutation because it is the whole content: the predicate
-- is inhabited by plain recursion on the term, so holding one is
-- holding a copy of the term.
open import Refuted.Domain-Predicate using
  (structural-domain-has-content-false; sub-total)

-- A REFUTATION THAT RUNS THE EVALUATOR NEEDS AN EVALUATOR THAT
-- COMPUTES, and while the candidate's arms are postulated none does.
-- RECOVERY: git show 3abdafa1:agda/evidence/refuted/Refuted/Flattened-Input.agda
--   holds the input-under-a-flattener counterexample, pinned by
--   running the evaluator; it comes back when the arms do.

-- THE ROOT-SIDE TWIN OF THE SLOT-TABLE FORGERY: why `run-wellFormed`
-- carries an authorship premise on its program and not only on its
-- table.
open import Refuted.Forged-Root using (saw-forged-root)

-- THE ROOM IS THE WRONG CURRENCY FOR THE STORE RE-ENTRY.  A candidate
-- indexed by the unconnected count closes every edge of the subscribe
-- cycle but one, and the repair for that one is an invariant funding
-- the flattener's backlog pop out of a fall in the room.  A program
-- with no share in it has room zero at every state and still takes
-- that pop, so the funding conclusion is refuted outright rather than
-- merely unproven.
open import Refuted.Room-Backlog using (room-zero; saw-room-cannot-fund)
