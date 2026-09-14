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
--
-- WHY THE TREE IS SMALL.  A probe expires with its target, and the
-- statements this tree was written against were the budget's: a grant,
-- a nest store, a walk maximum, a caps arithmetic priced in gas.  None
-- of them is stateable now, so the rows are evidence about a machine
-- that is gone and E2 expires every one of them.
--
-- AND TWO FURTHER GENERATIONS EXPIRED THE SAME WAY, WHICH IS WHAT SAYS
-- THE MECHANISM IS THE RIGHT ONE RATHER THAN AN OVERHEAD.  Six files
-- were written against a drain premise that READ a registry against the
-- program, and that reading is refuted in every form it was tried; nine
-- more instantiated the CARRIED bound a frame was held to, and the whole
-- apparatus of a carried figure went when the descent stopped being
-- ordered by a syntactic seed.  Every one of those rows was green to the
-- last day and said nothing about the statement that replaced it — which
-- is exactly the silent death E2 exists to make loud.
--
-- What is worth recovering from the fifty-one expired files is the
-- HARNESS rather than any verdict — the real-evaluator plumbing, the
-- program families, and the coverage boundaries recorded at the foot of
-- several of them — since a green on a bound this development no longer
-- states says nothing about the descent that replaced it.
--
-- RECOVERY: git show 919f115:agda/evidence/probed/Probed/
module Probed.Main where

-- THE APPARATUS IS CLAIMED FROM THE ROOT rather than from whichever
-- file happens to spend it: E7 refuses a `-- TARGET:` with no `Confirms`
-- row and E6 refuses a `-- FORK:` that does not inhabit `Separates`, so
-- both belong to the tree and a tree with nothing open still owes them.
open import Probed.Apparatus using (Confirms; Separates)

-- THE CONNECT EDGE'S COUNTING COMPONENT, at slot tables of one and
-- three shared slots — the only part of the order that counts rather
-- than measures, and the only one decidable without a run.
open import Probed.Connect-Count using (row-one-count; row-three-count;
  row-three-one-taken; row-last-slot; row-with-slack; row-not-head)

-- THE SHELF UNDER THE SUBSTITUTION LEMMA — the telescope membership,
-- whose rows buy non-vacuity rather than an inequality, and the
-- weakening, whose rows have content on both sides.
open import Probed.Data-Shelf using (row-of-head; row-of-tail;
  row-wk-leaf; row-wk-strm)

-- THE TWO BINDING ARMS THE STRICT DROP DEFERS — instantiated at the
-- observable payload, which is the region that could make either
-- false.
open import Probed.Eval-Binders using (row-case-data; case-data-bound;
  row-case-obs; case-obs-bound; case-obs-value;
  row-if-selected; row-if-unselected)

-- THE BURST REPORT'S TWO PRICING LEAVES — the data payload, whose rows
-- reach the two types at which the reading recurses, and the silent
-- term, whose load-bearing row stands at a type reaching an observable
-- the value does not take.
open import Probed.Burst-Handed using (row-data-flat; row-data-pair;
  row-data-sum; row-silent-flat; row-silent-sum; row-silent-binder)
