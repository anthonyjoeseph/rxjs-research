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
-- AND A SECOND GENERATION EXPIRED THE SAME WAY, WHICH IS WHAT SAYS THE
-- MECHANISM IS THE RIGHT ONE RATHER THAN AN OVERHEAD.  Six files were
-- written against a drain premise that READ a registry against the
-- program, and the reading is now refuted in every form it was tried;
-- the statement they instantiated is stated per TEMPLATE instead, and
-- it quantifies over states rather than fixing one, so no `refl` row
-- can reach its hypotheses at all.  Their rows were green to the last
-- day and said nothing about the statement that replaced them — which
-- is exactly the silent death E2 exists to make loud.
--
-- What is worth recovering from the forty-two expired files is the
-- HARNESS rather than any verdict — the real-evaluator plumbing, the
-- program families, and the coverage boundaries recorded at the foot of
-- several of them — since a green on a bound this development no longer
-- states says nothing about the descent that replaced it.
--
-- RECOVERY: git show 919f115:agda/evidence/probed/Probed/
module Probed.Main where

open import Probed.Root
  using (cellP1; rowP1; cellP4; rowP4; cellP7; rowP7; cellS2; rowS2)

open import Probed.Operator-Root
  using (opRoot)

open import Probed.Carried-Leaf
  using (ofFlat; ofNest; scanFlat; scanNest; rate; packed-is; packed2L-is;
         recurRow)

-- the two pinned figures are claimed beside the rows because the store
-- half and the payload half come back EQUAL at every point, and a
-- repair that separated them would leave the rows green saying nothing
open import Probed.Fold-Burst
  using (rate₁; rate₄; layers₃; product; queued; nested;
         oneLayer-is; twoLayer-is)

-- the four pinned figures are claimed beside the rows because the
-- payload half and the store half are what make either conjunct
-- comparable at all: a repair that sent either to zero would leave
-- every row green having compared nothing
open import Probed.Take-Frame
  using (takeCut₁; takeEdge₂; takePass; takeDeep; takeMid; takeCut;
         cut₁-is; edge₂-is; pass-is; deep-is; mid-is; cut-is)

open import Probed.Hop-Edge
  using (hopRow₁; hopRow₂; hopRow₃; hopRowP; hopRowS; hopRowE;
         packed₁-is; packed₂-is; packed₃-is; packedP-is; packedS-is;
         packedE-is)

-- the six figures are claimed beside the rows because two independent
-- tightnesses are what make the rows mean anything: the GROWING rows
-- return exactly their bound, and what every row is HANDED equals the
-- source's own reading, so a repair loosening either end would leave the
-- rows green over a comparison with margin nobody had checked
open import Probed.Map-Frame
  using (mapGrow₀; mapShed₀; mapKeep₀; mapGrow₁; mapShed₁; mapKeep₁;
         mapGrowS; mapShedS; mapKeepS;
         grow₀-is; shed₀-is; keep₀-is; grow₁-is; shed₁-is; keep₁-is;
         growS-is; shedS-is; keepS-is)

-- the two-readings identities are claimed alongside the rows because
-- they are what the rows rest on rather than what the rows show: they
-- say a queue cannot hold something deeper than the source that emitted
-- it, so the only falsifiable half left is the frame's own write, and a
-- repair separating the two readings would leave these rows green over
-- a park branch nobody had checked again
open import Probed.Hop-Store
  using (stRow₀; stRow₁; stRow₂; q0-is; q1-is; q2-is;
         same₀; same₁; same₂)

-- the two readings are claimed AHEAD of the rows here, inverting the
-- usual order, because the rows are degenerate in their conjuncts and
-- say so: what could have failed is the gate's reading being a constant
-- while the body under it is not, and a repair that made the gate track
-- its body would leave both rows green with nothing separating them
open import Probed.Defer-Blind
  using (body-reads; gate-reads; open-is; gated-is; openRow; gatedRow)

-- the sweep figures are claimed beside the fork because the separation
-- alone would not say the margin is nil: the fork says the two rules
-- disagree at one arrival, and the sweep says the winning rank is the
-- least one that works there, so a rule supplying more than it needs
-- could not hide behind the same green
open import Probed.Arrival-Spend
  using (deepFork; packed₁-is; packed₃-is; packed₄-is; packed₅-is;
         packed₆-is; packed₇-is; packed₈-is; flat-reads)

-- the packed rows are claimed beside the fits because each is a way a
-- fit could have been green having asked for nothing — no arrival, an
-- arrival reaching no chain, or a chain the premise compares at nought
-- against a reading of nought — and the ladder's rows are claimed for
-- the opposite reason: they hold by equality at three rungs, so the
-- constant margin is the finding rather than a control.  The two forked
-- rows are claimed as a PAIR, since what either says alone is a figure
-- and what they say together is that the fan-out never reaches the
-- door: a repair letting a second chain through would move both
open import Probed.Door-Fits
  using (bareRow; doorBare; flatRow; doorFlat;
         flat₂Row; flat₃Row; doorFlat₂; doorFlat₃;
         gatedRow; doorGated;
         forkedRow; forkedRawRow; doorForked; doorForkedRaw)

-- the agreement rows are claimed beside the fork because a separation
-- between two rules that differ everywhere says nothing about the shape
-- it stands at, and the counts because each is a way both rules could
-- have been evaluated over nothing — and the `thru-outer` counts are
-- claimed for the opposite reason again: they are nought at every point
-- measured, which is the finding rather than a control
open import Probed.Chain-Compose
  using (agree₁; agree₂; agree₃; agreeCap; exitFork;
         uTerm; uReach; uInners; uOuters; uRank;
         gTerm; gReach; gInners; gOuters; gRank;
         capReach; capInners; capOuters; uStore; gStore)

-- the sweeps are claimed beside the fork because the separation says
-- only that the store half is read, and what the rows add is the two
-- things a separation cannot: that a cascade's write stays under the
-- bound the fold fixes, at three rates, and that neither slot kind puts
-- a second chain under that bound at all — the second being what says
-- the residue is the sink's rather than untried here
open import Probed.Store-Rank
  using (storeFork; liveA; fastA; fasterC; liveB; manyD;
         sharedE; sharedF)

-- the quiet fan-out is claimed beside the fork for the reason the
-- agreement rows elsewhere are: a separation between two rules that
-- differ everywhere says nothing about the shape it stands at, and
-- this one agrees at the same width with the writing removed.  The
-- payload row is claimed for the opposite reason again — it is nought
-- at every point, which is what attributes the store's whole figure to
-- the folds rather than to what crossed the share
open import Probed.Share-Fanout
  using (fanoutFork; oneRow; thriceRow; mixedRow; payRow;
         quietRow; quietAgree)

-- the store figures are claimed beside the three dry rows because each
-- is a way a dry-free reading could have been green having dispatched
-- nothing — an empty registration list, a store that was nought going
-- in, or one the dispatch never wrote — and the quiet row is claimed
-- for the opposite reason: it is nought at both ends, which is what
-- separates the dry property from the writing rather than controlling
-- for it
open import Probed.Sink-Dry
  using (one3-is; quiet3-is; sinkOne3; sinkQuiet3)

-- the three packed figures are claimed beside the dry rows because the
-- dry flag reading false says nothing on its own — it is false at a
-- point nothing emitted too — so what makes those rows evidence is the
-- handed reading being positive and the rank standing strictly above
-- the bound.  The exit-frame figure is claimed for the opposite
-- reason: it is nought in every column, which is the row's own
-- statement that it buys instantiability and not coverage
open import Probed.Exit-Frame
  using (packed₁-is; packed₂-is; packed₃-is; fi-packed-is;
         dryRow₁; dryRow₂; dryRow₃;
         fromInnerCarried; fromInnerDry)
