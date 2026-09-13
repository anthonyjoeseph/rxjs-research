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
-- and the delivery figure, claimed because it is TIGHT at both points —
-- two against two and three against three — so a reading that
-- undercharged a literal list by one delivery crosses here, where every
-- hop figure beside it would stay where it is
open import Probed.Carried-Leaf using (ofPacked-is)

-- the two pinned figures are claimed beside the rows because the store
-- half and the payload half come back EQUAL at every point, and a
-- repair that separated them would leave the rows green saying nothing
open import Probed.Fold-Burst
  using (rate₁; rate₄; layers₃; product; queued; nested;
         oneLayer-is; twoLayer-is)

-- and the two WIDE rows, whose steps re-wrap two copies of the
-- accumulator and three: they are claimed with the count figures rather
-- than alone because the six rows above are degenerate on the delivery
-- axis and these are not, and the figures are what say so — sixty-four
-- and seven hundred and twenty-nine out of six refolds, against a
-- reading flat in the rate that would read six at both
open import Probed.Fold-Burst
  using (widened; widened3; sixCounts-is; wideCount-is; wide3Count-is)

-- the four pinned figures are claimed beside the rows because the
-- payload half and the store half are what make either conjunct
-- comparable at all: a repair that sent either to zero would leave
-- every row green having compared nothing
open import Probed.Take-Frame
  using (takeCut₁; takeEdge₂; takePass; takeDeep; takeMid; takeCut;
         cut₁-is; edge₂-is; pass-is; deep-is; mid-is; cut-is)

-- and the delivery side, where one row is a comparison and the rest are
-- the floor.  The five degenerate counts are claimed BECAUSE they are
-- degenerate: a source delivering once reads one against one, so the
-- wide row — nine handed against three returned, a cut the take does
-- not get to lower — is the only place this axis could have crossed,
-- and its own row is claimed beside it
open import Probed.Take-Frame
  using (takeWide; wide-is; wide-counts;
         cut₁-counts; edge₂-counts; pass-counts; deep-counts;
         mid-counts; cut-counts)

open import Probed.Hop-Edge
  using (hopRow₁; hopRow₂; hopRow₃; hopRowP; hopRowS; hopRowE;
         packed₁-is; packed₂-is; packed₃-is; packedP-is; packedS-is;
         packedE-is)
-- and the delivery digits the packed hop figures project away, claimed
-- at the three shapes the hop family could not separate on that axis
open import Probed.Hop-Edge using (countsP-is; countsS-is; countsE-is)

-- the figures are claimed beside the rows because two independent
-- tightnesses are what make the rows mean anything: the GROWING rows
-- return exactly their bound, and what every row is HANDED equals the
-- source's own reading, so a repair loosening either end would leave the
-- rows green over a comparison with margin nobody had checked.  They
-- come in PAIRS because the payload does: a count figure and a hop
-- figure per point, so a repair that read only one half would leave the
-- other standing unexamined
open import Probed.Map-Frame
  using (mapGrow₀; mapShed₀; mapKeep₀; mapGrow₁; mapShed₁; mapKeep₁;
         mapGrowS; mapShedS; mapKeepS;
         grow₀-counts; grow₀-hops; grow₀-stores;
         shed₀-counts; shed₀-hops; keep₀-counts; keep₀-hops;
         grow₁-counts; grow₁-hops; shed₁-counts; shed₁-hops;
         keep₁-counts; keep₁-hops;
         growS-counts; growS-hops; growS-stores;
         shedS-counts; shedS-hops; keepS-counts; keepS-hops)

-- and the delivery family, whose three rows are claimed with SIX
-- figures because the finding is a DIRECTION and not a height: counts
-- one, three and five in against one, nine and twenty-five out, hops
-- three, five and seven — so a bound that merely saturated would show
-- as a figure standing still across the triple, which no single row
-- could report
open import Probed.Map-Frame
  using (mapFold₁; mapFold₃; mapFold₅;
         fold₁-counts; fold₁-hops; fold₃-counts; fold₃-hops;
         fold₅-counts; fold₅-hops)

-- the two-readings identities are claimed alongside the rows because
-- they are what the rows rest on rather than what the rows show: they
-- say a queue cannot hold something deeper than the source that emitted
-- it, so the only falsifiable half left is the frame's own write, and a
-- repair separating the two readings would leave these rows green over
-- a park branch nobody had checked again
open import Probed.Hop-Store
  using (stRow₀; stRow₁; stRow₂; q0-is; q1-is; q2-is;
         same₀; same₁; same₂)
-- and the delivery digit at the shallowest queue, claimed because the
-- hypothesis is SATURATED there: this family varies the store, so the
-- count side sitting where the outer's reading puts it is what says the
-- store axis is the one being moved
open import Probed.Hop-Store using (counts₀-is)

-- the two readings are claimed AHEAD of the rows here, inverting the
-- usual order, because the rows are degenerate in their conjuncts and
-- say so: what could have failed is the gate's reading being a constant
-- while the body under it is not, and a repair that made the gate track
-- its body would leave both rows green with nothing separating them
open import Probed.Defer-Blind
  using (body-reads; gate-reads; open-is; gated-is; openRow; gatedRow)
-- and the delivery digits, claimed as degenerate for the same reason
-- the rows above them are: a source emitting a single inner hands the
-- frame back an empty burst, so nothing on this axis could have failed
-- and saying so is what stops the rows being read as coverage
open import Probed.Defer-Blind using (open-counts; gated-counts)

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

-- and the SINK side, claimed as a triple because no one of them says
-- anything: the finding is a margin that stays at one while the two
-- halves under it move independently, so a row dropped from this list
-- would leave the other two reading as a constant nobody had varied.
-- The two fits are claimed beside them for the reason the forked pair
-- is — they stand at the second telescope, where the arrival's own
-- chain carries a frame before it sinks, which is the shape the first
-- telescope has no row for
open import Probed.Door-Fits
  using (shallowRow; deepRow; widerRow; doorDeep; doorDeep₂)

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

-- and the delivery figures, claimed for the third reason again: handed
-- equals held at every one of the three, so that half of the premise is
-- SATURATED rather than slack, and a repair that lowered the bound on
-- the count side would cross at all three at once
open import Probed.Exit-Frame using (counts₁-is; counts₂-is; counts₃-is)

-- the three saturation rows are claimed with FIVE figures because the
-- statement is an equality between two runs of the same machine, and an
-- equality is exactly the shape that goes green over a machine ignoring
-- the parameter being varied.  The two admitted lengths say the dispatch
-- meets a registry at all; the emit pair at counters of one and two say
-- the counter is READ at this program, which is the only thing that
-- makes an agreement further up a finding; and the third says where the
-- agreement begins, so the seed is claimed as sufficient rather than as
-- tight
open import Probed.Dispatch-Saturates
  using (admits₁-is; admits₂-is; short-is; long-is; seed-is;
         satSeed; satAbove; satDeep)

-- THE DEPTH ROWS, which is what is left once the floor stopped being
-- measurable.  A registry row's chain is indexed by the floor its source
-- dictates and the sink constructor demands its own index be at least
-- that floor, so the stratification this file once read off a run is now
-- what the row's TYPE says — a row asserting it could not have failed,
-- which is why the two that did are gone rather than restated.  The
-- counter is therefore spent on DEPTH alone: the two admitted lengths
-- say the nest is one chain wide at each rung, and the staircase — one,
-- two, three, then three again — says the counter is read all the way
-- down and STOPS one below the seed, which is the shape that makes the
-- saturation rows a statement about the seed rather than about a machine
-- ignoring it.  The three saturation rows stand at the deepest nest a
-- context of four admits, which is where the sibling probe's own receipt
-- says it did not reach
open import Probed.Sink-Floor
  using (floorAdmits₁-is; floorAdmits₃-is;
         one-is; two-is; three-is; four-is;
         floorSatSeed; floorSatAbove; satMid)

-- the UNFOLD row, claimed beside its own negative control because the
-- conclusion it instantiates is free at the context's own size: the
-- control fixes the same unfolded term at floor zero and the predicate
-- computes to `false`, so the two positive rows are readings of a
-- predicate that can reject rather than tidy greens over a statement
-- nothing could falsify
open import Probed.Unfold-Bound using (ground; carriesLow; carriesBoth)
