-- THE FOLD'S REGISTRY PRICE, READ AS A LENGTH AND NOT AS A LEVEL.
-- What a level has to cover here is one quantity: the LONGEST SINGLE
-- registration the fold leaves behind.  `regsSz?` is an `all` over the
-- registry, so the price is per ENTRY -- many short entries cost what
-- one costs, and only a single entry getting longer can move it.  A
-- subscribing frame lengthens no standing entry; it swaps its own head
-- for a `from-inner` and registers a NEW chain carrying one frame per
-- operator of the inner it received.
--
-- SO THE PRICE IS ONE FRAME STEP, AND NOT A DOUBLING, BECAUSE THE TWO
-- CAPS ARE DIFFERENT QUANTITIES.  A registered chain is the walked
-- path plus the frames each subscribe along it pushes.  The path is
-- capped by `pathSz?` at `S`, which bounds both its length and every
-- frame's own syntax, so what a whole walk can push is a PRODUCT of
-- two quantities `S` dominates -- while the standing registry and the
-- arriving values are capped by `B`, which the caller has already
-- taken up the iterate.  One `sizeStep S B` buys `S·(1+2B)`, which
-- covers `S·S` and `B` together at every `1 ≤ S ≤ B`.  Reading a
-- single budget for both caps is what makes the doubling look
-- available, and it is exactly the collapse `Refuted.Fold-Path-Regs-
-- Len` breaks: a maximum doubled cannot pay a spine's product.
module Verify-Budget-Sufficient.Regs-Fold-Len where

open import Data.Bool using (Bool; true)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator using (Sched; EvalSt; Path; foldPath; iterSize; sizeStep)
open import Verify-Budget-Sufficient.Caps using (iterSize-suc; iterSize-infl)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

-- WHAT THE FOLD LEAVES REGISTERED, AT THE ONE CONJUNCT THAT CAN MOVE.
-- The step is DETERMINED -- one call, one frame step -- rather than a
-- witness chosen after the fact, and nothing in it is denominated in
-- how deep a sink re-enters.  The path's own cap IS denominated here,
-- and that is the restatement: the walk's product is charged against
-- `S`, the quantity that bounds it, instead of against the entry
-- budget it is unrelated to.  Both of the fold's re-entries are inside
-- this claim: rootward through the frames and sideways at a share,
-- where it and `dispatchShare` are mutually recursive and every
-- admitted chain re-enters with its own continuation.
--
-- REFUTED: `Refuted.Chain-Step-Regs-Cap` -- the fixed-cap form this
--   replaces, at a five-node inner and a six-frame chain against a cap
--   of six.  Both premises hold and the registered chain has length
--   eight, so what broke was the length ledger rather than any size
--   reading, and no further hypothesis repairs it.
-- REFUTED: `Refuted.Fold-Path-Regs-Len` -- the DOUBLING itself, at a
--   frame whose function NESTS its argument in flatten levels.  `B`
--   must dominate two independent quantities, the frame's own syntax
--   and the path's length, so it is their MAXIMUM -- while `k` such
--   frames of depth `d` compose down ONE spine and register their
--   PRODUCT.  Ten frames of depth two enter at a cap of thirteen,
--   walked chain twelve and standing registry twelve, and leave a
--   chain of thirty-one registered against a doubling that offers
--   twenty-six.  No constant factor repairs it, and no further
--   hypothesis: the two parameters move independently, so the repair
--   is a conclusion stated in the per-FRAME currency the size ledger
--   already charges in and the proven walk-face siblings already
--   premise.
-- DEAD ROUTE: composing a per-FRAME registry statement along the path,
--   so that the fold needs no statement of its own.  Each frame costs a
--   level, so a chain costs its own length in levels and a sink
--   re-enters chains that cost theirs -- and the level range that
--   asks for is dead in `Refuted.Sink-Level-Range`, at the smallest
--   cap the caps invariant admits.  What blocks it is the arithmetic
--   rather than the composition: the size reading is an exponential
--   of the level and the affordable range is a cap squared plus a
--   cap, so sharpening the walk factor buys a constant and the two
--   separate at every cap.
-- DEAD ROUTE: and neither does carrying the values at the entry budget
--   through the frame arm, which is what proving this leaf by
--   induction along the path would need.  A frame INFLATES the values
--   it passes on -- the size
--   ledger takes them a level per frame -- so a fold whose statement
--   fixes one budget for the values cannot hand that budget to its own
--   recursion.  What survives is the reading here, where the values
--   are premised once at entry and the registered length is bounded
--   against that reading rather than against the values the walk
--   later carries.
-- DEAD ROUTE: and neither does deleting this face outright and reading
--   the registry off the caps face's own levelled walk, which is the
--   repair the two faces' near-identical clause structure invites.  The
--   projector and the levelled walk predicate both exist and the walks
--   do rewrite clause for clause, but the consumer does not: the depth
--   cascade is what spends these walks, and its own ceiling is a
--   PREMISE of the lemma that produces the caps receipt, so a cascade
--   taking that receipt would be proving its ceiling from its ceiling.
--   The caps face sits ABOVE the depth cascade, not beside it, and that
--   ordering is what the redundancy reading misses.
--
-- PROBED: `Probed.Chain-Step-Regs-Level` -- the ROOTWARD re-entry, over
--   a stack of one to eight `mergeAllᵉ` flattens whose sources are each
--   other, every figure read off a state the evaluator reached and
--   every depth pinned to the arm that measures a real `chainStep`.
--   The registered length grows by exactly ONE per flatten level while
--   the inner's own size grows by four, so the descent does not recurse
--   and the one axis that could refute this form is closed along that
--   route.  NOT COVERED: the SIDEWAYS re-entry at a `share-sink`, and
--   the shapes the sweep below covers.
--
-- PROBED: `git show b066797` holds three re-entry sweeps whose reading
--   is one sentence and whose programs are the expensive part -- the
--   SIDEWAYS re-entry where `foldPath` and `dispatchShare` recur
--   through a four-deep share telescope rooted at each of five slots;
--   the DIAMOND, where a share fans to several registered chains at
--   widths one to four and again compounded over a two-way def; and
--   the CUTTING arm, a `takeᵉ` expiring at the leaf, on a share's def
--   between two sinks, and on one branch of a width-two share where
--   `shareGo`'s ordering is observable.  In all three the maximum
--   registered path length is UNCHANGED across the step and equal to
--   the flatten control's: the telescope holds at two, the fan at
--   three at every width, and no cut leaves an entry longer than the
--   control.  So a share is entered rather than merely built (the
--   emit count is the crossing count plus one), a fan multiplies
--   registry ENTRIES and lengthens none of them, and a cut only
--   shrinks.  NOT COVERED: a telescope deeper than four; and the cut
--   rows speak to the length conjunct alone, since a shrinking step
--   satisfies a growth bound whatever the frames did -- and two of
--   their arms did not cut at all, a FIRST arrival giving `switchAllᵉ`
--   nothing to abandon and `exhaustAllᵉ` nothing to refuse, which is
--   the gap the sweep below is read to close.
-- PROBED: `Probed.Chain-Step-Regs-Second` -- the SECOND arrival, which
--   closes both gaps the cutting sweep named.  The inner is a scripted
--   slot timed past the outer, so it is still live when the second
--   arrival lands and the first arrival's full `cascade` supplies the
--   state; then `switchAllᵉ` really abandons and `exhaustAllᵉ` really
--   refuses.  Both now read STRICTLY BELOW the flatten control's
--   registry rather than identical to it, which is what says the
--   cutting arm was taken; and no row shrinks -- the control grows by
--   the inner it registers, both cutting arms hold level -- so the SIZE
--   conjunct is under test here for the first time, not merely the
--   length one.  Registered length is flat at the control's on every
--   row, the share-def cut included.  NOT COVERED: what an abandoned
--   inner's own delivery would do after its registration is dropped.
--
-- PROBED: `git show b066797` holds the arrival that comes FROM an
--   inner, which is the re-entry every sweep above steps past: all of
--   them step an OUTER's arrival, and an inner registered by a flatten
--   re-enters `foldPath` mid-flight carrying the sighted path the
--   outer built.  It is the second-arrival program with one line of
--   its script changed -- the inner due BETWEEN two outer values
--   rather than past them all -- and the shift is pinned by a
--   provenance CONTRAST rather than a bare number: the stepped
--   arrival's source differs from the first arrival's under the
--   retiming and equals it under the sibling's timing, so the two
--   readings together say the door was entered at an inner.
--   Registered length comes back no longer than the same program's
--   flatten control at the same step, on every arm -- so the one
--   unbounded conjunct is not lengthened by the frames a mid-flight
--   path arrives carrying.  NOT COVERED: one level of nesting, so an
--   arrival from an inner OF an inner is unreached; and the stepped
--   arrival is the SECOND overall, so a door met after several inner
--   deliveries have landed is unmeasured.
--
-- PROBED: `Probed.Chain-Step-Regs-Ops` -- an inner that CARRIES
--   OPERATORS, which is the axis `Refuted.Chain-Step-Regs-Cap` moves
--   to break the fixed-cap form and which every sweep above leaves
--   still: all of them register an inner that is a bare slot read, so
--   no registered chain in any of them gains a frame of the inner's
--   own.  Three operator counts over the second-arrival program, read
--   as a SUM of registered lengths because the entry a step adds is
--   shorter than the longest one already standing and a maximum is
--   therefore flat while the registry gains frames.  The merge arm
--   grows by exactly one more than the operator count at each count,
--   against a switch arm that grows by nothing at any of them -- so
--   the frames pushed are the inner's, and the axis is live in a RUN
--   and not only in a constructed state.  The growth sits under the
--   inner's own syntax, which is the quantity the arrival's size
--   premise bounds, so a level covers what the cap could not.  The
--   registry is then read ENTRY BY ENTRY, matched on the id each was
--   registered under, because the sum is a lens and not the charge:
--   `regsSz?` is an `all`, so many short entries cost what one costs
--   and only a single entry getting LONGER can move the price.  No
--   entry standing before a step is longer after it, on either arm at
--   any count, over a surviving set the rows count rather than assume
--   -- so every frame the total records arrives as a NEW entry and
--   the charge is untouched by the growth.  NOT COVERED: the
--   operators are identity maps and one nesting level, so a frame
--   reading its argument's syntax is unmeasured; and every row
--   registers one new entry per step, so a step registering several
--   is reached only through the held row.
--
-- PROBED: `Probed.Chain-Step-Regs-Read` -- a frame that READS its
--   argument's syntax, which is the axis every sweep above holds
--   fixed, taken here in its DUPLICATING form: a map function merging
--   its argument with itself, stacked zero, two, four and six deep.
--   The duplication is witnessed rather than assumed -- the chains
--   standing after the step run three, nine, thirty-three, a hundred
--   and twenty-nine -- and the charge does not see it: entry and exit
--   budgets are EQUAL at every height, both found by independent
--   searches so an unsatisfiable premise would show as a wrong figure
--   rather than as a green.  The copies are SIBLINGS and `regsSz?` is
--   an `all`, so exponential width costs what one entry costs.  The
--   exit is read against one FRAME STEP of the entry budget, taken at
--   `S = B` so the joint search pins all three premises at once.  NOT
--   COVERED: only the additive shape, and only `S = B`.  A frame that
--   NESTS its argument composes down one spine instead, which is
--   where the doubling this replaced dies.

-- PROBED: `Probed.Fold-Regs-Two-Caps` -- the two caps SEPARATED,
--   which every row above collapses.  Neither cap can refute by
--   moving up: raising either enlarges the grant and weakens the
--   premise it gates at once, so for a fixed door the binding
--   instantiation is each cap at its own least, and separation is a
--   property of the PROGRAM.  Two families that look like they
--   provide it do not, and both were run: re-applying the fold
--   saturates the registry at the first step, and on a duplicator
--   `pathSz?` charges each frame's own syntax, so a value the walked
--   frames built is priced by the cap that prices them.  What works
--   is standing the syntax OFF the path -- a duplicator stack merged
--   beside a single map, with the scheduler firing the map's source
--   first.  The path column holds at three while the registry column
--   climbs six, nine, fourteen with the branch nothing walks, and the
--   exit column equals the registry column at every row: the fold
--   charges the registry nothing the walk added, so the frame step is
--   spare and the margin widens with the separation instead of
--   closing.  NOT COVERED: the walk is disjoint from the standing
--   entries here, and the separation is only in the length conjunct --
--   `S` is held at one program throughout rather than swept.
-- PROBED: `git show b066797` holds the same separation with the walk
--   INSIDE the structure that prices `B` rather than beside it.  The
--   walked branch carries duplicator frames of the same shape as the
--   unwalked heavy one, so the entries the fold registers are cut from
--   the syntax the standing entries are, and the reading is taken over
--   EVERY chain the arrival matches instead of the head of the
--   registry's list.  The caps stay apart -- path at six against a
--   registry at seven and ten -- and the exit column equals the
--   registry column at every row, so a walk of the standing shape adds
--   nothing above what was already standing and the step stays spare.
--   NOT COVERED, and it is a finding rather than a gap in the sweep:
--   the walked DEPTH moved no column, three frames reading identically
--   to one, so the construction does not lengthen the walked chain and
--   a walk that is longer than the standing entries is still unread.
-- PROBED: `git show b066797` also holds the NESTING spine below its
--   crossover -- the shape that refuted the doubling and the only one
--   known to make a registration track the walk's PRODUCT rather than
--   its maximum: `k` frames each wrapping `d` flatten levels compose
--   down one spine, so the exit rises with `k * d` while the walked
--   path rises with `k` alone.  Depth cannot refute -- it raises the
--   frame's own syntax, and the cap is a MAXIMUM over that syntax and
--   the walked length, so a deeper frame buys the room it costs --
--   which leaves height as the one measure-side axis and one stretch
--   worth spending programs on: the heights at which the path is
--   still shorter than the syntax, where both caps sit PINNED and the
--   grant does not answer a taller spine.  Read at two such heights
--   the caps hold at thirteen while the exit climbs nineteen to
--   thirty-one, so the margin is shrinking there and the step still
--   fits with room.  Whether that stretch ENDS is the live sibling
--   below, and it is the reading that makes this one safe rather than
--   a trend.
-- PROBED: `Probed.Fold-Regs-Nest-Cross` -- that it does end, which is
--   what makes the shrinking stretch above safe rather than a trend.
--   Past the height at which the spine outgrows the frame the caps
--   track the height instead of the syntax: at the first such height
--   they read fifteen against an exit of forty, the grant having gone
--   from three hundred fifty-one to four hundred sixty-five for nine
--   registrations more.  So the grant is quadratic in a cap the spine
--   itself drives while the exit is linear in it, and the margin
--   widens from there rather than closing.  NOT COVERED: one depth,
--   and one arrival -- the spine is read where it is longest, not
--   where a second delivery has already cut it.
-- PROBED: `git show b066797` also holds the whole family read at an
--   arrival that is NOT the first, which is the axis every row above
--   takes at its easiest: they take the door once, so the reading is
--   made against the state the subscribe left, the registry at its
--   shortest and no chain having run.  Read at the second and third
--   arrivals, below the crossover and again above it, the path cap
--   and the exit hold while the ENTRY cap climbs exactly once -- from
--   the value the first arrival was handed to the value that arrival
--   left -- and then does not move.  So the premise stands on the
--   fold's OWN registrations by the second delivery and that is a
--   fixed point of the run rather than an artifact of the subscribe;
--   and the exit does not follow the entry up.  Above the crossover
--   that is the one place a delivery can LOWER the column the grant is
--   quadratic in while the exit it must clear stays linear in that
--   same column and was produced by the longer spine -- and the fit
--   holds there too, so cutting the spine does not break it.  NOT
--   COVERED: one height on each side of the crossover, one program
--   family, and no arrival past the third, which the outer slot does
--   not offer.
postulate
  foldPath-regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) →
    1 ≤ S →
    S ≤ B →
    valsSz? B vals ≡ true →
    pathSz? S path ≡ true →
    regsSz? B (EvalSt.registry st) ≡ true →
    regsSz? (sizeStep S B)
      (EvalSt.registry (proj₂ (proj₂
        (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≡ true

-- AND THE LEVEL FORM IS THAT FRAME STEP SPENT, NOTHING MORE.  The
-- consumer wants one step of the iterate, because the level is what
-- the depth cascade accumulates down its selection and what the walk
-- factor is denominated in.  The leaf's two caps are exactly the two
-- the iterate already keeps apart -- the program's own `S` and the
-- level reached -- so the step's equation is the whole of this body
-- and no widening is spent in between.  The path is premised at `S`
-- here rather than at the level, which is where the level form is
-- STRONGER than the reading it replaced: a caller standing high up
-- the iterate no longer has to claim its chains grew with it.
foldPath-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S j : ℕ) →
  1 ≤ S →
  valsSz? (iterSize S j S) vals ≡ true →
  pathSz? S path ≡ true →
  regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
  regsSz? (iterSize S (suc j) S)
    (EvalSt.registry (proj₂ (proj₂
      (foldPath sf gas id now envSrc path vals evs fin sched st))))
    ≡ true
foldPath-regsSz sf gas id now envSrc path vals evs fin sched st S j 1≤S hv hp hreg =
  subst (λ z → regsSz? z out ≡ true)
        (sym (iterSize-suc S j S))
        (foldPath-regsLen sf gas id now envSrc path vals evs fin sched st
          S (iterSize S j S) 1≤S (iterSize-infl S 1≤S j S) hv hp hreg)
  where
  out = EvalSt.registry (proj₂ (proj₂
          (foldPath sf gas id now envSrc path vals evs fin sched st)))
