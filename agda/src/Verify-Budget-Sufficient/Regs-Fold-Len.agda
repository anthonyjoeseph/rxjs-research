-- THE FOLD'S REGISTRY PRICE, READ AS A LENGTH AND NOT AS A LEVEL.
-- What a level has to cover here is one quantity: the LONGEST SINGLE
-- registration the fold leaves behind.  `regsSz?` is an `all` over the
-- registry, so the price is per ENTRY -- many short entries cost what
-- one costs, and only a single entry getting longer can move it.  A
-- subscribing frame lengthens no standing entry; it swaps its own head
-- for a `from-inner` and registers a NEW chain carrying one frame per
-- operator of the inner it received.
--
-- SO THE PRICE IS A DOUBLING, AND THAT IS WHY THE STEP IS COMFORTABLE
-- RATHER THAN TIGHT.  A registered chain is the walked path plus the
-- inner's own count.  The walked half is capped by `pathSz?`, whose
-- length conjunct is the only unbounded one; the inner half is capped
-- by the values' size premise, `sizeᵛ` at an observable being `sizeᵉ`.
-- Both sit under the entry budget, so the registration is bounded by
-- the budget twice over -- while one `sizeStep` buys `S·(1+2B)`, which
-- exceeds `B+B` at every `1 ≤ S`.  Stating the leaf in the LENGTH
-- currency is what makes that margin visible: the level form hides a
-- doubling inside an exponential and reads as though the two were the
-- same claim.
module Verify-Budget-Sufficient.Regs-Fold-Len where

open import Data.Bool using (Bool; true)
open import Data.List using (List)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; n≤1+n;
  +-identityʳ; *-identityˡ; *-monoˡ-≤)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator using (Sched; EvalSt; Path; foldPath; iterSize; sizeStep)
open import Verify-Budget-Sufficient.Caps using (iterSize-suc)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; regsSz?; regsSz?-widen)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

-- THE MARGIN, MADE CHECKED RATHER THAN ARGUED.  One step of the level
-- buys strictly more than the doubling the registration costs, and it
-- does so at the smallest base the caps invariant admits -- so nothing
-- about the arithmetic depends on the base being generous.
dbl≤sizeStep : ∀ (S B : ℕ) → 1 ≤ S → B + B ≤ sizeStep S B
dbl≤sizeStep S B 1≤S =
  ≤-trans (≤-reflexive (sym (twice B)))
    (≤-trans (n≤1+n (2 * B))
      (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * B)))))
               (*-monoˡ-≤ (suc (2 * B)) 1≤S)))
  where
  twice : ∀ (b : ℕ) → 2 * b ≡ b + b
  twice b = cong (b +_) (+-identityʳ b)

-- WHAT THE FOLD LEAVES REGISTERED, AT THE ONE CONJUNCT THAT CAN MOVE.
-- The count is DETERMINED -- one call, one doubling -- rather than a
-- witness chosen after the fact, and nothing in it is denominated in
-- the path's length or in how deep a sink re-enters.  Both of the
-- fold's re-entries are inside this claim: rootward through the frames
-- and sideways at a share, where it and `dispatchShare` are mutually
-- recursive and every admitted chain re-enters with its own
-- continuation.
--
-- REFUTED: `Refuted.Chain-Step-Regs-Cap` -- the fixed-cap form this
--   replaces, at a five-node inner and a six-frame chain against a cap
--   of six.  Both premises hold and the registered chain has length
--   eight, so what broke was the length ledger rather than any size
--   reading, and no further hypothesis repairs it.
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
--   through the frame arm, which is the repair the doubling above
--   invites.  A frame INFLATES the values it passes on -- the size
--   ledger takes them a level per frame -- so a fold whose statement
--   fixes one budget for the values cannot hand that budget to its own
--   recursion.  What survives is the reading here, where the values
--   are premised once at entry and the registered length is bounded
--   against that reading rather than against the values the walk
--   later carries.
--
-- PROBED: `Probed.Chain-Step-Regs-Level` -- the ROOTWARD re-entry, over
--   a stack of one to eight `mergeAllᵉ` flattens whose sources are each
--   other, every figure read off a state the evaluator reached and
--   every depth pinned to the arm that measures a real `chainStep`.
--   The registered length grows by exactly ONE per flatten level while
--   the inner's own size grows by four, so the descent does not recurse
--   and the one axis that could refute this form is closed along that
--   route.  NOT COVERED: the SIDEWAYS re-entry at a `share-sink`, which
--   `Probed.Chain-Step-Regs-Share` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Share` -- the SIDEWAYS re-entry, where
--   `foldPath` and `dispatchShare` are mutually recursive and the depth
--   is the share telescope rather than the syntax.  One five-slot
--   context, a scripted driver at slot zero and four `mergeAllᵉ` shares
--   above it, rooted at each of the five slots in turn, so one arrival
--   crosses zero to four share boundaries inside a single `chainStep`.
--   Every row is pinned to the arm that measures a real step, and the
--   step's emit count is read alongside the lengths: it is the crossing
--   count plus one at every depth, so the telescope is entered and not
--   merely built.  The maximum registered path length is TWO before the
--   step and two after it at every one of the five depths -- the
--   sideways route lengthens no registered path at all, while the
--   registry count tracks the telescope and is unchanged across the
--   step.  NOT COVERED: a telescope deeper than four, and a share
--   fanning out to more than one chain, which
--   `Probed.Chain-Step-Regs-Fan` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Fan` -- the DIAMOND, the share shape
--   both re-entry sweeps left out: each of them fans every share to
--   exactly one registered chain and so measures a share as a relay.
--   Width is varied in the PROGRAM rather than in the telescope, `w`
--   branches of the root reading one `input`, over three slots at
--   widths one to four; and two further rows put a width-`w` fan over
--   a share whose own def is a two-way fan, which is where width
--   compounds with depth.  The emit count separates a relay from a
--   fan outright and reads as the fan: the compounded rows deliver
--   twice their width, not their width.  The maximum registered path
--   length is THREE before the step and three after it in every row,
--   width one through four and compounded alike -- so a fan multiplies
--   registry ENTRIES and the emit stream, and lengthens no entry.
--   NOT COVERED: the operator KIND at the frames of a sinking chain,
--   which `Probed.Chain-Step-Regs-Cut` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Cut` -- the CUTTING arm, against a
--   flatten control of the same shape.  A `takeᵉ` whose count expires
--   on the stepped arrival, at the leaf and again on the def of a share
--   so the cut sits BETWEEN two sinks; plus a mixed row where one
--   branch of a width-two share cuts and the other survives, which is
--   where `shareGo`'s ordering is observable.  No cut leaves a longer
--   entry registered than the control does: the cut rows come back
--   SHORTER, and the survivor of the mixed row sits at exactly the
--   control's length.  NOT COVERED, and the rows say so themselves:
--   `switchAllᵉ` and `exhaustAllᵉ` read identical to the control
--   because a FIRST arrival gives neither anything to cut, so their
--   real arm needs a second `chainStep`; and every row that does cut
--   SHRINKS the registry, which satisfies a growth bound whatever the
--   frames did -- those rows are evidence about the length conjunct
--   alone, which is the only unbounded one but not the only one.
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
--   row, the share-def cut included.  NOT COVERED: the inner never
--   fires, so no arrival ever comes FROM one -- which
--   `Probed.Chain-Step-Regs-Inner` takes up -- and what an abandoned
--   inner's own delivery would do after its registration is dropped is
--   unmeasured.
--
-- PROBED: `Probed.Chain-Step-Regs-Inner` -- the arrival that comes FROM
--   an inner, which is the re-entry every sweep above steps past: all
--   of them step an outer's arrival, and an inner registered by a
--   flatten re-enters `foldPath` mid-flight, carrying the sighted path
--   the outer built.  It is the second-arrival sweep's program with one
--   line of its script changed -- the inner is due BETWEEN two outer
--   values instead of past them all -- and the shift is pinned by a
--   provenance CONTRAST rather than by a bare number: the stepped
--   arrival's source differs from the first arrival's under the
--   retiming and equals it under the sibling's timing, so the two
--   readings together say the door was entered at an inner.  Registered
--   length comes back no longer than the same program's flatten control
--   at the same step, on every arm -- so the one unbounded conjunct is
--   not lengthened by the frames a mid-flight path arrives carrying.
--   NOT COVERED: one level of nesting, so an arrival from an inner OF
--   an inner is not reached; the inner is a bare slot read, so nothing
--   here carries operators of its own into the registered chain, which
--   is the quantity `Refuted.Chain-Step-Regs-Cap` moves; and the
--   stepped arrival is the SECOND overall, so a door met after several
--   inner deliveries have landed is unmeasured.
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
postulate
  foldPath-regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B : ℕ) →
    valsSz? B vals ≡ true →
    pathSz? B path ≡ true →
    regsSz? B (EvalSt.registry st) ≡ true →
    regsSz? (B + B)
      (EvalSt.registry (proj₂ (proj₂
        (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≡ true

-- AND THE LEVEL FORM IS THAT LENGTH READING SPENT, NOTHING MORE.  The
-- consumer wants one step of the iterate rather than a doubling,
-- because the level is what the depth cascade accumulates down its
-- selection and what the walk factor is denominated in.  So the whole
-- of this body is the margin above, applied at the level the caller
-- happens to be standing on, and the step's own equation is what
-- carries it across.
foldPath-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S j : ℕ) →
  1 ≤ S →
  valsSz? (iterSize S j S) vals ≡ true →
  pathSz? (iterSize S j S) path ≡ true →
  regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
  regsSz? (iterSize S (suc j) S)
    (EvalSt.registry (proj₂ (proj₂
      (foldPath sf gas id now envSrc path vals evs fin sched st))))
    ≡ true
foldPath-regsSz sf gas id now envSrc path vals evs fin sched st S j 1≤S hv hp hreg =
  subst (λ z → regsSz? z out ≡ true)
        (sym (iterSize-suc S j S))
        (regsSz?-widen out (dbl≤sizeStep S (iterSize S j S) 1≤S)
          (foldPath-regsLen sf gas id now envSrc path vals evs fin sched st
            (iterSize S j S) hv hp hreg))
  where
  out = EvalSt.registry (proj₂ (proj₂
          (foldPath sf gas id now envSrc path vals evs fin sched st)))
