------------------------------------------------------------------
-- KILLING THE DOOR: the evaluator clause that goes, and the family
-- that licenses deleting it.  A sketch — nothing here typechecks and
-- nothing imports it; it is deleted by the commit that makes the change.
------------------------------------------------------------------

-- THE DOOR is `subscribeInner`'s `obsDepthᵉ o <? r`, the one guard in
-- the subscribe cycle that answers a rank with the dry marker.  Its
-- `no` arm is what makes `hasDry` true, which is what makes
-- `rank-sufficient` false, which is Tier 1.

-- THE PREMISE THAT KILLS IT IS A FACT ABOUT THE PROGRAM, AND IT IS
-- CHEAPER THAN ANY CARRIED BOUND.  `o` is a value a frame handed on,
-- and where that frame was a `map-f` the value is `applyFn fn v` — a
-- substitution instance of a subterm of `fn`.  Substituting DATA moves
-- no `strmᵗ`, so `Rx.Obs-Depth.Substitution.obsDepth-applyFn` gives
-- `obsDepthᵉ (applyFn fn v) < obsDepthᵗ fn` outright, with no bound
-- carried in from anywhere.  The door's guard IS that comparison.
--
-- SO THE PREMISE ARRIVES ONE FRAME LOWER THAN THE WHOLE FAMILY WAS
-- AIMED.  `thru-outer-frame-carried` was supposed to be what said an
-- emitted inner is shallow; it is not needed for that — the map below
-- it already established it, and the hop's job is to pass the reading
-- along rather than to establish it.  The carried family is still what
-- the SOURCE-delivered observable needs, and it is now the only thing
-- that needs it.

-- DEAD ROUTE: giving `thru-outer` a rank FIELD ρ, set at install, so
--   the hop re-seeds at a figure the machine owns and its drop is
--   `ρ < suc ρ`.  It does close the arm without a premise, and it
--   relocates the residue to the *All install, where it is a claim about
--   a TERM.  It is dead because it invents a fourth currency for a
--   question three refutations have already priced: the family's axis
--   set is settled, so a mechanism whose whole content is avoiding the
--   family buys a new shelf of statements nothing has instantiated, in
--   place of five whose regions are known.  It is also strictly weaker
--   about the run — ρ is not claimed to dominate the inners, so a wrong
--   ρ is a silent re-seeding rather than a failed obligation.

-- DEAD ROUTE: threading `HandedOK (o ∷ []) τ` into `subscribeInner` as
--   an ARGUMENT and spending it for `ltR`.  It makes the evaluator a
--   proof-carrying function: every caller up to `evaluate` acquires an
--   obligation, and the impl stops mirroring anything a plain rxjs
--   pipeline can do.  That is the one line this repo does not cross.
module Rx.Evaluator.Carried where

open import Data.Bool using (Bool)
open import Data.Nat  using (ℕ; suc)
open import Data.List using (List; [])
open import Data.Product using (_×_; _,_)
open import Induction.WellFounded using (Acc; acc)

open import Rx.Prim using (Tick; Id; InstEvent)
open import Rx.Exp  using (Ty; obs; Ctx; Val; Closed; syncSizeᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Strat-Order using (Tri; _≺_; ltR)
open import Rx.Evaluator using (AllOp; NodeId; Frame; Path; _↠_; from-inner;
  Sched; EvalSt; subscribeE; splitBurst)

variable
  τ  : Tri
  lo : ℕ

------------------------------------------------------------------
-- THE CLAUSE AFTER THE CHANGE.
------------------------------------------------------------------

-- Against the real `subscribeInner`, the diff is three deletions and
-- one substitution: the `with obsDepthᵉ o <? r` goes, the `no` arm and
-- its `close drySource dried ∷ []` go, and the descent witness — which
-- the `yes` branch used to get from the test's own proof — comes from
-- the premise instead.
--
-- THE PREMISE IS AN ARGUMENT HERE AND MUST NOT BE ONE IN THE EVALUATOR.
-- Written this way the clause is route 1, which is dead.  It is spelled
-- out because it is the shape the DOMAIN side already has — the
-- relation's `inner` constructor demands a real sub-derivation, so
-- `subscribeInner⇓-total` proving the machine's result related IS the
-- kill — and what the real evaluator change has to do is make this
-- argument disappear: `r` is the bound the `thru-outer` frame above was
-- entered under, and `hop` is `thru-outer-frame-carried` at that frame,
-- so the fact is available at the call site rather than at this one.
subscribeInner′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {U r s}
                → Acc _≺_ (U , r , s)
                → AllOp → NodeId → Path Γ lo u t → Id → Tick
                → (o : Val Γ (obs u)) → obsDepthᵉ o < r
                → Sched Γ → EvalSt e
                → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t))
                    × Bool × Sched Γ × EvalSt e
subscribeInner′ (acc rec) op allNid κ id now o hop sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE (rec (ltR {r′ = obsDepthᵉ o} {s′ = syncSizeᵉ o} hop))
                   o (from-inner op allNid inst ↠ κ) id now
                   (record sched { nextNode = suc inst }) st
      (vs , bs , done) = splitBurst burst
  in inst , vs , bs , done , sched′ , st′

------------------------------------------------------------------
-- THE ORDER OF OPERATIONS, WHICH IS THE PART WORTH HANDING FORWARD.
------------------------------------------------------------------

-- 1.  PROBE `applyFn-strict`, which is the cheapest thing on this face
--     and the only one that could kill the route in an afternoon.
--     `Probed.Template-Depth` holds the rows, including the one that
--     refutes the UNCONDITIONED form — the data hypothesis is the
--     statement, not a convenience.
-- 2.  Prove `Rx.Obs-Depth.Substitution.obsDepth-subΘ`, which is a
--     clause-for-clause copy of `Rx.Obs-Depth.obsDepth-elimG` with one
--     content-bearing arm.  Then `obsDepth-applyFn` falls out.
-- 3.  Spend it at `map-frame-carried`, which becomes a real body — and
--     the input bound `Pin` leaves four of the five leaves.
-- 4.  `subscribeInner!` then has its premise from the call site, and
--     the clause is written with no `with` at all — the kill, in the
--     builder.  `Refuted.Dry-Wrap` goes red at the cutover and is
--     deleted with it; `make refuted` going red is the signal.
--
-- AND STEPS 4 AND 5 ARE NOT THE TWO HALVES ANYONE THOUGHT (Anthony).
-- Two different things are called killing the door and they schedule
-- OPPOSITELY.  Proving the refusing arm UNREACHABLE is a claim about
-- the machine as it stands, and it comes LAST — the arm is reachable
-- today and three witnesses reach it, so proving otherwise now would be
-- proving something false.  DELETING the arm comes first, and it is not
-- a removal: it is a change of what the recursion is over.  The order
-- is numeric, so every non-structural edge re-establishes it at
-- runtime, and a runtime re-establishment has a negative answer.  A
-- derivation taking each sub-call's own witness as a premise has none
-- to give.
--
-- SO KILLING THE DOOR AND INHABITING THE RELATION ARE ONE OBLIGATION
-- RATHER THAN CONSECUTIVE ONES, which is why this was in the wrong
-- place for a structural reason and not by a priority call: to BUILD a
-- derivation at a hop you must show the guard's positive branch is
-- taken, and that is exactly spending the report at the hop site.
-- `Verify-Rank-Sufficient.Doorless` is that builder.
--
-- WHAT STAYS OPEN AFTER ALL FIVE, AND IT IS SMALLER THAN THE TIER WAS.
-- A template's output is priced by the program; a SOURCE's output is
-- not, and neither is a FOLD's, whose accumulator is fed back through a
-- non-data environment.  Those two are the residue, and they are the
-- two the carried family was always genuinely for.
