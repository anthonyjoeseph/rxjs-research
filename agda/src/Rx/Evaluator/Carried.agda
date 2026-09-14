------------------------------------------------------------------
-- KILLING THE DOOR: the evaluator clause that goes, and the family
-- that licenses deleting it.  A sketch — nothing here typechecks and
-- nothing imports it; it is deleted by the commit that makes the change.
------------------------------------------------------------------

-- THE DOOR is `subscribeInner`'s `obsDepthᵉ o <? r`, the one guard in
-- the subscribe cycle that answers a rank with the dry marker.  Its
-- `no` arm is what makes `hasDry` true, which is what makes
-- `rank-sufficient` false, which is Tier 1.

-- THE PREMISE THAT KILLS IT IS NOT A NEW MECHANISM — IT IS THE CARRIED
-- FAMILY, SPENT.  `o` is a value a `thru-outer` frame was handed, and
-- `Verify-Rank-Sufficient.Push-Carried.thru-outer-frame-carried` is
-- exactly the statement that such a value is written strictly shallower
-- than the bound the frame was entered under.  So the arm is unreachable
-- the moment that shelf holds, the clause can be deleted, and
-- `Refuted.Dry-Wrap` goes red — which is what the tier's close looks
-- like as a machine event.  Nothing has to be INVENTED here; the axis
-- set the family needs is already known and stated in one pass.

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

-- 1.  State the five frames at the full axis set — done, in
--     `Verify-Rank-Sufficient.Push-Carried`.  Until that block holds,
--     nothing below it is worth starting.
-- 2.  Discharge `thru-outer-frame-carried` first of the five.  It is the
--     only one the door needs, and it is the one whose region the two
--     `Refuted.Carried-*` witnesses already map.
-- 3.  `subscribeInner⇓-total` then has its premise from the call site,
--     and the `no` arm dies by `⊥-elim` — the kill, in the relation.
-- 4.  ONLY THEN delete the clause from `Rx.Evaluator`, which is what
--     makes `hasDry` false of the machine rather than of the relation.
--     `Refuted.Dry-Wrap` goes red in that same commit and is deleted
--     with it; `make refuted` going red is the signal, not a problem.
--
-- Steps 3 and 4 are the two halves people conflate, and the order
-- matters: deleting the clause first leaves the evaluator with a hole
-- where the descent witness was, and the premise is the only thing that
-- fills it.
