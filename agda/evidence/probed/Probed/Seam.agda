----------------------------------------------------------------------
-- THE PROTOCOL FACE'S SEAM, AT THE ONLY PROGRAMS THAT REDUCE.
--
-- WHAT THE CARVE MADE INSTANTIABLE, which is the whole reason this
-- file can exist.  The fused predecessor asserted a verdict about a
-- CONCATENATION and named nothing between its two ends, so a program
-- could decide the verdict and never the mechanism.  Both leaves below
-- carry the automaton's state at the seam and the relation it stands in
-- to the evaluator's, and all of that computes: the fold is a left fold
-- over a list the builder produces, and the relation's five fields are
-- decidable equalities and a bound.
--
-- SO A ROW HERE DECIDES THE SEAM, NOT THE VERDICT.  A relation with a
-- field that is wrong at the root frame — a horizon minted rather than
-- inherited, an instant opened with something owed, a registry the live
-- multiset does not shadow — fails at this program, and the sampling
-- sweep that covered the predecessor could not have seen any of it.
--
-- AND THE DERIVATION IS THE BUILDER'S ONLY BY CONVENIENCE HERE, which
-- is the one axis this file improves on that sweep: the rows are read
-- off `subscribeE!` and `drain!` directly rather than off a whole run,
-- so the leaf's quantification over an arbitrary derivation is
-- exercised by two builders rather than by one composite.  It is still
-- not the arbitrary one; `evaluate-deterministic` is the fact that
-- would close that.
--
-- NOT REACHED: every flattening program, since the frame dispatch hands
-- a `thru-outer` frame to a live postulate and no `refl` decides
-- anything past it; any source at all, so the drain row below is read
-- at an EMPTY schedule and decides the drain's exit rather than its
-- step; any type other than `natᵗ`; any context but the empty one,
-- which is also what makes the schedule's well-typedness field
-- vacuously true here rather than checked.

-- TARGET: subscribeE-root-wf @999a3b
-- TARGET: drain-wf @c4f5d7
module Probed.Seam where

open import Data.List using (_∷_; [])
open import Data.Vec using ([])     -- contexts are Vecs; ∷/[] overload per type
open import Data.Nat using (z≤n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; ofᵉ)
open import Rx.Evaluator using (root; sched-init; st-init)
open import Rx.Evaluator.Builder using (Runs; subscribeE!; drain!)
open import Readme-Theorems using (noSlots)
open import Verify-Well-Formed using (subscribeE-root-wf; drain-wf)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

-- TWO VALUES IN ONE SUBSCRIBE BURST, which is the smallest shape whose
-- burst is more than a single envelope: a relation that counted the
-- instant's emits rather than its registrations parts from the
-- automaton here and not at a one-value program.
pair₀ : Closed Γ₀ natᵗ
pair₀ = ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])

----------------------------------------------------------------------
-- 1.  THE ROOT FRAME REACHES THE SEAM.  LOAD-BEARING on all four of
-- the relation's non-vacuous fields at once: the burst must drive the
-- automaton to a state at all (a subscribe frame that owed something
-- leaves the fold in `nothing` and no witness exists), that state's
-- live multiset must shadow the registry, its horizon must not have
-- run ahead of the frame's own id, and its open instant must be the
-- frame's with nothing owed.
----------------------------------------------------------------------

sub₀ : Runs {e = pair₀} {lo = 0} pair₀ root 0 0 (sched-init pair₀ noSlots) (st-init pair₀)
sub₀ = subscribeE! noSlots pair₀ root 0 0 (sched-init pair₀ noSlots) refl
         (st-init pair₀)

row-root : Confirms (subscribeE-root-wf {e = pair₀} noSlots (proj₂ sub₀))
row-root = _ , refl , record
  { live-matches  = λ s _ → refl
  ; reg-typed     = refl
  ; horizon-low   = z≤n
  ; current-frame = inj₂ refl
  ; hot-live      = λ ()
  }

----------------------------------------------------------------------
-- 2.  THE DRAIN LEAVES THE AUTOMATON PAID UP.  DEGENERATE on the
-- induction and LOAD-BEARING on its exit: this program schedules no
-- source, so the drain emits nothing and the row decides that the seam
-- state is ALREADY paid up rather than that any step preserves it.  A
-- relation admitting a state with an unsettled instant fails here,
-- which is the half worth having at a source-free program; the
-- stepping half is not reached and needs a scheduled source.
--
-- AND THE STATE IS THE ONE THE ROW ABOVE PRODUCED, which is what stops
-- this row being read against a state the machine cannot reach.  Both
-- the automaton's seam state and the evaluator's are projected out of
-- the root row and the subscribe builder respectively, so nothing here
-- is hand-built and the two rows compose into the run this face's
-- top line is about.
----------------------------------------------------------------------

row-drain : Confirms (drain-wf {e = pair₀} 1 (proj₂ (proj₂ row-root))
  (proj₂ (drain! 1 1 (proj₁ (proj₂ (proj₁ sub₀))) (proj₂ (proj₂ (proj₁ sub₀))))))
row-drain = _ , refl , refl
