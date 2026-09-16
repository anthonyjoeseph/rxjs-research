-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN.  `The-Proof` draws `evaluate-well-formed` and nothing else from
-- this face: a canonical run's emit stream is accepted by the protocol
-- automaton, which is what lets the batcher be quantified over
-- WellFormed streams rather than arbitrary ones.
--
-- AND IT IS A BODY OVER THE DENOTATION, WHICH IS WHAT ORDERS THE TIERS
-- (Anthony).  A run is a PREFIX of a program's meaning -- that is
-- adequacy, and it is the only thing in the repo carrying a fact about
-- a PROGRAM down onto an arbitrary fuel's run.  Stating this face as a
-- body over it makes the dependence checked rather than asserted: the
-- domain is what well-formedness is proven FROM, so the domain finishes
-- first, and a domain that cannot carry the predicate is a finding here
-- rather than a preference.
--
-- WHY THE SEAM ROUTE IS NOT THE ONE.  A seam argument re-establishes a
-- relation between an automaton, a scheduler and an eval state at every
-- step, in a currency carrying node ids and a drain counter; the
-- denotational one is an induction on SYNTAX, one clause per former, in
-- a currency with none of that in it.  The second is what the batching
-- claim above wants, since the property it needs is of a bare emit
-- list.
module Verify-Well-Formed where

open import Data.List using (_++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (WellFormed)
open import Verify-Adequacy using (meaning; adequacy)

-- THE ONE LEAF, AND IT IS QUANTIFIED OVER EVERY PREFIX RATHER THAN
-- STATED AT THE MEANING.  That is not a convenience: the descent has to
-- land at an ARBITRARY fuel's stopping point, and only a
-- prefix-quantified statement reaches one.  It is also where the tier's
-- whole remaining risk sits, since nothing has instantiated it -- the
-- sweep below is evidence about the body's conclusion, not about this.
--
-- DEAD ROUTE: descending from a well-formed meaning to a well-formed
--   run along `WellFormed` ITSELF.  Structurally blocked by the final
--   check: `WellFormed` applies it to the LAST state, so it is not
--   prefix-closed, and an adequacy conclusion is a PREFIX -- the
--   property does not travel down.  It is the descent along that
--   predicate that is dead, and the statement below is the different
--   one it rules in rather than out.
postulate
  meaning-prefix-well-formed :
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
      (pre rest : Stream Γ t) →
    meaning e ins ≡ pre ++ rest →
    WellFormed pre

-- THE BODY, AND ITS ONE MOVE IS ELIMINATING ADEQUACY'S WITNESS.  The
-- remainder adequacy hands back is exactly what the leaf's `rest` wants,
-- so the composition reduces rather than being asserted -- which is what
-- makes a domain unable to supply the leaf show up as a type error here.
--
-- A sampling sweep of 6200 programs over two depths, about a third
-- carrying `μᵉ`, found no refutation of this conclusion; the harness's
-- `wellFormed?` is the same computation `WellFormed` is, pinned to
-- `git show a0d882c6:agda/src/QuickCheck.agda`.  Every row sits at a
-- derivation the BUILDER produced, while the statement quantifies over
-- any at its indices -- `evaluate-deterministic` is the fact that would
-- make those the same set.

-- RECOVERY: git show 081328b0:agda/src/Verify-Well-Formed.agda restores
--   the seam carve -- two leaves meeting at a named automaton state, the
--   `BurstInv` relation they were denominated in, and `Glue`'s fold law
--   composing their conclusions.
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate↓ fuel e ins)
evaluate-well-formed fuel e ins with adequacy fuel e ins
... | rest , eq = meaning-prefix-well-formed e ins (evaluate↓ fuel e ins) rest eq
