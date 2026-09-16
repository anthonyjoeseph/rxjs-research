-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN.  `The-Proof` draws `evaluate-well-formed` and nothing else from
-- this face: a canonical run's emit stream is accepted by the protocol
-- automaton, which is what lets the batcher be quantified over
-- WellFormed streams rather than arbitrary ones.
--
-- AND IT IS A BODY OVER THE TWO HALVES `WellFormed` IS COMPOSED OF.
-- `Rx.Protocol` splits the predicate where it actually divides: the
-- automaton run, which is prefix-closed, and the final check, which
-- reads the last state and is not.  Each half is owed separately here,
-- and both are owed of the RUN — so both reduce at a concrete program,
-- which the single statement they replace did not.
module Verify-Well-Formed where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (WellFormed; ProtocolSt; protocol-init; runProtocol;
  paidUp; Accepted; wellFormed-settled)

-- THE AUTOMATON HALF: no emit of a run is ever rejected.  Every clause
-- the automaton checks — instant freshness, bracketing, fan-out
-- exactness, complete discipline — is a promise the evaluator makes
-- while producing the stream, so this is the half that is structural
-- in how the run is BUILT.
--
-- DEAD ROUTE: obtaining this half from a well-formed denotation, by
--   quantifying a leaf over every prefix of a program's meaning and
--   instantiating it at the run.  `WellFormed` of a prefix demands the
--   final check AT THE CUT, and an instant's obligations span several
--   emits — `handoff` bumps owed and later deliveries pay it off, which
--   is what `paidOff` exists to close — so a cut between them is
--   rejected.  The prefix-quantified statement is therefore false at
--   every instant with more than one emit, and what is true of an
--   arbitrary prefix is the automaton half ALONE, which is
--   `runProtocol-prefix` and needs no domain to say.
postulate
  evaluate-accepted :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    Accepted (runProtocol protocol-init (evaluate↓ fuel e ins))

-- THE SETTLEDNESS HALF: a run stops on an instant boundary, with every
-- obligation paid.  This is a fact about where `evaluate↓` may CUT
-- rather than about what it emits, and it is the whole of what the
-- final check needs.  It is also where this face's remaining risk
-- sits: an off-by-one between the point a budget is spent and the
-- point a cut is emitted is a counterexample rather than a hard proof.
postulate
  evaluate-settled :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
      (ps : ProtocolSt) →
    runProtocol protocol-init (evaluate↓ fuel e ins) ≡ just ps →
    paidUp ps ≡ true

-- THE BODY, AND ITS ONE MOVE IS RECOMPOSING THE PREDICATE.  Neither
-- half is `WellFormed` and together they are exactly it, so a leaf that
-- does not suffice shows up as a type error here rather than as a
-- statement nobody can instantiate.
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
evaluate-well-formed fuel e ins =
  wellFormed-settled (evaluate↓ fuel e ins)
    (evaluate-accepted fuel e ins)
    (evaluate-settled fuel e ins)
