-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN.  `The-Proof` draws `evaluate-accepted` and nothing else from
-- this face: no emit of a canonical run is rejected by the protocol
-- automaton, which is what lets the batcher be quantified over legal
-- streams rather than arbitrary ones.
--
-- AND ACCEPTANCE IS THE WHOLE OF WHAT IS OWED (Anthony, asking for a
-- claim that does not read the evaluator).  This face used to owe a
-- second half — that a run stops on an instant boundary, every
-- obligation paid — and `batch-agreement` never had a use for it: it
-- took the conjunction and immediately weakened it back to acceptance.
-- A statement about where the MACHINE stops is the one thing here that
-- could not be restated over the stream, so retiring it is what leaves
-- this face saying something about a stream's contents alone.
module Verify-Well-Formed where

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; uniqᵗ)
open import Rx.Envelope using (instEmitᵗ)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (protocol-init; runProtocol; Accepted)

-- Every clause the automaton checks — instant freshness, bracketing,
-- fan-out exactness, complete discipline — is a promise the evaluator
-- makes while producing the stream, so this is the half that is
-- structural in how the run is BUILT.  It is also prefix-closed, since
-- `runProtocol` short-circuits on rejection, which is what makes it
-- the half a compositional reading could ever descend through.
--
-- A sampling sweep of 6200 programs over two depths, about a third
-- carrying `μᵉ`, found no refutation of the conjunction this was a
-- half of; the harness's `wellFormed?` is a decision procedure for
-- that conjunction, pinned to `git show a0d882c6:agda/src/QuickCheck.agda`.
-- Every row sits at a derivation the BUILDER produced, while the
-- statement quantifies over any at its indices --
-- `evaluate-deterministic` is the fact that would make those the same
-- set.

-- AND THE SEGMENT DECOMPOSITION IS NOT PART OF IT, BECAUSE THE PLAIN
-- CARRIER PUT THE PROTOCOL BEYOND THE MACHINE'S REACH.  While the
-- evaluator MINTED the envelope, an instant was the machine's to
-- choose and a per-segment soundness claim was the machine's to keep.
-- With the protocol riding on the values, elaboration mints at a
-- SOURCE former and passes an `input` through untouched, so a scripted
-- slot's value IS the envelope -- and `isData` admits the envelope
-- type, so such a slot is writable.  A table scripted to an instant
-- past the counter, or to values with no `init`, reaches the output
-- verbatim.  What acceptance is missing is a hypothesis that the SLOT
-- TABLE is protocol-valid: the well-formedness obligation has moved
-- from the machine to whoever supplies the inputs, and where that
-- hypothesis belongs is the simul tree's question rather than this
-- face's.
-- DEAD ROUTE: obtaining this from a well-formed denotation, by
--   quantifying a leaf over every prefix of a program's meaning and
--   instantiating it at the run.  That route was stated against the
--   conjunction, whose final check demands settledness AT THE CUT, and
--   an instant's obligations span several emits, so a cut between them
--   is rejected.  What is true of an arbitrary prefix is this
--   statement ALONE, which needs no domain to say.
-- DEAD ROUTE: recovering soundness by strengthening an evaluator
--   clause, or by carving the run into segments and composing them.
--   The counterexample never enters a clause -- the value is opaque to
--   every rule that moves it -- so no induction over the machine can
--   see it, and a decomposition inherits the defect segment by
--   segment.
-- RECOVERY: git show d465f023:agda/src/Rx/Protocol/Sound.agda restores
--   the segment predicate, its `++` composition law and the root
--   instantiation that turned a sound run into an accepted one; the
--   same sha's `Verify-Well-Formed` holds the drain induction that
--   spent them, and its `Rx/Envelope/Decode.agda` the `++` law of the
--   decode that the composition needed.
postulate
  evaluate-accepted :
    ∀ {n} {Γ : Ctx n} {u} (fuel : Fuel) (e : Closed Γ (instEmitᵗ uniqᵗ u))
      (ins : Slots Γ) →
    Accepted (runProtocol protocol-init (decodeStream (evaluate↓ fuel e ins)))
