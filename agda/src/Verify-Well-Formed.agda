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
open import Rx.Exp using (Ctx; Closed)
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
--
-- DEAD ROUTE: obtaining this from a well-formed denotation, by
--   quantifying a leaf over every prefix of a program's meaning and
--   instantiating it at the run.  That route was stated against the
--   conjunction, whose final check demands settledness AT THE CUT, and
--   an instant's obligations span several emits, so a cut between them
--   is rejected.  What is true of an arbitrary prefix is this
--   statement ALONE, which needs no domain to say.

-- RECOVERY: git show 9f5e3339:agda/src/Verify-Well-Formed.agda restores
--   the seam carve -- two leaves meeting at a named automaton state, the
--   `BurstInv` relation they were denominated in, and `Glue`'s fold law
--   composing their conclusions.
postulate
  evaluate-accepted :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    Accepted (runProtocol protocol-init (evaluate↓ fuel e ins))
