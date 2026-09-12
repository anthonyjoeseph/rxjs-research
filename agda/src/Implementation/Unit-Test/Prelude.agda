------------------------------------------------------------------
-- THE BUG CACHE'S SHARED VOCABULARY: what a cached case IS, now that a
-- case is a value rather than a type.
--
-- A CASE IS A PROGRAM, AND BOTH PROPERTIES ARE CHECKED OF IT.  Each
-- entry used to be a `refl` pinning one predicate of one run, which put
-- the run inside the TYPECHECKER: a case cost minutes, so the two
-- predicates were two separate types and a program found to violate one
-- was never asked about the other.  Compiled, the run is a function
-- call and asking twice is free -- so a row names a program, and every
-- row is held to both.  That is strictly more than the cache used to
-- carry: a program cached for a protocol violation now also guards
-- agreement, which is the property the whole campaign is about.
--
-- WHY THE PREDICATES ARE BOOLEANS RATHER THAN EQUATIONS.  Agreement is
-- stated on the BATCHED streams, whose payloads are lists of naturals,
-- and it is settled by `Rx.Emit-Eq` -- the same family the QuickCheck
-- binary already decides agreement with, so a cached case and the seed
-- that found it are answering one question.  Well-formedness is already
-- a boolean at the protocol automaton, so there was never an equation
-- there to lose.
--
-- WHAT IS NOT HERE, DELIBERATELY: a predicate for a run that went DRY.
-- A dry run refutes `rank-sufficient`, which is a postulate rather than
-- a disagreement between two implementations of one batching, so the
-- QuickCheck binary reports it unpasteably and it stays out of a corpus
-- whose verdict gates the build.
------------------------------------------------------------------
module Implementation.Unit-Test.Prelude where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)

open import Rx.Exp using (Ctx; Closed; natᵗ)
open import Rx.Evaluator using (evaluate)
open import Rx.Slots using (Slots)
open import Rx.Protocol using (wellFormed?)
open import Rx.Emit-Eq using (eqBatched)
open import Implementation using (impl-batchSimultaneous)
open import Spec using (spec-batchSimultaneous)

-- the QuickCheck's fixed context: two nat-typed slots
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- one cached counterexample: a label, and the run that produced it
record Case : Set where
  constructor cached
  field
    name  : String
    fuel  : ℕ
    prog  : Closed Γ₂ natᵗ
    slots : Slots Γ₂

open Case using (name; fuel; prog; slots)

-- the evaluator's raw output must satisfy the protocol automaton
-- (evaluate-well-formed, cached case by case)
wellFormed : Case → Bool
wellFormed c = wellFormed? (evaluate (fuel c) (prog c) (slots c))

-- impl and spec, fed the SAME evaluate output, must batch it identically
agrees : Case → Bool
agrees c = eqBatched (impl-batchSimultaneous run) (spec-batchSimultaneous run)
  where run = evaluate (fuel c) (prog c) (slots c)
