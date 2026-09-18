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
-- A ROW IS AN AUTHOR'S PROGRAM, AND THE HARNESS ROOT IS WHAT MAKES IT
-- ONE RUN.  Batching reads the protocol off an ENVELOPE, and only an
-- elaborated program carries one, so a row holds an `SExp` and the
-- three steps between it and a verdict -- elaborate, cap, decode -- sit
-- here rather than in either harness.  Sharing them is not tidiness: a
-- cached row and the seed that found it have to be the same run, and a
-- cap applied in one place and not the other is two.
--
-- WHAT IS NOT HERE, DELIBERATELY: a predicate for a run that went DRY.
-- No builder constructs the marker, so a dry run is not a disagreement
-- between two implementations of one batching — it is the descent
-- refusing, which the QuickCheck binary reports unpasteably, and it
-- stays out of a corpus whose verdict gates the build.
------------------------------------------------------------------
module Implementation.Unit-Test.Prelude where

open import Data.Bool using (Bool)
open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; takeᵉ; nat̂)
open import Rx.SExp using (SExp; emitᵗ; emitᵛ)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (Slots)
open import Rx.Protocol using (wellFormed?)
open import Rx.Emit-Eq using (eqBatched)
open import Implementation using (impl-batchSimultaneous)
open import Spec using (spec-batchSimultaneous)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- envelope over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

Γ₂ᵉ : Ctx 2
Γ₂ᵉ = emitᵛ Γ₂

-- one cached counterexample: a label, and the run that produced it
record Case : Set where
  constructor cached
  field
    name  : String
    fuel  : ℕ
    prog  : SExp Γ₂ [] [] [] natᵗ
    slots : Slots Γ₂ᵉ

open Case using (name; fuel; prog; slots)

-- THE ROOT CAP, AND IT IS WHAT MAKES A SWEEP FINITE AT ALL.  A guarded
-- fixpoint whose step hands back more than it was given costs the fuel
-- as an EXPONENT, and nothing in a generator declines to draw one.  A
-- budget on the emitted stream cannot retire that, because the cost is
-- inside one cascade rather than in the stream's spine, so the budget
-- is only reached by paying for it; a `takeᵉ` cuts instead, since it
-- unsubscribes the fixpoint.
--
-- IT IS A PLAIN FORMER OVER THE ELABORATED PROGRAM, AND IT HAS TO BE.
-- The author's palette has no `take` at all, so there is nothing to cut
-- with on the simul side; above the elaboration the count is in
-- ENVELOPES rather than in values, which is a coarser cut than the
-- author's would have been and is the right one here -- what has to be
-- bounded is how much of the run the harness performs, and an envelope
-- is one delivery.
capProg : Closed Γ₂ᵉ (emitᵗ natᵗ) → Closed Γ₂ᵉ (emitᵗ natᵗ)
capProg e = takeᵉ (nat̂ 24) e

-- the run a row names: the author's program elaborated, capped, driven
-- by the slot table, and decoded back to the envelope stream both
-- batchings read
runOf : Case → List (InstEmit (Val Γ₂ᵉ natᵗ))
runOf c = decodeStream {Γ = Γ₂ᵉ} {a = natᵗ}
            (evaluate↓ (fuel c) (capProg (elaborate (prog c))) (slots c))

-- the decoded stream must satisfy the protocol automaton
-- (evaluate-well-formed, cached case by case)
wellFormed : Case → Bool
wellFormed c = wellFormed? (runOf c)

-- impl and spec, fed the SAME stream, must batch it identically
agrees : Case → Bool
agrees c = eqBatched (impl-batchSimultaneous (runOf c))
                     (spec-batchSimultaneous (runOf c))
