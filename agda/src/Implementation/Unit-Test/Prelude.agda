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
open import Data.List using (List; []; concat)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; listᵗ; emptyᵉ; takeᵉ; nat̂)
open import Rx.SExp using (SExp; emitᵗ; plainᵛ)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Palette using (plainPalette)
open import Rx.Evaluator.Builder plainPalette using (evaluate↓)
open import Rx.Slots plainPalette using (Slots; shared)
open import Rx.Protocol using (wellFormed?)
open import Rx.Emit-Eq using (eqBatched)
open import Rx.Batch using (batchSimultaneousᵖ)
open import Spec using (spec-batchSimultaneous)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- envelope over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

Γ₂ᵉ : Ctx 2
Γ₂ᵉ = plainᵛ Γ₂

-- THE TELESCOPE IS EMPTY OBSERVABLES, AND THAT IS A BLOCKAGE RATHER
-- THAN A CHOICE.  An elaborated program's slots stand at the ENVELOPE,
-- so the two shapes a `Slot` offers are a script -- which would be
-- writing source and instant tokens by hand, the one thing the palette
-- exists to make unsayable -- and a `shared` def, which has to be an
-- elaborated program to carry an envelope honestly.  The def route is
-- what is blocked: the stratification field asks for
-- `T (inputsBelowᵉ k d)` to compute, and `d` is a real body over
-- POSTULATED leaves, so the walk hits a postulate at the first former
-- and gets stuck for every elaborated `d`, at every `k`.  `emptyᵉ` is a
-- constructor and reduces, so it is the one def this table can state,
-- and every `inputˢ` a program draws therefore reaches a source that
-- never emits.
--
-- WHAT THAT COSTS THE SWEEP, and it is worth knowing before reading a
-- green: no hot or cold source, so no asynchronous arrival, so the
-- whole timing axis is uncovered -- what remains is the synchronous
-- one, where every value enters through an `ofˢ`.  The blockage lifts
-- on its own the day the elaboration's leaves become definitions.
slots₂ : Slots Γ₂ᵉ
slots₂ _ = shared emptyᵉ

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
-- AND IT IS A PLAIN FORMER OVER THE ELABORATED PROGRAM RATHER THAN THE
-- AUTHOR'S `takeˢ`, WHICH CUTS AT THE WRONG LEVEL FOR THIS JOB.  A
-- `takeˢ` counts the author's VALUES, so a program whose every value
-- arrives in one envelope is not bounded by one at all; above the
-- elaboration the count is in ENVELOPES, and an envelope is one
-- delivery -- which is the quantity the harness's cost is linear in.
-- The cap is a harness budget and not part of any program a row names,
-- so it belongs above the elaboration on those grounds too.
capProg : Closed Γ₂ᵉ (emitᵗ natᵗ) → Closed Γ₂ᵉ (emitᵗ natᵗ)
capProg e = takeᵉ (nat̂ 24) e

-- the run a row names: the author's program elaborated, capped, driven
-- by the slot table, and decoded back to the envelope stream both
-- batchings read
runOf : Case → List (InstEmit (Val Γ₂ᵉ natᵗ))
runOf c = decodeStream {Γ = Γ₂ᵉ} {a = natᵗ}
            (concat (evaluate↓ (fuel c) (capProg (elaborate (prog c))) (slots c)))

-- the decoded stream must satisfy the protocol automaton
-- (evaluate-well-formed, cached case by case)
wellFormed : Case → Bool
wellFormed c = wellFormed? (runOf c)

-- THE SAME ROW, RUN WITH THE OPERATOR INSIDE THE MACHINE.  This is the
-- left side of `formal-verification-batchSimultaneous`, and it is a
-- second RUN rather than a function applied to the first: the tree is
-- the author's program, elaborated, capped, and wrapped in the plain
-- batching former.  `Val Γ (listᵗ t) = List (Val Γ t)` definitionally,
-- which is why the two sides below meet without a transport.
batchedOf : Case → List (InstEmit (List (Val Γ₂ᵉ natᵗ)))
batchedOf c = decodeStream {Γ = Γ₂ᵉ} {a = listᵗ natᵗ}
                (concat (evaluate↓ (fuel c)
                          (batchSimultaneousᵖ (capProg (elaborate (prog c))))
                          (slots c)))

-- THE MACHINE'S BATCHING AND THE SPEC'S MUST AGREE.  The old shape fed
-- ONE stream to two Agda functions and so tested no evaluator at all;
-- this compares a run of the batching program against the spec applied
-- to the run without it.
agrees : Case → Bool
agrees c = eqBatched (batchedOf c) (spec-batchSimultaneous (runOf c))
