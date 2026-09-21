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

open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; concat)
open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.String using (String)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; listᵗ; takeᵉ; nat̂; inputsBelowᵉ)
open import Rx.SExp using (SExp; emitᵗ; plainᵏ; Kinds; sharedᵏ; emptyˢ)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Simul-Slots using (SimulSlots; SimulSlot; sharedˢ; embedSlots)
open import Rx.Protocol using (wellFormed?)
open import Rx.Emit-Eq using (eqBatched)
open import Rx.Batch using (batchSimultaneousᵖ)
open import Spec using (spec-batchSimultaneous)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- envelope over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- BOTH SLOTS ARE `sharedᵏ`: each one holds another srxjs program, so
-- it stands at the ENVELOPE and `input` reads it straight.  The kind
-- vector is not a free choice beside the table -- `SimulSlot` is
-- indexed by it, so this line and `mkSlots` below are one statement.
κ₂ : Kinds 2
κ₂ = sharedᵏ ∷ⱽ sharedᵏ ∷ⱽ []ⱽ

Γ₂ᵉ : Ctx 2
Γ₂ᵉ = plainᵏ Γ₂ κ₂

-- THE TABLE IS BUILT FROM TWO AUTHOR-WRITTEN DEFINITIONS, and that is
-- what a row has to name, because the sweep DRAWS it.  What makes a
-- drawn table possible at all is that the stratification side
-- condition COMPUTES: a definition is an `SExp` and every elaboration
-- leaf is a real body, so `inputsBelowᵉ` of it reduces to a boolean
-- rather than getting stuck on a postulate.
--
-- IT LIVES HERE RATHER THAN IN THE GENERATOR because a pasted row has
-- to typecheck where the corpus lives, so the name a row prints has to
-- be one the corpus can see.
tOf : (b : Bool) → Maybe (T b)
tOf true  = just tt
tOf false = nothing

-- A DEFINITION THAT BREAKS STRATIFICATION FALLS BACK TO SILENCE rather
-- than being rejected, because this is a total function and the
-- generator has no way to prove its draw stratified.  In practice the
-- fallback is unreached -- `genSlotRef k` draws only from slots below
-- `k` by construction -- but it is what makes the row a program rather
-- than a proof obligation.
slot₀ : SExp Γ₂ [] [] [] natᵗ → SimulSlot Γ₂ κ₂ 0 natᵗ sharedᵏ
slot₀ d with tOf (inputsBelowᵉ 0 (elaborate κ₂ d))
... | just ok = sharedˢ d {ok = ok}
... | nothing = sharedˢ emptyˢ

slot₁ : SExp Γ₂ [] [] [] natᵗ → SimulSlot Γ₂ κ₂ 1 natᵗ sharedᵏ
slot₁ d with tOf (inputsBelowᵉ 1 (elaborate κ₂ d))
... | just ok = sharedˢ d {ok = ok}
... | nothing = sharedˢ emptyˢ

-- WRITTEN SLOT BY SLOT rather than with a wildcard: the arm a slot may
-- use is `lookup κ₂ i`, which does not reduce for an abstract `i`.
-- That is the kind indexing doing its job -- a table cannot name an
-- arm without saying which slot it is naming it for.
mkSlots : SExp Γ₂ [] [] [] natᵗ → SExp Γ₂ [] [] [] natᵗ → SimulSlots Γ₂ κ₂
mkSlots d₀ d₁ zero          = slot₀ d₀
mkSlots d₀ d₁ (suc zero)    = slot₁ d₁
mkSlots d₀ d₁ (suc (suc ()))

-- one cached counterexample: a label, and the run that produced it
record Case : Set where
  constructor cached
  field
    name  : String
    fuel  : ℕ
    prog  : SExp Γ₂ [] [] [] natᵗ
    slots : SimulSlots Γ₂ κ₂

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
            (concat (evaluate↓ (fuel c) (capProg (elaborate κ₂ (prog c))) (embedSlots (slots c))))

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
                          (batchSimultaneousᵖ (capProg (elaborate κ₂ (prog c))))
                          (embedSlots (slots c))))

-- THE MACHINE'S BATCHING AND THE SPEC'S MUST AGREE.  The old shape fed
-- ONE stream to two Agda functions and so tested no evaluator at all;
-- this compares a run of the batching program against the spec applied
-- to the run without it.
agrees : Case → Bool
agrees c = eqBatched (batchedOf c) (spec-batchSimultaneous (runOf c))
