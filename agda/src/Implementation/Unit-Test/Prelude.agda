------------------------------------------------------------------
-- THE BUG CACHE'S SHARED VOCABULARY: what a cached case IS, now that a
-- case is a value rather than a type.
--
-- A CASE IS A PROGRAM, AND EVERY TOP-LINE STATEMENT IS CHECKED OF IT.
-- Compiled, a run is a function call and asking several questions of it
-- is free -- so a row names a program, and every row is held to all of
-- `The-Proof`'s statements that compute on it: the run `WellFormed`
-- field by field, its values the plain program's arrival by arrival,
-- and the batcher's batches the spec's.
--
-- WHY THE PREDICATES ARE BOOLEANS RATHER THAN EQUATIONS.  Each is the
-- decision of one statement's conclusion on one row, settled by
-- `Rx.Emit-Eq` where it is an agreement -- the family the QuickCheck
-- binary decides with, so a cached case and the seed that found it are
-- answering one question.
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

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; concat; map; length)
open import Data.Nat using (ℕ; _≡ᵇ_; _<ᵇ_; _≟_)
open import Data.Fin using (zero; suc)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)

open import Rx.Prim using (InstEmit; ObservableInput)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; takeᵉ; nat̂; inputsBelowᵉ)
open import Rx.SExp using (SExp; plainᵏ; Kinds; scriptedᵏ; sharedᵏ; emptyˢ)
open import Rx.Envelope.Decode using (decodeEmits)
open import Rx.Arrivals using (arrivals↓)
open import Rx.Plain using (plainExp; plainValues)
open import Rx.Simul-Slots using (SimulSlots; SimulSlot; scriptedˢ; sharedˢ; plainSlots)
open import Rx.Protocol using (wellFormed?; protocol-init; runProtocol; accepts?)
open import Rx.Emit-Eq using (eqBatches; eqBursts)
open import Function using (_∘_)
open import Implementation.Pipeline using (elaborateImpl; embedSlotsImpl; unwrapImpl)
open import Rx.Batch using (batchSimultaneousᵖ)
open import Verify-Batch-Simultaneous.Well-Formed using (valuesOf; toSpec; ends?)
import Spec
open Spec ℕ _≟_ using (spec-batchSimultaneous)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- envelope over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- SLOT ZERO IS SCRIPTED AND SLOT ONE IS SHARED.  A script is the only
-- slot that schedules arrivals -- a share runs inside whatever
-- subscribed it -- so without one every run is its subscribe burst
-- alone.  Slot one holds another srxjs program, stands at the ENVELOPE,
-- and may read slot zero.  The kind vector is not a free choice beside
-- the table -- `SimulSlot` is indexed by it, so this line and `mkSlots`
-- below are one statement.
κ₂ : Kinds 2
κ₂ = scriptedᵏ ∷ⱽ sharedᵏ ∷ⱽ []ⱽ

Γ₂ᵉ : Ctx 2
Γ₂ᵉ = plainᵏ Γ₂ κ₂

-- THE TABLE IS BUILT FROM A SCRIPT AND AN AUTHOR-WRITTEN DEFINITION,
-- and that is what a row has to name, because the sweep DRAWS it.  What
-- makes a drawn definition possible at all is that the stratification
-- side condition COMPUTES: a definition is an `SExp` and every elaboration
-- leaf is a real body, so `inputsBelowᵉ` of it reduces to a boolean
-- rather than getting stuck on a postulate.
--
-- IT LIVES HERE RATHER THAN IN THE GENERATOR because a pasted row has
-- to typecheck where the corpus lives, so the name a row prints has to
-- be one the corpus can see.
tOf : (b : Bool) → Maybe (T b)
tOf true  = just tt
tOf false = nothing

slot₀ : ObservableInput ℕ → SimulSlot Γ₂ κ₂ 0 natᵗ scriptedᵏ
slot₀ s = scriptedˢ {ok = tt} s

-- A DEFINITION THAT BREAKS STRATIFICATION FALLS BACK TO SILENCE rather
-- than being rejected, because this is a total function and the
-- generator has no way to prove its draw stratified.  In practice the
-- fallback is unreached -- `genSlotRef k` draws only from slots below
-- `k` by construction -- but it is what makes the row a program rather
-- than a proof obligation.

slot₁ : SExp Γ₂ [] [] [] natᵗ → SimulSlot Γ₂ κ₂ 1 natᵗ sharedᵏ
slot₁ d with tOf (inputsBelowᵉ 1 (plainExp d))
... | just ok = sharedˢ d {ok = ok}
... | nothing = sharedˢ emptyˢ

-- WRITTEN SLOT BY SLOT rather than with a wildcard: the arm a slot may
-- use is `lookup κ₂ i`, which does not reduce for an abstract `i`.
-- That is the kind indexing doing its job -- a table cannot name an
-- arm without saying which slot it is naming it for.
mkSlots : ObservableInput ℕ → SExp Γ₂ [] [] [] natᵗ → SimulSlots Γ₂ κ₂
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
capProg : ∀ {t} → Closed Γ₂ᵉ t → Closed Γ₂ᵉ t
capProg e = takeᵉ (nat̂ 24) e

-- the run a row names: the author's program elaborated, capped, driven
-- by the slot table, and decoded arrival by arrival -- `runᴵ` under the
-- harness cap
runsOf : Case → List (List (InstEmit (Val Γ₂ᵉ natᵗ)))
runsOf c = map (decodeEmits {Γ = Γ₂ᵉ} {a = natᵗ})
               (arrivals↓ (fuel c) (capProg (elaborateImpl κ₂ (prog c))) (embedSlotsImpl (slots c)))

runOf : Case → List (InstEmit (Val Γ₂ᵉ natᵗ))
runOf = concat ∘ runsOf

------------------------------------------------------------------
-- `input-well-formed`, one field at a time, so a failing row says which.
------------------------------------------------------------------

instants : List (InstEmit (Val Γ₂ᵉ natᵗ)) → List ℕ
instants = map InstEmit.instant

allAre : ℕ → List ℕ → Bool
allAre i []       = true
allAre i (j ∷ js) = (i ≡ᵇ j) ∧ allAre i js

memᵇ : ℕ → List ℕ → Bool
memᵇ i []       = false
memᵇ i (j ∷ js) = (i ≡ᵇ j) ∨ memᵇ i js

disjoint : List ℕ → List ℕ → Bool
disjoint []       ys = true
disjoint (x ∷ xs) ys = not (memᵇ x ys) ∧ disjoint xs ys

sameᵇ : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → Bool
sameᵇ []                = true
sameᵇ ([] ∷ arrs)       = sameᵇ arrs
sameᵇ ((x ∷ xs) ∷ arrs) = allAre (InstEmit.instant x) (instants xs) ∧ sameᵇ arrs

distinctᵇ : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → Bool
distinctᵇ []           = true
distinctᵇ (arr ∷ arrs) = disjoint (instants arr) (instants (concat arrs)) ∧ distinctᵇ arrs

-- the `same` field is `sameᵇ`, one instant per arrival; the `distinct`
-- field is `distinctᵇ`, no instant in two arrivals; and the `accepted`
-- field is `acceptedᵇ`, the protocol automaton accepting the flat run
acceptedᵇ : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → Bool
acceptedᵇ runs = accepts? (runProtocol protocol-init (concat runs))

-- the bug cache's own, and STRONGER than the field: the flat run is
-- accepted AND ends paid up
wellFormed : Case → Bool
wellFormed c = wellFormed? (runOf c)

------------------------------------------------------------------
-- `plain-agrees`.
------------------------------------------------------------------

-- THE PLAIN PROGRAM IS CAPPED IN VALUES AND THE ELABORATED ONE IN
-- ENVELOPES, so the two cuts are not one cut and a capped row is not
-- compared.  A row neither cap reached is the uncapped run on both
-- sides; `capped` says which rows those are, and a sweep counts them.
capPlain : ∀ {t} → Closed Γ₂ t → Closed Γ₂ t
capPlain e = takeᵉ (nat̂ 24) e

plainOf : Case → List (List ℕ)
plainOf c = map plainValues (arrivals↓ (fuel c) (capPlain (plainExp (prog c))) (plainSlots (slots c)))

-- over the two runs, so a harness that has them computes neither twice
plainAgreesᵇ : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → List (List ℕ) → Bool
plainAgreesᵇ runs plain =
  not (length (concat runs) <ᵇ 24) ∨ not (length (concat plain) <ᵇ 24)
    ∨ eqBatches (map valuesOf runs) plain

------------------------------------------------------------------
-- `batch-agrees`, on the run the row's program gives.
------------------------------------------------------------------

-- THE BATCHER IS RUN INSIDE THE MACHINE, OVER THE ROW'S OWN PROGRAM,
-- rather than over a replay: that is the operator the TypeScript port
-- mirrors.  Where the run is `WellFormed` it answers the statement's
-- question; where it is not, a disagreement may be the run's fault
-- rather than the batcher's, which is why the fields are checked apart.
implBurstsOf : Case → List (List (List ℕ))
implBurstsOf c =
  map (unwrapImpl {Γ = Γ₂ᵉ} {a = natᵗ})
      (arrivals↓ (fuel c)
                 (batchSimultaneousᵖ (capProg (elaborateImpl κ₂ (prog c))))
                 (embedSlotsImpl (slots c)))

specOf : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → List (List (List ℕ))
specOf = map (spec-batchSimultaneous ∘ toSpec)

specBurstsOf : Case → List (List (List ℕ))
specBurstsOf c = specOf (runsOf c)

agrees : Case → Bool
agrees c = eqBursts (implBurstsOf c) (specBurstsOf c)

------------------------------------------------------------------
-- EVERY CHECK AT ONCE, OVER RUNS COMPUTED ONCE.  Each argument is one
-- shared thunk, where each of six `Case`-level checks would re-run the
-- program: a row costs its runs, not its runs times its checks.
------------------------------------------------------------------
checks : List (List (InstEmit (Val Γ₂ᵉ natᵗ))) → List (List (List ℕ)) → List (List ℕ)
       → List (String × Bool)
checks runs impl plain =
  ("well-formed" , wellFormed? (concat runs)) ∷ ("impl≡spec" , eqBursts impl (specOf runs))
  ∷ ("plain" , plainAgreesᵇ runs plain) ∷ ("same" , sameᵇ runs)
  ∷ ("distinct" , distinctᵇ runs) ∷ ("ends" , ends? protocol-init runs) ∷ []

checksOf : Case → List (String × Bool)
checksOf c = checks (runsOf c) (implBurstsOf c) (plainOf c)
