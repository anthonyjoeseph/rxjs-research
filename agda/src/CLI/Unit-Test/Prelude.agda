------------------------------------------------------------------
-- THE BUG CACHE'S SHARED VOCABULARY: what a cached case IS, now that a
-- case is a value rather than a type.
--
-- A CASE IS A PROGRAM, AND EVERY TOP-LINE STATEMENT IS CHECKED OF IT.
-- Compiled, a run is a function call and asking several questions of it
-- is free -- so a row names a program, and every row is held to the four
-- statements `Main` imports, each at its own two sides.
--
-- WHY THE PREDICATES ARE BOOLEANS RATHER THAN EQUATIONS.  Each is the
-- decision of one statement's conclusion on one row, settled by
-- `CLI.Emit-Eq` where it is an agreement -- the family the QuickCheck
-- binary decides with, so a cached case and the seed that found it are
-- answering one question.
--
-- WHAT IS NOT HERE, DELIBERATELY: a predicate for a run that went DRY.
-- No builder constructs the marker, so a dry run is not a disagreement
-- between two implementations of one batching — it is the descent
-- refusing, which the QuickCheck binary reports unpasteably, and it
-- stays out of a corpus whose verdict gates the build.
------------------------------------------------------------------
module CLI.Unit-Test.Prelude where

open import Data.Bool using (Bool; true; false; T; _∧_; not; _xor_)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Fin using (zero; suc)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (ObservableInput; hot; cold)
open import Rx.Exp using (Ctx; Val; natᵗ; obs; inputsBelowᵉ; FlatOp)
open import SExp.Syntax using (SExp; plainᵏ; plainᵗ; Kinds; hotᵏ; coldᵏ; sharedᵏ; emptyˢ; emitᵗ;
  flattenˢ; mapˢ; pairˢ; inlˢ; inrˢ; unitˢ; varˢᵗ)
open import Rx.Evaluator using (Burst)
open import SExp.Plain using (plainExp)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ)
open import CLI.Emit-Eq using (eqListℕ; eqBatches)
open import SExp.Pipeline using (emitsᴵ; runᴾ)
open import Timed.Translation using (packetOf; timedᶜ; itemᵗ)
open import Left-To-Right.Statement using (joinedᴵ)
open import Timed.Timing-Correct using (stampedᵀ)
open import Batchable.Statement using (batchedᴱ; groupedᴱ)
open import Timed.Faithful using (untimedᵀ)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- InstEmit over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- SLOT ZERO IS SCRIPTED AND SLOT ONE IS SHARED.  A script is the only
-- slot that schedules arrivals -- a share runs inside whatever
-- subscribed it -- so without one every run is its subscribe burst
-- alone.  Slot one holds another srxjs program, stands at the INSTEMIT,
-- and may read slot zero.  The kind vector is not a free choice beside
-- the table -- `SimulSlot` is indexed by it, so slot zero's kind is
-- read off its script, and `mkSlots` below is what says so.
κOf : ObservableInput ℕ → Kinds 2
κOf (hot _)    = hotᵏ  ∷ⱽ sharedᵏ ∷ⱽ []ⱽ
κOf (cold _ _) = coldᵏ ∷ⱽ sharedᵏ ∷ⱽ []ⱽ

Γ₂ᵉ : Kinds 2 → Ctx 4
Γ₂ᵉ κ = plainᵏ Γ₂ κ

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

-- A DEFINITION THAT BREAKS STRATIFICATION FALLS BACK TO SILENCE rather
-- than being rejected, because this is a total function and the
-- generator has no way to prove its draw stratified.  In practice the
-- fallback is unreached -- `genSlotRef k` draws only from slots below
-- `k` by construction -- but it is what makes the row a program rather
-- than a proof obligation.

slot₁ : ∀ {κ} → SExp Γ₂ [] [] [] natᵗ → SimulSlot Γ₂ κ 1 natᵗ sharedᵏ
slot₁ d with tOf (inputsBelowᵉ 1 (plainExp d))
... | just ok = sharedˢ d {ok = ok}
... | nothing = sharedˢ emptyˢ

-- WRITTEN SLOT BY SLOT rather than with a wildcard: the arm a slot may
-- use is `lookup (κOf d₀) i`, which does not reduce for an abstract `i`
-- or script.  That is the kind indexing doing its job -- a table cannot
-- name an arm without saying which slot it is naming it for.
mkSlots : (d₀ : ObservableInput ℕ) → SExp Γ₂ [] [] [] natᵗ → SimulSlots Γ₂ (κOf d₀)
mkSlots (hot as)     d₁ zero       = hotˢ {ok = tt} as
mkSlots (cold ss as) d₁ zero       = coldˢ {ok = tt} ss as
mkSlots (hot _)      d₁ (suc zero) = slot₁ d₁
mkSlots (cold _ _)   d₁ (suc zero) = slot₁ d₁
mkSlots _            d₁ (suc (suc ()))

-- RXJS'S THREE NAMED FLATTENERS, which the author's tree does not have
-- as formers: `flattenˢ` over a map making every element a lane and none
-- an echo.  `mergeAll` is `flatAllˢ (mergeᶠ nothing)`, `concatAll` is
-- `flatAllˢ (mergeᶠ (just 1))`, `switchAll` and `exhaustAll` are
-- `flatAllˢ switchᶠ` and `flatAllˢ exhaustᶠ`.  It lives HERE because a
-- row is pasted where the corpus lives and the sweep prints the name.
flatAllˢ : ∀ {Δᵍ Δ Θ t} → FlatOp → SExp Γ₂ Δᵍ Δ Θ (obs t) → SExp Γ₂ Δᵍ Δ Θ t
flatAllˢ op e = flattenˢ op (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (varˢᵗ (here refl)))) e)

-- one cached counterexample: a label, and the run that produced it
record Case : Set where
  field
    name  : String
    fuel  : ℕ
    prog  : SExp Γ₂ [] [] [] natᵗ
    kinds : Kinds 2
    slots : SimulSlots Γ₂ kinds

open Case using (name; fuel; prog; kinds; slots)

-- the kinds are read off the table's own type, so a row names none
cached : String → ℕ → SExp Γ₂ [] [] [] natᵗ → {κ : Kinds 2} → SimulSlots Γ₂ κ → Case
cached n f e {κ} ins = record { name = n ; fuel = f ; prog = e ; kinds = κ ; slots = ins }

------------------------------------------------------------------
-- THE FOUR STATEMENTS `Main` IMPORTS, EACH DECIDED AT ITS OWN SIDES.
-- A side is the statement module's own definition applied at this row,
-- never a restatement of it, so the check and the claim cannot drift
-- apart: at `Γ₂`, the row's kinds, `natᵗ` and `tt`, what is compared here is what
-- the statement says is equal.
--
-- NO CAP.  A `takeᵉ` above the program -- counted in InstEmits or in
-- values -- runs a different program from the one the row names, and a
-- capped run is an instance of no statement.  The fuel is the one budget
-- the statements quantify over, so it is the one a row may set.
------------------------------------------------------------------

data Statement : Set where
  left-to-rightˢ timing-correctˢ batchableˢ timed-faithfulˢ : Statement

-- in `Main`'s order, which is the order a report counts them in
statements : List Statement
statements = left-to-rightˢ ∷ timing-correctˢ ∷ batchableˢ ∷ timed-faithfulˢ ∷ []

statementName : Statement → String
statementName left-to-rightˢ  = "left-to-right"
statementName timing-correctˢ = "timing-correct"
statementName batchableˢ      = "batchable"
statementName timed-faithfulˢ = "timed-faithful"

-- `left-to-right`: the batches joined back up, and the plain run
ltrSides : Case → List ℕ × List ℕ
ltrSides c = joinedᴵ tt (kinds c) (fuel c) (prog c) (slots c) , runᴾ (fuel c) (prog c) (slots c)

-- `timing-correct`: each value's stamp, beside its packet.  The
-- contexts are passed by hand because `Val` at a concrete type forgets
-- its context, so no argument's type can say which one it was.
Γ₂ᵗ : Kinds 2 → Ctx 4
Γ₂ᵗ κ = plainᵏ (timedᶜ Γ₂ κ) κ

packets : ∀ κ → List (ℕ × Val (Γ₂ᵗ κ) (plainᵗ (itemᵗ natᵗ))) → List (ℕ × List ℕ)
packets κ []             = []
packets κ ((i , v) ∷ ps) = (i , packetOf {Γ = Γ₂ᵗ κ} natᵗ v) ∷ packets κ ps

stampsOf : Case → List (ℕ × List ℕ)
stampsOf c = packets (kinds c) (stampedᵀ (kinds c) (fuel c) (prog c) (slots c))

-- `batchable`: both sides read one run's emits, so the run is an
-- argument and computed once
batchSides : ∀ κ → Burst (Γ₂ᵉ κ) (emitᵗ natᵗ) → List (List ℕ) × List (List ℕ)
batchSides κ es = batchedᴱ {Γ′ = Γ₂ᵉ κ} natᵗ tt es , groupedᴱ {Γ′ = Γ₂ᵉ κ} natᵗ tt es

batchableSides : Case → List (List ℕ) × List (List ℕ)
batchableSides c = batchSides (kinds c) (emitsᴵ (kinds c) (fuel c) (prog c) (slots c))

-- `timed-faithful`: the timed program's run untimed, and the plain run
faithfulSides : Case → List ℕ × List ℕ
faithfulSides c = untimedᵀ tt (kinds c) (fuel c) (prog c) (slots c) , runᴾ (fuel c) (prog c) (slots c)

-- `Coherent`, decided: same stamp exactly when same packet
coherentᵇ : ℕ × List ℕ → ℕ × List ℕ → Bool
coherentᵇ (i , p) (j , q) = not ((i ≡ᵇ j) xor eqListℕ p q)

-- `AllPairs`, decided
coheresWith : ℕ × List ℕ → List (ℕ × List ℕ) → Bool
coheresWith x []       = true
coheresWith x (y ∷ ys) = coherentᵇ x y ∧ coheresWith x ys

allPairsᵇ : List (ℕ × List ℕ) → Bool
allPairsᵇ []       = true
allPairsᵇ (x ∷ xs) = coheresWith x xs ∧ allPairsᵇ xs

-- each takes its sides as ONE argument, so a pair is computed once
agreeᴸ : List ℕ × List ℕ → Bool
agreeᴸ (l , r) = eqListℕ l r

agreeᴮ : List (List ℕ) × List (List ℕ) → Bool
agreeᴮ (l , r) = eqBatches l r

holds : Statement → Case → Bool
holds left-to-rightˢ  c = agreeᴸ (ltrSides c)
holds timing-correctˢ c = allPairsᵇ (stampsOf c)
holds batchableˢ      c = agreeᴮ (batchableSides c)
holds timed-faithfulˢ c = agreeᴸ (faithfulSides c)

checksOf : List Statement → Case → List (String × Bool)
checksOf ss c = map (λ s → statementName s , holds s c) ss
