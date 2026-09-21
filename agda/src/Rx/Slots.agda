-- THE SLOT TELESCOPE, on its own so that BOTH the width measures and
-- the evaluator can read it.
--
-- WHY IT IS NOT IN Rx.Evaluator.  A width measure has to walk a shared
-- def, so it needs `Slot` / `Slots`; the evaluator needs the same
-- telescope to seed its descent.  With the telescope inside the
-- evaluator that is a cycle; here it is a shared prerequisite, and
-- Rx.Evaluator re-exports the whole module so the ~1400 sites that read
-- `Slots` off the evaluator are untouched.
module Rx.Slots where

open import Data.Bool    using (T)
open import Data.Nat     using (ℕ)
open import Data.Vec     using (lookup)
open import Data.Fin     using (toℕ)

open import Rx.Prim using (ObservableInput)
open import Rx.Exp  using (Ty; Ctx; Val; Closed; isData; inputsBelowᵉ)

-- slot i of Γ is either an external SCRIPTED input (hot/cold) or a
-- SHARED observable: a plain tree with an implicit all-resets-false
-- share() at its root.  Share identity is the de Bruijn index -- the
-- binding, not the expression, exactly as a JS `const`.
--
-- SCRIPTED SLOTS CARRY DATA ONLY (`T (isData t)`, discharged by
-- unification at every data type, so ordinary scripts are written
-- unchanged).  An observable-typed script would be a hole in the
-- walk's descent order: a value at observable type is a body paired
-- with an environment, so its script could emit the very program being
-- walked, and the *All hop off it would be asked to descend from a
-- rank to itself.  The regress is real, not merely undescending --
-- such a program re-enters itself unboundedly -- so no edge can pay
-- for it and the restriction is by construction.
--
-- A SHARED SLOT IS UNDER NO SUCH BAR, and the difference is that a
-- shared def IS walked, so its emissions are syntactically inside it
-- and the crossing is the connect edge, which the reducibility
-- candidate answers at the definition's own type.
--
-- THIS TELESCOPE IS THE EVALUATOR AT FULL SCOPE AND A SHARED DEF HERE
-- IS AN ARBITRARY PLAIN TREE, which at an observable type can hand the
-- machine an envelope no elaboration produced -- `subs-shared`
-- subscribes a definition straight down the consumer's path, so its
-- emissions reach the wire exactly as written.  That is DELIBERATE and
-- it is what the differential harness runs at: the TypeScript
-- fast-check drives this evaluator over plain trees and knows nothing
-- of srxjs, so narrowing here would narrow the thing under test.
--
-- WHAT A CLAIM ABOUT SRXJS QUANTIFIES OVER INSTEAD IS `Rx.Simul-Slots`,
-- where a shared slot's definition is an `SExp` and the table is read
-- back into this one by elaborating it.  A definition there cannot
-- forge at any type, because every envelope in it was built by the
-- elaboration -- so the observable-typed shared slot survives, and it
-- survives without a side condition here.
---- THE TELESCOPE IS STRATIFIED (`inputsBelowᵉ k`): slot k's def may
-- reference only inputs at indices strictly below k -- a real JS
-- `const` telescope, where reading a later `const` is a TDZ error,
-- and exactly what the TS generator builds (a def is generated
-- against the strict prefix of earlier slot types).  The index `k`
-- is a parameter of `Slot` so the side condition can name it; like
-- `isData` on scripted slots, it discharges by unification at every
-- concrete program.
-- What it buys: any per-slot reading is computable by recursion on
-- the slot index, since slot k's def consults only slots j < k.
-- Without it a slot's reading would have to be sought as a
-- simultaneous solution over the whole table.
data Slot {n} (Γ : Ctx n) (k : ℕ) (t : Ty) : Set where
  scripted : {ok : T (isData t)} → ObservableInput (Val Γ t) → Slot Γ k t
  shared   : (d : Closed Γ t) {ok : T (inputsBelowᵉ k d)} → Slot Γ k t

Slots : ∀ {n} → Ctx n → Set
Slots Γ = ∀ i → Slot Γ (toℕ i) (lookup Γ i)
