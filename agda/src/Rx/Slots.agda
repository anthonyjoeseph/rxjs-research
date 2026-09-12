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
-- SHARED observable: an exp tree with an implicit all-resets-false
-- share() at its root.  Share identity is the de Bruijn index — the
-- binding, not the expression, exactly as a JS `const`.
--
-- SCRIPTED SLOTS CARRY DATA ONLY (`T (isData t)`, discharged by
-- unification at every data type, so ordinary scripts are written
-- unchanged).  An observable-typed slot would be a hole in the walk's
-- descent order: `Val Γ (obs u) = Closed Γ u`, so its script could emit
-- the very program being walked, and the *All hop off it would be asked
-- for `measureE V e ≺ᵛ measureE V e`.  The regress is real, not merely
-- undescending — such a program re-enters itself at every finite gas —
-- so no edge can pay for it and the restriction is by construction.
-- Higher-order pipelines are unaffected: an observable-typed slot is a
-- `shared` def, which IS walked, so its emissions are syntactically
-- inside it and the crossing is the connect edge (anchored by
-- connect-anchor).
--
-- THE TELESCOPE IS STRATIFIED (`inputsBelowᵉ k`): slot k's def may
-- reference only inputs at indices strictly below k — a real JS
-- `const` telescope, where reading a later `const` is a TDZ error,
-- and exactly what the TS generator builds (a def is generated
-- against the strict prefix of earlier slot types).  The index `k`
-- is a parameter of `Slot` so the side condition can name it; like
-- `isData` on scripted slots, it discharges by unification at every
-- concrete program.  What it buys: a per-slot hop depth is
-- computable by recursion on the slot index (slot k's hop reads only
-- hops j < k), which is what let a per-slot hop measure report the
-- slot's true hop instead of the refuted constant 0: an obs-typed
-- shared def emits values of positive hop, so a hop bound that zeroes
-- the share boundary is false.  The measure that spent this is gone
-- with the budget; the side condition stays, because the TS generator
-- builds exactly this telescope and a JS const cannot read forward.
data Slot {n} (Γ : Ctx n) (k : ℕ) (t : Ty) : Set where
  scripted : {ok : T (isData t)} → ObservableInput (Val Γ t) → Slot Γ k t
  shared   : (d : Closed Γ t) {ok : T (inputsBelowᵉ k d)} → Slot Γ k t

Slots : ∀ {n} → Ctx n → Set
Slots Γ = ∀ i → Slot Γ (toℕ i) (lookup Γ i)

