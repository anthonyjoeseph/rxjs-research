-- THE SLOT TELESCOPE, on its own so that BOTH the width measures and
-- the evaluator can read it.
--
-- WHY IT IS NOT IN Rx.Evaluator any more.  `budgetAt` — the seeded gas —
-- now reads `Rx.Frame-Width.entryCeil`, because the caps recurrence's
-- BASE width IS the entry ceiling and a budget that must dominate the
-- recurrence has to know the number it starts from.  Frame-Width in turn
-- needs `Slot` / `Slots` to walk a shared def.  With the telescope in
-- the evaluator that is a cycle; here it is a shared prerequisite, and
-- Rx.Evaluator re-exports the whole module so the ~1400 sites that read
-- `Slots` off the evaluator are untouched.
module Rx.Slots where

open import Data.Bool    using (T)
open import Data.List    using (map; tabulate)
open import Data.Nat.ListAction  using (sum)
open import Data.Nat     using (ℕ; suc; _+_)
open import Data.Vec     using (lookup)

open import Rx.Prim using (Timed; ObservableInput; hot; cold)
open import Rx.Exp  using (Ty; Ctx; Val; Closed; isData; sizeᵉ; sizeᵛ)

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
data Slot {n} (Γ : Ctx n) (t : Ty) : Set where
  scripted : {ok : T (isData t)} → ObservableInput (Val Γ t) → Slot Γ t
  shared   : Closed Γ t → Slot Γ t

Slots : ∀ {n} → Ctx n → Set
Slots Γ = ∀ i → Slot Γ (lookup Γ i)

-- the size that seeds the budget is the WHOLE program's: root
-- expression, every shared slot def (connect subscribes defs, and
-- their μ/inner structure spends fuel just like the root's), AND
-- every scripted value — a scripted obs value is delivered and
-- subscribed like any other inner, so its syntax demands fuel the
-- root's size knows nothing about
inputSize : ∀ {n} {Γ : Ctx n} {t} → ObservableInput (Val Γ t) → ℕ
inputSize {t = t} (hot async)       =
  suc (sum (map (λ tv → sizeᵛ t (Timed.val tv)) async))
inputSize {t = t} (cold sync async) =
  suc (sum (map (sizeᵛ t) sync)
       + sum (map (λ tv → sizeᵛ t (Timed.val tv)) async))

slotSize : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotSize (scripted i) = inputSize i
slotSize (shared d)   = sizeᵉ d

slotsSize : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsSize sl = sum (tabulate λ i → slotSize (sl i))
