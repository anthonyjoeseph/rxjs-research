-- ══════════════════════════════════════════════════════════════════
-- DEPTH-CONN: a share connect cannot be bounded by a store that need
-- not hold the def
--
-- THE STATEMENT REFUTED HERE IS A PREDECESSOR.  It was
-- `depth-conn-storeNest`; the successor is `depth-conn-input`
-- (Depth-Compositional), which reads the slot inside the statement
-- instead of taking the def as an argument, so it has no free variable
-- left for this witness to attack.  Neither name will co-occur with the
-- other in `src` — grep for the successor.
--
-- The statement bounds the depth of a SHARE CONNECT by the store's own
-- nesting:
--
--   depthConn g i d κ bid now sched st ≤ storeNestMax sched st
--
-- and quantifies `d` — the definition being connected — over every
-- `Closed Γ (lookup Γ i)` there is, with nothing tying it to `sched`.
-- Its only caller reaches it through `with Sched.slots sched i`, so
-- there `d` IS the slot's stored def and `sizeᵉ d = slotNest (shared d)
-- ≤ slotsNestMax (Sched.slots sched) ≤ storeNestMax sched st`.  That
-- inequality is the whole reason the bound is believable, and the
-- statement does not have it: read off a free `d`, `slotNest (shared d)`
-- is a size the right-hand side has never heard of.
--
-- So the refutation does not need an exotic store.  It needs the
-- POOREST one — a program whose every slot is `scripted`, at its own
-- initial state — and any `d` at all whose connect spends one arc:
--
--   slotsNestMax (all scripted) = 0    nodesNestMax [] = 0
--   ⇒ storeNestMax = 0
--
-- while `depthConn (gs g0) i d root 0 0` enters `d` and its one
-- `thru-outer` frame charges `suc _` (Caps-Depth, SPENDING ARC 1).
-- `1 ≤ 0` is the contradiction.
--
-- AND THE WITNESS IS REACHABLE, which is what makes this a statement
-- defect rather than a state one: `sched-init e ins` at `st-init e` is
-- exactly what `evaluate` starts from.  What is unreachable is the CALL
-- — with every slot scripted, the mirror never asks about a `shared d`
-- at all.  That is the diagnosis in one line: the statement admits
-- instances its caller cannot make, and the caller already holds the
-- fact that rules them out.
--
-- WHAT IT DOES NOT SAY.  Nothing here touches the successor, and the
-- double-count described in its header is a separate obstacle that
-- survives this refutation intact.  This is a defect of QUANTIFICATION,
-- not of the bound.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Depth-Conn where

open import Data.Empty   using (⊥)
open import Data.Fin     using (Fin; zero)
open import Data.List    using ([]; _∷_)
open import Data.Nat     using (_≤_)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
open import Rx.Prim      using (Gas; g0; gs; Id; Tick; cold)
open import Rx.Exp       using (natᵗ; Ctx; Closed; ofᵉ; emptyᵉ; mergeAllᵉ; nat̂; strmᵗ)
open import Rx.Slots     using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth       using (depthConn)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax)

------------------------------------------------------------------
-- THE POOREST STORE: one scripted slot, nothing else
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

-- MATCHED ON THE INDEX, not `ins₁ _`: `scripted`'s side condition is
-- `T (isData (lookup Γ i))`, and `lookup Γ₁ i` does not reduce for an
-- abstract `i`, so the blanket clause leaves it an unsolved meta.
ins₁ : Slots Γ₁
ins₁ zero = scripted (cold [] [])

rootProg : Closed Γ₁ natᵗ
rootProg = emptyᵉ

------------------------------------------------------------------
-- AND A DEF WHOSE CONNECT SPENDS ONE ARC.  `mergeAllᵉ` over a
-- synchronous singleton: subscribing the outer emits its one inner
-- observable in the same frame, so the burst runs back through the
-- `thru-outer` frame, whose depth clause is `suc (depthWalk …)`.
------------------------------------------------------------------

defBad : Closed Γ₁ natᵗ
defBad = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

------------------------------------------------------------------
-- REFUTED
------------------------------------------------------------------

sched₁ : Sched Γ₁
sched₁ = sched-init rootProg ins₁

st₁ : EvalSt rootProg
st₁ = st-init rootProg

-- BOTH SIDES, as numbers.  The absurd pattern alone would carry the
-- refutation — `()` is accepted only where the type has no constructor,
-- so it already asserts the left side is a `suc` and the right a `zero`,
-- and `0 ≤ 0` would be inhabited by `z≤n` and rejected.  The numbers are
-- pinned anyway, because they are the finding: one spending arc against
-- a store with nothing in it.  A later change that makes either side
-- move gets a red row here rather than a quietly different refutation.
depth-is-1 : depthConn (gs g0) zero defBad root 0 0 sched₁ st₁ ≡ 1
depth-is-1 = refl

store-is-0 : storeNestMax sched₁ st₁ ≡ 0
store-is-0 = refl

depth-conn-free-def-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
     (κ : Path Γ (lookup Γ i) t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthConn g i d κ bid now sched st ≤ storeNestMax sched st) → ⊥
depth-conn-free-def-absurd h
  with subst₂ _≤_ depth-is-1 store-is-0
         (h (gs g0) zero defBad root 0 0 sched₁ st₁)
... | ()
