------------------------------------------------------------------
-- INIT-CAPS: `capsOK?` holds at the BASE caps, at the initial state.
--
-- This discharges what `init-capsOK?-base-core` postulated
-- (`init-capsOK?-base-core`, Caps-Bridge).  Its own module because it
-- is a lemma family that consumes Measures / Caps-Face / Frame-Width
-- as finished facts — an import, not a mutuality — and because
-- Caps-Bridge should not pay this grind's recheck.
--
-- THE CONJUNCTS of `capsOK?` (Caps-Face), at `st-init`:
--   (1) stBounded? cSize sched st   — all-concat-tab + mkHot-bounded
--   (2) regsSz? cSize registry      — refl, the registry is []
--   (3) all (widLive cWid slots) live — the branch that was open
--   (4) all (widNode cWid slots) nodes — refl, nodes is []
--   (5) length registry ≤ᵇ cReg     — refl, 0 ≤ᵇ suc _
--   (6) all (parkRoom …) nodes      — refl, nodes is []
--   (7) all (closLive caps slots) live — the closure key, same shape as (3)
--   (8) srcFloor? sched             — sched-init sets nextSource = n, so n ≤ᵇ n
--
-- CONJUNCTS (3) AND (7) ARE THE TWO WITH CONTENT, and `scripted`'s own
-- index closes both: `scripted` carries `{ok : T (isData t)}`, EVERY
-- data type has `pWᵛ ≡ 0` (the outWᵛ/dWᵛ/pWᵛ-data-zero family below),
-- and every data type reads `true` under the closure measure
-- (`closLive-pend`), so the checks reduce to `0 ≤ᵇ cWid` and to `true`.
-- Cold and shared slots contribute no live source at all.
--
-- The eight scaffold hypotheses the -core carried are NOT used: they
-- were kit for a route this proof does not take.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Init-Caps where




open import Data.Bool    using (true; T)
open import Data.Nat     using (ℕ; suc; _+_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n+m)
open import Data.List    using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Exp    using (Ty; Ctx; Closed; Val; sizeᵉ; isData)
open import Rx.Slots  using (scripted; shared; slotSize; slotsSize; Slots)
open import Rx.Prim   using (hot; cold)
open import Rx.Frame-Width  using (pWᵛ; entryCeil)
open import Rx.Evaluator    using (mkHot; sched-init; st-init; resolve)

-- Boolean and bound toolkit from Measures (the lightest path; avoids
-- pulling in the full Wet/Caps/Keeps-Ring chain)
open import Verify-Budget-Sufficient.Measures
  using (boundedLive; all-concat-tab; mkHot-bounded; fᵢ≤sum-tab)

-- capsOK? and widLive live in Caps-Face
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; widLive; closLive; closLive-pend)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (pWᵛ-data)

-- Caps record type and constructor
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Decide using (∧-intro; ≤ᵇ-true)

-- baseCaps lives here now; Caps-Bridge imports it back.  (It used to
-- be defined in Caps-Bridge, which is downstream of this module.)
baseCaps : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Caps
baseCaps {n = n} e sl =
  caps (2 + sizeᵉ e + slotsSize sl)
       (suc (entryCeil n sl e))
       (suc (sizeᵉ e + slotsSize sl))

----------------------------------------------------------------------
-- STEP 1.  Decompose the T (isData _) proof for product and sum types.
----------------------------------------------------------------------

-- When T (isData (s ×ᵗ t)) holds, extract T (isData s).
-- Works equally for s +ᵗ t since isData (s ×ᵗ t) = isData (s +ᵗ t) definitionally.


----------------------------------------------------------------------
-- STEP 2.  outWᵛ = 0 and dWᵛ = 0 for data types; hence pWᵛ = 0.
----------------------------------------------------------------------



-- pWᵛ j sl t v = outWᵛ j sl t v ⊔ dWᵛ j sl t v (.Frame-Width-419)
-- cong₂ _⊔_ p q : outWᵛ ⊔ dWᵛ ≡ 0 ⊔ 0; and 0 ⊔ 0 = 0 definitionally

----------------------------------------------------------------------
-- STEP 3.  The widLive predicate holds on any list of pending values
--           when T (isData t).  pWᵛ = 0 and 0 ≤ᵇ W = true for all W.
----------------------------------------------------------------------

all-pWᵛ-data : ∀ {n} {Γ : Ctx n} {A : Set} (j W : ℕ) (sl : Slots Γ) (t : Ty)
  → T (isData t) → (ps : List (A × Val Γ t))
  → all (λ tv → pWᵛ j sl t (proj₂ tv) ≤ᵇ W) ps ≡ true
all-pWᵛ-data j W sl t ok [] = refl
all-pWᵛ-data j W sl t ok ((tk , v) ∷ ps) =
  ∧-intro
    -- pWᵛ-data gives pWᵛ = 0; subst replaces it; 0 ≤ᵇ W = refl
    (subst (λ x → (x ≤ᵇ W) ≡ true) (sym (pWᵛ-data j sl t ok v)) refl)
    (all-pWᵛ-data j W sl t ok ps)

----------------------------------------------------------------------
-- STEP 4.  widLive W ins holds for every live source produced by
--           mkHot ins i.  Only hot scripted slots produce a live
--           source; cold and shared yield [], trivially true.
----------------------------------------------------------------------

widLive-mkHot : ∀ {n} {Γ : Ctx n} (W : ℕ) (ins : Slots Γ) (i : Fin n)
  → all (widLive W ins) (mkHot ins i) ≡ true
widLive-mkHot {n = n} {Γ = Γ} W ins i with ins i
... | scripted {ok = ok} (hot async) =
      -- mkHot ins i = [l] with l.elemTy = lookup Γ i, l.pending = resolve 0 async
      -- all (widLive W ins) [l] = widLive W ins l ∧ true
      -- widLive W ins l = all (λ tv → pWᵛ n ins (lookup Γ i) (proj₂ tv) ≤ᵇ W) (resolve 0 async)
      ∧-intro (all-pWᵛ-data n W ins (lookup Γ i) ok (resolve 0 async)) refl
... | scripted (cold _ _) = refl   -- mkHot returns []
... | shared _            = refl   -- mkHot returns []

closLive-mkHot : ∀ {n} {Γ : Ctx n} (c : Caps) (ins : Slots Γ) (i : Fin n)
  → all (closLive c ins) (mkHot ins i) ≡ true
closLive-mkHot {n = n} {Γ = Γ} c ins i with ins i
... | scripted {ok = ok} (hot async) =
      ∧-intro (closLive-pend c ins (lookup Γ i) ok (resolve 0 async)) refl
... | scripted (cold _ _) = refl   -- mkHot returns []
... | shared _            = refl   -- mkHot returns []

----------------------------------------------------------------------
-- STEP 5.  The main proof.
--
-- capsOK? (right-assoc ∧):
--   stBounded? B sched st
--   ∧ regsSz? B (registry st)
--   ∧ all (widLive W slots) live
--   ∧ all (widNode W slots) nodes
--   ∧ (length registry ≤ᵇ cReg)
--
-- At init: registry = [], nodes = [], live = concat (tabulate (mkHot ins))
-- So conjuncts (2),(4),(5) are trivially refl; (1) and (3) use concat-tab.
----------------------------------------------------------------------

init-capsOK?-base-go : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  → capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true
init-capsOK?-base-go {n = n} e ins =
  let B = 2 + sizeᵉ e + slotsSize ins
      W = suc (entryCeil n ins e)
      -- (1) stBounded? = all (boundedLive B) live ∧ all _ nodes
      --     nodes = [] → all _ [] = refl
      --     live = concat (tabulate (mkHot ins)):
      C1 = all-concat-tab (boundedLive B) (mkHot ins)
             (λ i → mkHot-bounded ins B i
                      (≤-trans
                        (fᵢ≤sum-tab (λ j → slotSize (ins j)) i)
                        -- slotsSize ins ≤ (2 + sizeᵉ e) + slotsSize ins = B
                        (m≤n+m (slotsSize ins) (2 + sizeᵉ e))))
      -- (3) all (widLive W ins) live
      C3 = all-concat-tab (widLive W ins) (mkHot ins)
             (λ i → widLive-mkHot W ins i)
      -- (7) all (closLive (baseCaps e ins) ins) live
      C7 = all-concat-tab (closLive (baseCaps e ins) ins) (mkHot ins)
             (λ i → closLive-mkHot (baseCaps e ins) ins i)
  in
  ∧-intro (∧-intro C1 refl)          -- (1) ∧-true  stBounded? ∧ []
    (∧-intro refl                     -- (2) regsSz? [] = refl
      (∧-intro C3                     -- (3) widLive live
        (∧-intro refl                 -- (4) widNode [] = refl
          (∧-intro refl               -- (5) 0 ≤ᵇ suc _ = refl
            (∧-intro refl             -- (6) parkRoom [] = refl
              (∧-intro C7             -- (7) closLive live
                (≤ᵇ-true n n ≤-refl))))))) -- (8) sched-init sets nextSource = n

abstract
  init-capsOK?-base : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    → capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true
  init-capsOK?-base = init-capsOK?-base-go
