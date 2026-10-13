-- THE BATCHER CAN LAG THE RUN IT BATCHES BY MORE THAN ONE UNIT OF FUEL,
-- BECAUSE A UNIT OF FUEL IS AN ARRIVAL AND AN ARRIVAL CAN BE SILENT.
-- A batch leaves when the next instant's first emit or the run's
-- completion says its instant is over, and the arrival one unit past
-- the fuel may put nothing at all on the run.  Here two values a nested
-- `switchAll` hands out at subscribe are in the elaborated run at fuel
-- one, the second arrival is silent, and the batcher has emitted
-- nothing at fuel one or at fuel two -- so the batcher's sandwich with
-- its slack fixed at one unit past the run's own fuel is false.  The
-- compiled sweep found it at depth 3, seed 14, as a red `left-to-right`
-- at fuel one, which it is not: `left-to-right` names its own impl
-- fuel, and two works.
--
-- WHAT IT KILLS IS THE COUPLING, NOT THE BATCHER.  The batcher's joined
-- run reaches both values at fuel three.
module Refuted.Batched-Sandwich where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Exp using (Ctx; isData; natᵗ; mergeᶠ; switchᶠ)
open import Rx.Prim using (Fuel; ObservableInput; cold; after_,_)
open import SExp.Syntax using (SExp; Kinds; inputˢ; ofˢ; emptyˢ; scanˢ; varˢᵗ; natˢ; fstˢ; strmˢ; deferˢ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Readings using (joinedᴵ; valsᴵ)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots; flatAllˢ)

-- the batcher's sandwich read one unit of fuel past the run it batches
One-Past-Sandwich : Set
One-Past-Sandwich =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Prefix _≡_ (joinedᴵ ok κ fuel e ins) (valsᴵ ok κ fuel e ins) ×
  Prefix _≡_ (valsᴵ ok κ fuel e ins) (joinedᴵ ok κ (suc fuel) e ins)

-- seed 14, case 347 of the depth-3 sweep, as the binary printed it
prog : SExp Γ₂ [] [] [] natᵗ
prog =
  deferˢ (flatAllˢ switchᶠ (ofˢ (
      strmˢ (flatAllˢ switchᶠ (ofˢ (strmˢ (inputˢ (suc zero)) ∷ strmˢ emptyˢ ∷
                                    strmˢ (ofˢ (natˢ 5 ∷ natˢ 5 ∷ [])) ∷ [])))
    ∷ strmˢ (flatAllˢ (mergeᶠ (just 3))
               (scanˢ (strmˢ (flatAllˢ switchᶠ (ofˢ (fstˢ (varˢᵗ (here refl)) ∷ []))))
                      (strmˢ emptyˢ) (inputˢ zero)))
    ∷ [])))

script : ObservableInput ℕ
script = cold [] ((after 1 , 9) ∷ (after 0 , 7) ∷ [])

ins : SimulSlots Γ₂ (κOf script)
ins = mkSlots script (inputˢ zero)

-- the elaborated run holds both values at fuel one
vals₁ : valsᴵ tt (κOf script) 1 prog ins ≡ 5 ∷ 5 ∷ []
vals₁ = refl

-- and the batcher, one unit of fuel past it, has emitted nothing.  The
-- fuel is written as the statement writes it, so the refutation below
-- compares no run by evaluating it.
joined₂ : joinedᴵ tt (κOf script) (suc 1) prog ins ≡ []
joined₂ = refl

no-prefix : Prefix {A = ℕ} _≡_ (5 ∷ 5 ∷ []) [] → ⊥
no-prefix ()

one-past-sandwich-false : One-Past-Sandwich → ⊥
one-past-sandwich-false bs =
  no-prefix (subst (Prefix _≡_ (5 ∷ 5 ∷ [])) joined₂
              (subst (λ xs → Prefix _≡_ xs (joinedᴵ tt (κOf script) (suc 1) prog ins))
                     vals₁ (proj₂ (bs tt (κOf script) 1 prog ins))))
