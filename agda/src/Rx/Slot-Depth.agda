------------------------------------------------------------------
-- WHAT A SLOT REFERENCE IS WORTH: the environment `Rx.Obs-Depth` is
-- parameterised over, and the only one anybody means.
--
-- A reference is one symbol standing for a definition of any nesting,
-- so the number it reads has to be the DEFINITION's own — and that is
-- well defined because the telescope is STRATIFIED (`Rx.Slots`: slot
-- k's definition references only inputs at strictly smaller indices),
-- which makes a per-slot reading computable by recursion on the slot
-- index.  `ηAt` builds the stage-k environment — right below k, nought
-- at and above it — and `slotDepth` reads each slot off its own stage.
-- Nothing here recurses on a term while its environment is still being
-- built, so the whole construction is structural.
--
-- THE FIXPOINT IS THE PRODUCT, and it is what a connect spends: at a
-- shared slot the staged number IS the definition's reading under the
-- full environment, so a connect re-seeding the rank at the definition
-- discharges the caller's entry invariant by reflexivity rather than by
-- an inequality anything has to carry.  It holds because the reading
-- touches η only at inputs the term contains, and stratification
-- confines those to indices where the stage already agrees — which is
-- exactly `Rx.Obs-Depth.Eta-Cong.dep-η-congᵉ` and `ηAt-agrees` below,
-- and nothing more is needed.
--
-- RECOVERY: git show 919f115:agda/src/Rx/Slot-Hop.agda holds the same
--   construction over the deleted budget's hop measure, with a probe
--   trail behind it; the shape transfers, the quantity it was taken
--   over does not.
------------------------------------------------------------------
module Rx.Slot-Depth where

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans; cong; sym; subst)

open import Rx.Exp using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Obs-Depth using (depᵉ)
open import Rx.Obs-Depth.Eta-Cong using (dep-η-congᵉ)

-- one slot's reading, given an environment for the inputs its
-- definition may reference.  A scripted slot carries data only
-- (`isData`), so no emission of its can hold an observable at all.
slotDepthD : ∀ {n} {Γ : Ctx n} {k t} (η : Fin n → ℕ) → Slot Γ k t → ℕ
slotDepthD η (scripted _) = 0
slotDepthD η (shared d)   = depᵉ η 0 d

-- the stage-k environment: the true readings at indices < k, nought at
-- and above.  Structural on k — this is the recursion stratification
-- pays for.
ηAt : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → ℕ
ηAt sl zero    i = 0
ηAt sl (suc k) i =
  if toℕ i ≡ᵇ k then slotDepthD (ηAt sl k) (sl i)
                else ηAt sl k i

-- THE ENVIRONMENT: each slot read off its own stage
slotDepth : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → ℕ
slotDepth sl i = slotDepthD (ηAt sl (toℕ i)) (sl i)

-- THE STAGE IS ALREADY RIGHT WHERE IT CLAIMS TO BE: below k, `ηAt`'s
-- answer IS the fixpoint's.  Induction on k.  At zero the guard is
-- uninhabited and the statement is vacuous; at `suc k` the stage
-- branches on `toℕ j ≡ᵇ k`, and either both sides are the same reading
-- once the index equality is transported, or the guard and the branch
-- together give `toℕ j < k` and the induction hypothesis closes it.
ηAt-agrees : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ)
  (j : Fin n) → T (toℕ j <ᵇ k) →
  ηAt sl k j ≡ slotDepth sl j
ηAt-agrees sl zero    j ()
ηAt-agrees sl (suc k) j lt with toℕ j ≡ᵇ k in eqb
... | true  =
  cong (λ m → slotDepthD (ηAt sl m) (sl j))
       (sym (≡ᵇ⇒≡ (toℕ j) k (subst T (sym eqb) tt)))
... | false =
  ηAt-agrees sl k j
    (<⇒<ᵇ (≤∧≢⇒< (≤-pred (<ᵇ⇒< (toℕ j) (suc k) lt))
                 (λ e → subst T eqb (≡⇒≡ᵇ (toℕ j) k e))))

-- THE FIXPOINT, assembled.
slotDepth-fix : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
  sl i ≡ shared d {ok = ok} →
  slotDepth sl i ≡ depᵉ (slotDepth sl) 0 d
slotDepth-fix sl i {d} {ok} eq =
  trans (cong (slotDepthD (ηAt sl (toℕ i))) eq)
        (dep-η-congᵉ (toℕ i) 0 (ηAt-agrees sl (toℕ i)) d ok)
