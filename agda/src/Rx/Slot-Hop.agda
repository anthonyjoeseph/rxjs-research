------------------------------------------------------------------
-- THE HONEST SLOT-HOP ENVIRONMENT: the η that Rx.Hop-Depth's input
-- clause was parameterised FOR.
--
-- input-wet (Verify-Budget-Sufficient.Walk-Level, machine-checked)
-- refuted the constant-0 clause: an obs-typed shared slot's def emits
-- values of positive hop, so the walk face must charge the slot its
-- def's own hopD.  That number is well-defined because the telescope
-- is STRATIFIED (Rx.Slots: a shared def reads only inputs at strictly
-- smaller indices), so slot k's hop is computable by recursion on k —
-- ηAt builds the stage-k environment (correct below k, 0 at and above
-- it), and slotHop reads each slot's hop off its own stage.
--
-- THE FIXPOINT (slotHop-fix) is the fact the walk face consumes: at a
-- shared slot the staged number IS the def's hopD under the full
-- slotHop environment.  It holds because hopD only reads η at inputs
-- the term actually contains, and stratification confines those to
-- indices where the stage already agrees with the fixpoint — the two
-- postulated pieces (hopD-η-congᵉ, ηAt-agrees) say exactly that, and
-- nothing more is needed.
------------------------------------------------------------------
module Rx.Slot-Hop where

open import Data.Nat  using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Fin  using (Fin; toℕ)
open import Data.Bool using (T; if_then_else_)
open import Data.Vec  using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Rx.Exp       using (Ctx; Exp; Closed; inputsBelowᵉ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Hop-Depth using (hopDᵉ)

-- one slot's hop, given an environment for the inputs its def may
-- read.  A scripted slot carries data only (isData), so no emission
-- of its can hold an observable: hop 0.
slotHopD : ∀ {n} {Γ : Ctx n} {k t} (V : ℕ) (η : Fin n → ℕ) →
           Slot Γ k t → ℕ
slotHopD V η (scripted _) = 0
slotHopD V η (shared d)   = hopDᵉ V η d

-- the stage-k environment: the true hops at indices < k, 0 above.
-- Structural on k — this is the recursion stratification pays for.
ηAt : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (k : ℕ) → Fin n → ℕ
ηAt V sl zero    i = 0
ηAt V sl (suc k) i =
  if toℕ i ≡ᵇ k then slotHopD V (ηAt V sl k) (sl i)
                else ηAt V sl k i

-- THE ENVIRONMENT: each slot's hop off its own stage
slotHop : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) → Fin n → ℕ
slotHop V sl i = slotHopD V (ηAt V sl (toℕ i)) (sl i)

postulate
  -- hopD reads η only at the term's own inputs, so environments that
  -- agree below k agree on any term all of whose inputs sit below k.
  -- Mechanical mutual induction over Exp/Tm/List Tm; only the input
  -- clause touches η, and inputsBelowᵉ hands it exactly the guard the
  -- agreement hypothesis wants.
  hopD-η-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    hopDᵉ V η₁ e ≡ hopDᵉ V η₂ e

  -- the stage is already right where it claims to be: below k, ηAt's
  -- answer is the fixpoint's.  Induction on k; at toℕ j ≡ᵇ k the two
  -- sides are the same slotHopD after transporting the index equality,
  -- below it the stage delegates to itself and the IH closes.
  ηAt-agrees : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (k : ℕ)
    (j : Fin n) → T (toℕ j <ᵇ k) →
    ηAt V sl k j ≡ slotHop V sl j

-- THE FIXPOINT, assembled: at a shared slot, slotHop's staged answer
-- is the def's hopD under the full slotHop environment — the equation
-- the walk face's input clause charges against.
slotHop-fix : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
  sl i ≡ shared d {ok = ok} →
  slotHop V sl i ≡ hopDᵉ V (slotHop V sl) d
slotHop-fix V sl i {d} {ok} eq =
  trans (cong (slotHopD V (ηAt V sl (toℕ i))) eq)
        (hopD-η-congᵉ V (toℕ i) (ηAt-agrees V sl (toℕ i)) d ok)
