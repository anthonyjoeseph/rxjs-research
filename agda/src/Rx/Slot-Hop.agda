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
-- indices where the stage already agrees with the fixpoint — that is
-- exactly what `hopD-η-congᵉ` (Rx.Hop-Eta-Cong) and `ηAt-agrees`
-- (below) say, and nothing more is needed.
--
-- BOTH ARE NOW PROVEN (2026-08-14), so slotHop-fix rests on no
-- postulate.  That matters beyond the count: the input-wet restatement
-- is built on this equation, so while these two were postulates the
-- repair for a machine-refuted statement was itself unverified.
------------------------------------------------------------------
module Rx.Slot-Hop where

open import Data.Nat  using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Unit using (tt)
open import Data.Fin  using (Fin; toℕ)
open import Data.Bool using (T; true; false; if_then_else_)
open import Data.Vec  using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans; cong; sym; subst)

open import Rx.Exp       using (Ctx; Closed; inputsBelowᵉ; isData; Val)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Prim      using (ObservableInput)
open import Rx.Hop-Depth using (hopDᵉ)
-- PROVEN (ex-postulate 2026-08-14): the η congruence slotHop-fix spends
open import Rx.Hop-Eta-Cong using (hopD-η-congᵉ)

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

-- THE STAGE IS ALREADY RIGHT WHERE IT CLAIMS TO BE — ex-postulate
-- (2026-08-14): below k, ηAt's answer IS the fixpoint's.
--
-- Induction on k.  At k = 0 the guard `T (toℕ j <ᵇ 0)` is ⊥ and the
-- statement is vacuous, which is exactly why Demand-Probe series W —
-- whose fixpoint rows sit at slot 0 — exercised nothing of it, and why
-- series T had to reach k = 1 and k = 2 before the probe meant
-- anything.  At `suc k` the stage branches on `toℕ j ≡ᵇ k`:
--
--   · TRUE: both sides are the same `slotHopD V (ηAt V sl _) (sl j)`
--     once the index equality is transported — `slotHop` reads stage
--     `toℕ j`, the stage here is `k`, and the branch condition says
--     they are the same number.
--   · FALSE: `toℕ j ≤ k` from the guard and `toℕ j ≢ k` from the
--     branch give `toℕ j < k`, so the stage delegates to itself one
--     level down and the IH closes it.
ηAt-agrees : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (k : ℕ)
  (j : Fin n) → T (toℕ j <ᵇ k) →
  ηAt V sl k j ≡ slotHop V sl j
ηAt-agrees V sl zero    j ()
ηAt-agrees V sl (suc k) j lt with toℕ j ≡ᵇ k in eqb
... | true  =
  cong (λ m → slotHopD V (ηAt V sl m) (sl j))
       (sym (≡ᵇ⇒≡ (toℕ j) k (subst T (sym eqb) tt)))
... | false =
  ηAt-agrees V sl k j
    (<⇒<ᵇ (≤∧≢⇒< (≤-pred (<ᵇ⇒< (toℕ j) (suc k) lt))
                 (λ e → subst T eqb (≡⇒≡ᵇ (toℕ j) k e))))

-- THE FIXPOINT, assembled: at a shared slot, slotHop's staged answer
-- is the def's hopD under the full slotHop environment — the equation
-- the walk face's input clause charges against.
-- AND THE SCRIPTED SIDE OF THE SAME FIXPOINT, which is the easy half and was
-- never stated: a scripted slot replays stored values and subscribes nothing,
-- so it contributes NO hop at all.  `slotHopD` says so outright, and the slot
-- equation is what carries that up to `slotHop`.
--
-- This is the bound a scripted `input i` reports against, because
-- `hopDᵉ V η (input i)` IS `η i` -- so at a scripted slot the hop budget a
-- clause must fit its emitted values into is exactly ZERO, which is why its
-- consumers pair this with the hopDᵛ emptiness of a data type.
slotHop-scripted : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (i : Fin n)
  {ok : T (isData (lookup Γ i))}
  (x : ObservableInput (Val Γ (lookup Γ i))) →
  sl i ≡ scripted {ok = ok} x → slotHop V sl i ≡ 0
slotHop-scripted V sl i x eq = cong (slotHopD V (ηAt V sl (toℕ i))) eq

slotHop-fix : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
  sl i ≡ shared d {ok = ok} →
  slotHop V sl i ≡ hopDᵉ V (slotHop V sl) d
slotHop-fix V sl i {d} {ok} eq =
  trans (cong (slotHopD V (ηAt V sl (toℕ i))) eq)
        (hopD-η-congᵉ V (toℕ i) (ηAt-agrees V sl (toℕ i)) d ok)
