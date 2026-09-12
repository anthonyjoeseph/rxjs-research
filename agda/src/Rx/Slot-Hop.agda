------------------------------------------------------------------
-- THE SLOT-HOP ENVIRONMENT: the η that `Rx.Hop-Depth`'s input clause
-- was parameterised FOR.
--
-- `hopDᵉ` reads η at `input i` and nowhere else, so every consumer of
-- the measure has to say which environment it means.  The constant-0
-- reading is FALSE rather than merely coarse: an obs-typed shared
-- slot's def emits values of positive hop, and a subscription
-- connecting to that slot receives them, so zeroing the share
-- boundary breaks at the first flattener over an input.  What is
-- built here is the honest one.
--
-- IT IS WELL DEFINED BECAUSE THE TELESCOPE IS STRATIFIED.  `Rx.Slots`
-- carries a side condition saying a shared def reads only inputs at
-- strictly smaller indices, so slot k's hop is computable by
-- recursion on k: `ηAt` builds the stage-k environment — correct
-- below k, zero at and above it — and `slotHop` reads each slot's hop
-- off its own stage.  That side condition is in the syntax for this
-- and discharges by unification at every concrete program.
--
-- THE FIXPOINT HALF IS WHAT A CONNECT SPENDS.  The staged number at a
-- shared slot IS the def's reading under the FULL environment, and
-- that equation is what turns the walk's input clause — which knows
-- only `η i` — into a statement about the def the connect is about to
-- subscribe.  It rests on `Rx.Hop-Eta-Cong` and on the staging lemma
-- below, and on no postulate.
------------------------------------------------------------------
module Rx.Slot-Hop where

open import Data.Nat  using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Fin  using (Fin; toℕ)
open import Data.Vec  using (lookup)
open import Data.Bool using (true; false; T; if_then_else_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; subst)

open import Rx.Exp       using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Hop-Eta-Cong using (hopD-η-congᵉ)

-- one slot's hop, given an environment for the inputs its def may
-- read.  A scripted slot carries data only (`isData`), so no emission
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

-- THE STAGE IS ALREADY RIGHT WHERE IT CLAIMS TO BE: below k, `ηAt`'s
-- answer IS the full environment's.
--
-- Induction on k.  At zero the guard is uninhabited and the statement
-- is vacuous.  At `suc k` the stage branches on `toℕ j ≡ᵇ k`: on TRUE
-- both sides are the same `slotHopD` once the index equality is
-- transported, since `slotHop` reads stage `toℕ j` and the stage here
-- is `k`; on FALSE the guard gives `toℕ j ≤ k` and the branch gives
-- `toℕ j ≢ k`, so the stage delegates one level down and the induction
-- hypothesis closes it.
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

-- THE FIXPOINT, assembled: a shared slot's def reads the SAME at its
-- own stage as under the full environment — which is the equation a
-- connect charges against, since what it is about to subscribe is the
-- def while what its invariant carries is the slot's number.
--
-- IT IS STATED AT THE DEF AND NOT AT THE SLOT, and that is what makes
-- it spendable.  A walk reaching a slot reference matches the telescope
-- before it can name the def at all, so by the time the obligation
-- exists the caller's number has ALREADY reduced through `slotHopD` to
-- the def at the stage.  An equation whose left side is `slotHop V sl
-- i` would then have to be bridged back across that very match, at the
-- one site that cannot see it.  The side condition is what is really
-- consumed here; the telescope equation is not needed and is not taken.
slotHop-fix : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (i : Fin n)
  (d : Closed Γ (lookup Γ i)) → T (inputsBelowᵉ (toℕ i) d) →
  hopDᵉ V (ηAt V sl (toℕ i)) d ≡ hopDᵉ V (slotHop V sl) d
slotHop-fix V sl i d ok =
  hopD-η-congᵉ V (toℕ i) (ηAt-agrees V sl (toℕ i)) d ok
