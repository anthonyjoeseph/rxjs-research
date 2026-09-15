-- THE CONNECT EDGE'S ARITHMETIC, ASKED WITHOUT KNOWING THE SLOT IS
-- SHARED.
--
-- The claim is that connecting a slot the connected set does not
-- already hold moves the unconnected count strictly down, and its only
-- premise is that membership reads `false`.  That premise is the one
-- the clause's own branch supplies, so it reads as the whole of what
-- the caller knows — and it is not, because the count is not over
-- slots, it is over SHARED slots.  A `scripted` slot reads nought
-- whatever the set holds, so connecting one moves nothing and the
-- strict drop fails on the nose.
--
-- AND THE WITNESS IS THE SMALLEST TABLE THERE IS, WHICH IS WHAT SAYS
-- THIS IS A MISSING HYPOTHESIS RATHER THAN AN EDGE CASE.  One slot,
-- the empty set, the only index available: every quantity in the
-- statement is at its floor and the claim still reads `0 < 0`.  No
-- arithmetic repair reaches it, because there is no arithmetic here to
-- repair — the table the count is taken over contains nothing the
-- count can see.
--
-- WHAT THE REPAIR HAS TO BE, AND IT IS NOT A WEAKENING.  The true
-- statement carries the slot's own shape as a premise, and the caller
-- holds it: the connect arm is reached only at a `shared` slot,
-- because a `scripted` one has no definition to subscribe.  So the
-- conditioned form REPLACES a false statement rather than shrinking a
-- true one.
module Refuted.Scripted-Connect where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Vec using () renaming (_∷_ to _∷ᵛ_; [] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; natᵗ)
open import Rx.Prim using (Source; hot)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (unconn; memberSource)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

-- THE STATEMENT, COPIED WITH NOTHING CHANGED.  A repair that weakens
-- the conclusion weakens this witness in the same edit.
ConnectDrops : Set
ConnectDrops =
  ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n)
  → memberSource (toℕ i) cs ≡ false
  → unconn sl (toℕ i ∷ cs) < unconn sl cs

-- LOAD-BEARING: the one-slot table that is scripted rather than
-- shared.  It is the only shape in the statement that is not forced,
-- and it is the one the premise says nothing about.
sl₁ : Slots Γ₁
sl₁ zero    = scripted (hot [])
sl₁ (suc ())

-- Both sides read nought, which is the finding: the count cannot see
-- the slot being connected at all.
row-before : unconn sl₁ [] ≡ 0
row-before = refl

row-after : unconn sl₁ (toℕ {1} zero ∷ []) ≡ 0
row-after = refl

-- and the set is empty, so the premise holds at its floor too
row-absent : memberSource (toℕ {1} zero) [] ≡ false
row-absent = refl

-- 0 is not below 0.
connect-drops-false : ConnectDrops → ⊥
connect-drops-false h with h sl₁ [] zero refl
... | ()
