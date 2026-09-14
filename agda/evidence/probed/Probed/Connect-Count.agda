-- TARGET: connect-drops @ff369a
--
-- THE CONNECT EDGE'S ARITHMETIC, AT SLOT TABLES BUILT BY HAND.
--
-- The claim is that connecting a slot the connected set does not
-- already hold moves the unconnected count strictly down.  It reads no
-- program: `unconn` tabulates the slot table and counts the `shared`
-- entries whose index is absent from the set, so the whole statement is
-- a fact about a list gaining an element.  That is exactly what makes
-- it worth instantiating rather than reasoning about — the arithmetic
-- is decidable at any concrete table, so a row here is a `refl`-grade
-- check of the one component of the order that counts rather than
-- measures.
--
-- WHAT THE ROWS COVER AND WHAT THEY DO NOT.  Tables of one, two and
-- three `shared` slots, connected at the head with the set empty, with
-- one unrelated index already in it, and with slack left over — the
-- last being the load-bearing one, since a drop of exactly one has to
-- stay STRICT while other slots remain uncounted.  Not reached: a
-- `scripted` slot, which contributes nought to both sides and so can
-- only widen the gap; and the premise's own false branch, which is a
-- refutation rather than a row and is where the membership hypothesis
-- came from in the first place.
module Probed.Connect-Count where

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; nat̂; strmᵗ; ofᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (unconn)
open import Rx.Evaluator.Doorless using (connect-drops)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- ONE DEFINITION, REUSED AT EVERY WIDTH.  It writes a single numeral,
-- because nothing here reads the program at all.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = obs natᵗ ∷ []

d₁ : Closed Γ₁ (obs natᵗ)
d₁ = ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])

sl₁ : Slots Γ₁
sl₁ zero    = shared d₁
sl₁ (suc ())

Γ₃ : Ctx 3
Γ₃ = obs natᵗ ∷ obs natᵗ ∷ obs natᵗ ∷ []

d₃ : Closed Γ₃ (obs natᵗ)
d₃ = ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])

sl₃ : Slots Γ₃
sl₃ zero                = shared d₃
sl₃ (suc zero)          = shared d₃
sl₃ (suc (suc zero))    = shared d₃
sl₃ (suc (suc (suc ())))

----------------------------------------------------------------------
-- THE COUNTS, PINNED SO THAT A CHANGE TO `unconn` FAILS HERE RATHER
-- THAN SILENTLY REDENOMINATING THE ROWS BELOW.
----------------------------------------------------------------------

row-one-count : unconn sl₁ [] ≡ 1
row-one-count = refl

row-three-count : unconn sl₃ [] ≡ 3
row-three-count = refl

row-three-one-taken : unconn sl₃ (2 ∷ []) ≡ 2
row-three-one-taken = refl

----------------------------------------------------------------------
-- THE ROWS.  Each is the target applied at a table and a set, so the
-- type is generated from the statement as it reads and the body is the
-- inequality the table computes to.
----------------------------------------------------------------------

-- LOAD-BEARING at the floor: the last unconnected slot, whose connect
-- has to take the count to nought STRICTLY.  It fails the moment
-- `unconnAt` stops reading the membership it is handed.
row-last-slot : Confirms (connect-drops sl₁ [] zero refl)
row-last-slot = s≤s z≤n

-- LOAD-BEARING, and it is the one with slack: two slots stay
-- unconnected either side, so the claim is `1 < 2` rather than a drop
-- to nought, and a count that moved by nought or by two would fail
-- here while the row above stayed green.
row-with-slack : Confirms (connect-drops sl₃ (2 ∷ []) zero refl)
row-with-slack = s≤s (s≤s z≤n)

-- LOAD-BEARING on the set's shape: the index connected is not the head
-- of the set, so the count has to read membership rather than length.
row-not-head : Confirms (connect-drops sl₃ (2 ∷ []) (suc zero) refl)
row-not-head = s≤s (s≤s z≤n)
