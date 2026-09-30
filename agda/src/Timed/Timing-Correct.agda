------------------------------------------------------------------
-- TIMING-CORRECT: the impl's instant stamps group emits exactly as the
-- timed translation's packets do.
--
-- CLOSES A CHEAT THE OTHER TOP-LINE STATEMENTS LEAVE OPEN.  Stamping
-- every emit with one instant, or each with its own, fails
-- timing-correct, since the packets are the translation's and not the
-- impl's to arrange.
--
-- EVERY PAIR OF VALUES THE IMPL EMITS FOR A TIMED PROGRAM: same stamp
-- exactly when same packet.  END items carry packets too, so a
-- completion's instant is pinned as well as a value's.
------------------------------------------------------------------
module Timed.Timing-Correct where

open import Data.List    using ([])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Product using (proj₁; proj₂)
open import Function     using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel)
open import Rx.Exp        using (Ctx)
open import SExp.Syntax      using (SExp; Kinds)
open import SExp.Simul-Slots using (SimulSlots)
open import Timed.Translation     using (timed; timedSlots; packetOf)
open import SExp.Pipeline using (runᴵ)
open import Batchable.Inst-Extract using (instExtract)

Timing-Correct : Set
Timing-Correct =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  AllPairs (λ p q → (proj₁ p ≡ proj₁ q) ⇔ (packetOf t (proj₂ p) ≡ packetOf t (proj₂ q)))
           (instExtract (runᴵ κ fuel (timed κ e) (timedSlots ins)))

postulate
  timing-correct : Timing-Correct
