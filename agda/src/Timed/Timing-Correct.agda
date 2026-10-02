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

open import Data.List    using (List; [])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Product using (_×_; proj₁; proj₂)
open import Function     using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel; Id)
open import Rx.Exp        using (Ctx; Val)
open import SExp.Syntax      using (SExp; Kinds; plainᵏ; plainᵗ)
open import SExp.Simul-Slots using (SimulSlots)
open import Timed.Translation     using (timed; timedSlots; packetOf; timedᶜ; itemᵗ)
open import SExp.Pipeline using (runᴵ)
open import Batchable.Inst-Extract using (instExtract)

-- the impl's run of the timed program: each value with its stamp
stampedᵀ : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
         → List (Id × Val (plainᵏ (timedᶜ Γ κ) κ) (plainᵗ (itemᵗ t)))
stampedᵀ κ fuel e ins = instExtract (runᴵ κ fuel (timed κ e) (timedSlots ins))

-- same stamp exactly when same packet
Coherent : ∀ {m} {Γ′ : Ctx m} t → (p q : Id × Val Γ′ (plainᵗ (itemᵗ t))) → Set
Coherent t p q = (proj₁ p ≡ proj₁ q) ⇔ (packetOf t (proj₂ p) ≡ packetOf t (proj₂ q))

Timing-Correct : Set
Timing-Correct =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel) (e : SExp Γ [] [] [] t)
    (ins : SimulSlots Γ κ) →
  AllPairs (Coherent t) (stampedᵀ κ fuel e ins)

postulate
  -- PROBED: `Probed.Timing-Correct` -- `AllPairs` decided at fuel 30 over three
  --   first-order programs: a scripted slot taken to one of two arrivals,
  --   the script's two arrivals kept (two instants), and a literal of two
  --   values (one instant).  Not a flattener, a share, a `μ` nor a cold
  --   slot: a flattener's run does not reduce in the typechecker inside 8 GB
  --   at fuel 30 or 3, so those shapes are `make quickcheck`'s alone. The
  --   take stamps one item and is degenerate.
  timing-correct : Timing-Correct
