-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN'S CEILING ENTRY IS THE SAME BASE-CAP DEFECT ONE CURRENCY
-- OVER, and the currency is GAS rather than size.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  The drain's per-entry predicate asks, beside
-- the three readings `Refuted.Drain-Queue-Flat` already moved up to the
-- walk's own level, for a ceiling entry: a gas and a level the cascade
-- REACHED, with the gas above four plus the parked term's nesting.
-- Every other conjunct is now read at the level the walk is standing
-- at, so the cheap reading is that this one travels the same way --
-- the walk arrives holding a reached level of its own, and hands it
-- over.
--
-- WHY IT CANNOT WORK, AND IT IS THE LEVEL AGAIN.  A reached gas is
-- capped by the BASE size cap and by nothing else: the relation is
-- rooted at `suc` the entry size and every step spends one, so
-- `reached-gas` below reads the ceiling straight off the constructors.
-- The nesting on the other side is bounded only at the cap the walk has
-- STEPPED to, and one step multiplies the size by better than the size
-- itself.  So the demand is four plus a nesting free up to the stepped
-- cap, under `suc` the entry cap, and the family that sits in that gap
-- is the one the sibling file already built.
--
-- AND THE LEVEL IS LOAD-BEARING RATHER THAN DECORATION, which
-- `drain-reach-gas-base` says in the affirmative: at level zero the
-- room floor the entry already carries -- three units above the term
-- beside the slots, under the entry cap -- IS the gas floor, with the
-- bottom constructor supplying the reached level for nothing.  So the
-- obligation is met exactly where the step is the identity, and
-- refuted at the next level up.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Drain-Reach-Gas where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-monoʳ-≤)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Nest using (nest; nest≤)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Ceiling using (Reached; base; walk)

-- a slot-free program, so nothing here turns on the telescope: the
-- deficit this file is about is the LEVEL and nothing else
Γ₀ : Ctx 0
Γ₀ = []

sl₀ : Slots Γ₀
sl₀ ()

o₇ : Closed Γ₀ natᵗ
o₇ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

c₈ : Caps
c₈ = caps 8 1 1

----------------------------------------------------------------------
-- THE CEILING ON A REACHED GAS, off the constructors: the bottom is
-- reached with `suc` the entry size, and every walk step spends one
----------------------------------------------------------------------

reached-gas : ∀ (c : Caps) (d Lv g : ℕ) → Reached c d Lv g →
  g ≤ suc (Caps.cSize c)
reached-gas c d _ _ base                = ≤-refl
reached-gas c d _ _ (walk J g i hi r) =
  ≤-trans (n≤1+n g) (reached-gas c d J (suc g) r)

----------------------------------------------------------------------
-- THE ROW.  The parked term is admitted by one step of the entry cap
-- and refused by the base gas by four
----------------------------------------------------------------------

gasValUp₈ : nestValOK? (frameStep 1 c₈) (obs natᵗ) o₇ ≡ true
gasValUp₈ = refl

nest₈ : nest o₇ sl₀ [] ≡ 9
nest₈ = refl

room₈ : 3 + (sizeᵉ o₇ + slotsSize sl₀) ≡ 12
room₈ = refl

stepSize₈ : Caps.cSize (frameStep 1 c₈) ≡ 136
stepSize₈ = refl

baseGas₈ : suc (Caps.cSize c₈) ≡ 9
baseGas₈ = refl

DrainReachGas : Set
DrainReachGas = ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (cs : List Source) (d L : ℕ) (o : Val Γ (obs u)) →
  nestValOK? (frameStep L c) (obs u) o ≡ true →
  3 + (sizeᵉ o + slotsSize sl) ≤ Caps.cSize (frameStep L c) →
  Σ ℕ λ g → Σ ℕ λ Lv′ →
    (4 + nest o sl cs ≤ g) × (L ≤ Lv′) × Reached c d Lv′ g

drain-reach-gas-absurd : DrainReachGas → ⊥
drain-reach-gas-absurd f
  with f c₈ sl₀ [] 0 1 o₇ gasValUp₈
         (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))
... | g , Lv′ , hg , hL , r
  with ≤-trans hg (reached-gas c₈ 0 Lv′ g r)
... | s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))

----------------------------------------------------------------------
-- AND THE SAME OBLIGATION AT LEVEL ZERO, WHICH IS MET.  Four plus the
-- nesting is under the room floor the entry already carries, since the
-- sync spine is under the whole size and the residue under the slots,
-- and the bottom of the relation is reached carrying exactly that gas
----------------------------------------------------------------------

drain-reach-gas-base : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (cs : List Source) (d : ℕ) (o : Val Γ (obs u)) →
  3 + (sizeᵉ o + slotsSize sl) ≤ Caps.cSize c →
  Σ ℕ λ g → Σ ℕ λ Lv′ →
    (4 + nest o sl cs ≤ g) × (0 ≤ Lv′) × Reached c d Lv′ g
drain-reach-gas-base c sl cs d o hroom =
  suc (Caps.cSize c) , 0
  , s≤s (≤-trans (+-monoʳ-≤ 3 (nest≤ o sl cs)) hroom)
  , z≤n
  , base
