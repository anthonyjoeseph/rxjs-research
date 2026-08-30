-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN'S QUEUE CONJUNCTS CANNOT BE READ AT THE BASE CAP, so the
-- walk's own receipts do not deliver them at any level past the first.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  A `mergeAll` node's parked queue is drained
-- inside a frame the walk has already stepped into, and the drain's
-- own predicate asks three things of every parked term: its sync
-- spine under the cap, its closure under the cap, and room for its
-- syntax beside the slots.  All three are read at the ENTRY cap.  The
-- walk arrives holding exactly those readings -- at the cap it has
-- STEPPED to -- so the cheap repair is to hand them over.
--
-- WHY IT CANNOT WORK, AND THE LEVEL IS THE WHOLE OF IT.  A step is a
-- widening, so a term the walk admits at its own level is one the
-- entry cap may refuse, and the terms the walk parks are exactly the
-- ones built AT that level.  The rows below take the entry cap's size
-- at two, four and eight, step it once, and park a source whose spine
-- sits strictly between: admitted at the stepped cap by construction,
-- refused at the entry cap by construction.  So this is not a corner
-- of a chosen cap -- one step multiplies the size by better than the
-- size itself, and the gap it opens has a whole family inside it at
-- every cap at once.
--
-- AND THE LEVEL IS LOAD-BEARING RATHER THAN DECORATION: at level zero
-- the step is the identity, the premise reads the same cap as the
-- conclusion, and no instantiation could fail.  Every row here is at
-- one level, which is the smallest at which the claim says anything.
--
-- WHAT THIS DOES NOT KILL.  It says nothing about where the conjuncts
-- SHOULD sit.  Raising them to the walk's level is a separate claim
-- and dies separately, at the fit shelf the drain's grant is spent
-- against; `Refuted.Frame-Step-Compose` kills the other cheap repair,
-- re-basing that shelf at the walk's cap.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Drain-Queue-Flat where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; s≤s)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestValOK?; nestClosOK?)

-- a slot-free program, so nothing here turns on the telescope: the
-- deficit this file is about is the LEVEL and not the closure reading
Γ₀ : Ctx 0
Γ₀ = []

sl₀ : Slots Γ₀
sl₀ ()

----------------------------------------------------------------------
-- THE LADDER: an `ofᵉ` of k payloads has spine k + 2, so the family
-- reaches every size and a row can be placed anywhere in the gap
----------------------------------------------------------------------

o₁ : Closed Γ₀ natᵗ
o₁ = ofᵉ (nat̂ 0 ∷ [])

o₃ : Closed Γ₀ natᵗ
o₃ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

o₇ : Closed Γ₀ natᵗ
o₇ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

c₂ c₄ c₈ : Caps
c₂ = caps 2 1 1
c₄ = caps 4 1 1
c₈ = caps 8 1 1

----------------------------------------------------------------------
-- THE SPINE CONJUNCT
----------------------------------------------------------------------

valUp₂ : nestValOK? (frameStep 1 c₂) (obs natᵗ) o₁ ≡ true
valUp₂ = refl

valFlat₂ : nestValOK? c₂ (obs natᵗ) o₁ ≡ false
valFlat₂ = refl

valUp₄ : nestValOK? (frameStep 1 c₄) (obs natᵗ) o₃ ≡ true
valUp₄ = refl

valFlat₄ : nestValOK? c₄ (obs natᵗ) o₃ ≡ false
valFlat₄ = refl

valUp₈ : nestValOK? (frameStep 1 c₈) (obs natᵗ) o₇ ≡ true
valUp₈ = refl

valFlat₈ : nestValOK? c₈ (obs natᵗ) o₇ ≡ false
valFlat₈ = refl

DrainSpineFlat : Set
DrainSpineFlat = ∀ {n} {Γ : Ctx n} {u} (c : Caps) (L : ℕ) (o : Val Γ (obs u)) →
  nestValOK? (frameStep L c) (obs u) o ≡ true →
  nestValOK? c (obs u) o ≡ true

drain-spine-flat-absurd : DrainSpineFlat → ⊥
drain-spine-flat-absurd f with f c₈ 1 o₇ valUp₈
... | ()

----------------------------------------------------------------------
-- THE CLOSURE CONJUNCT, at the same rows: with no slots the telescope
-- is the identity, so what fails is the level and nothing else
----------------------------------------------------------------------

closUp₈ : nestClosOK? (frameStep 1 c₈) sl₀ o₇ ≡ true
closUp₈ = refl

closFlat₈ : nestClosOK? c₈ sl₀ o₇ ≡ false
closFlat₈ = refl

DrainClosFlat : Set
DrainClosFlat = ∀ {n} {Γ : Ctx n} {u} (c : Caps) (s : Slots Γ) (L : ℕ)
  (o : Val Γ (obs u)) →
  nestClosOK? (frameStep L c) s o ≡ true →
  nestClosOK? c s o ≡ true

drain-clos-flat-absurd : DrainClosFlat → ⊥
drain-clos-flat-absurd f with f c₈ sl₀ 1 o₇ closUp₈
... | ()

----------------------------------------------------------------------
-- THE ROOM FLOOR, which is the conjunct with no cap on the left at
-- all: three of overhead plus the term beside the slots, under the
-- ENTRY size.  The same parked term breaks it, and the three summands
-- make it break earlier than the spine conjunct rather than later
----------------------------------------------------------------------

roomUp₈ : sizeᵉ o₇ + slotsSize sl₀ ≡ 9
roomUp₈ = refl

roomFlat₈ : Caps.cSize c₈ ≡ 8
roomFlat₈ = refl

DrainRoomFlat : Set
DrainRoomFlat = ∀ {n} {Γ : Ctx n} {u} (c : Caps) (s : Slots Γ) (L : ℕ)
  (o : Val Γ (obs u)) →
  nestValOK? (frameStep L c) (obs u) o ≡ true →
  3 + (sizeᵉ o + slotsSize s) ≤ Caps.cSize c

drain-room-flat-absurd : DrainRoomFlat → ⊥
drain-room-flat-absurd f with f c₈ sl₀ 1 o₇ valUp₈
... | s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))) 

----------------------------------------------------------------------
-- THE TWO COLUMNS, packed base 100: the entry size against the size
-- one step buys it, at the three caps the rows are taken at
----------------------------------------------------------------------

flatSizes : ℕ
flatSizes = Caps.cSize c₂ + 100 * Caps.cSize c₄ + 10000 * Caps.cSize c₈

stepSizes : ℕ
stepSizes = Caps.cSize (frameStep 1 c₂) + 100 * Caps.cSize (frameStep 1 c₄)
          + 10000 * Caps.cSize (frameStep 1 c₈)

flatSizes≡ : flatSizes ≡ 80402
flatSizes≡ = refl

stepSizes≡ : stepSizes ≡ 1363610
stepSizes≡ = refl
