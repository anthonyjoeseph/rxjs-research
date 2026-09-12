-- THE FIT DOES NOT HOLD AT THE DOOR, AND THE WITNESS IS A RUN RATHER
-- THAN A STATE SOMEONE WROTE DOWN.
--
-- EVIDENCE, not a claim: `src` cannot import this tree and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- WHAT `hopFits` COMPARES.  Its left side prices what the chains in the
-- registry can still reach; its right the reading of the program those
-- chains were built from, both under `slotRd` off the schedule's own
-- telescope — there is no environment left for a caller to pick, which
-- is what makes a failure here a fact about the run and not about a
-- reading nobody uses.
--
-- WHY THE TWO COME APART.  The slot is SCRIPTED, and the syntax forces
-- a scripted slot's components to zero, so the right side reads the
-- program as if the arriving value were inert.  The root subscribe then
-- builds a chain THROUGH that slot — a flatten over a map over the
-- input — and the chain's own frames read two.  So the deficit is not a
-- matter of degree that a larger program would close: the right side is
-- blind, by construction, to exactly the layers the left side is
-- counting.
--
-- WHAT THIS DOES NOT SAY.  It kills the fit as an unconditional
-- property of the door, not the descent that consumes it: the drain
-- leaf takes `hopFits` as a HYPOTHESIS and is separately instantiated
-- at runs where it holds.  What has no witness after this is the claim
-- that every root subscribe hands the drain a state satisfying it.
--
-- AND THE ROWS AT THE END SAY HOW MUCH THE CONDITIONING WAS BUYING,
-- WHICH IS THE HALF WORTH READING TWICE.  The same family is run out to
-- twenty-four deliveries under ONE arrival: the values handed out read
-- twenty-four against a term still reading one, the fit is false
-- throughout — and the drain is DRY-FREE anyway.  So the fit is not
-- merely unavailable at the door, it is not necessary for the
-- conclusion it was introduced to support, and a repair that merely
-- weakens it enough to hold is repairing the wrong thing.
module Refuted.Entry-Fit where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; s≤s)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init; hasDry)
open import Verify-Rank-Sufficient.Hop using (hopFits; regsDepth)

----------------------------------------------------------------------
-- THE STATEMENT, RESTATED.  `hopFits` itself is IMPORTED rather than
-- spelled out, so a repair to the fit makes this witness fail to
-- typecheck — which is the answer this file exists to give, and it is
-- currently no.
----------------------------------------------------------------------

EntryHopFits : Set
EntryHopFits = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
              (st-init e)
  in hopFits (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))

----------------------------------------------------------------------
-- THE ADVERSARIAL RUN.  One slot, scripted, with an EMPTY synchronous
-- part and a single late value: the subscribe frame delivers nothing,
-- so every layer the registry holds was put there by the chain the root
-- built and not inherited from a burst.  The program flattens a map of
-- the arriving value into a six-element literal and folds over the
-- result, which is the smallest shape whose chain reaches past a
-- scripted slot's zero reading.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insLate : Slots Γ₁
insLate zero = scripted (cold [] (after 0 , 9 ∷ []))

step : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

burst6 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst6 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

casc6 : Closed Γ₁ (obs natᵗ)
casc6 = scanᵉ step (strmᵗ emptyᵉ) (mergeAllᵉ nothing (mapᵉ burst6 (input zero)))

ent₆ : Stream Γ₁ (obs natᵗ) × Sched Γ₁ × EvalSt casc6
ent₆ = subscribeE (rootWitness casc6 insLate) casc6 root 0 0
         (sched-init casc6 insLate) (st-init casc6)

ψ₆ : Fin 1 → Rd₃
ψ₆ = slotRd (Sched.slots (proj₁ (proj₂ ent₆)))

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl` ON EACH SIDE SEPARATELY rather than
-- computed inside the ⊥.  Either figure moving makes this file go red
-- at the pin, which is what stops the witness quietly agreeing with a
-- repaired statement that happens to still be false.
----------------------------------------------------------------------

regs₆ : regsDepth ψ₆ (EvalSt.registry (proj₂ (proj₂ ent₆))) ≡ 2
regs₆ = refl

term₆ : depthᵉ ψ₆ casc6 ≡ 1
term₆ = refl

entry-hop-fits-false : EntryHopFits → ⊥
entry-hop-fits-false h with h casc6 insLate
... | s≤s ()

----------------------------------------------------------------------
-- HOW MUCH THE FIT WAS BUYING, in the currency the fit itself is
-- denominated in.  `carried` is the deepest value a run hands out; two
-- payloads abreast cost what the deeper costs, which is the clause the
-- measure uses, so this is the friendliest reading available.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop ψ []             = 0
evHop ψ (value v ∷ es) = depthᵉ ψ v ⊔ evHop ψ es
evHop ψ (_ ∷ es)       = evHop ψ es

carried : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
          Stream Γ (obs u) → ℕ
carried ψ []         = 0
carried ψ (em ∷ ems) = evHop ψ (InstEmit.events em) ⊔ carried ψ ems

drainAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) (ins : Slots Γ) →
          Stream Γ t
drainAt f e ins =
  let ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
              (st-init e)
  in drain f 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))

burst24 : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
burst24 = strmᵗ (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ nat̂ 7
  ∷ nat̂ 8 ∷ nat̂ 9 ∷ nat̂ 10 ∷ nat̂ 11 ∷ nat̂ 12 ∷ nat̂ 13 ∷ nat̂ 14 ∷ nat̂ 15
  ∷ nat̂ 16 ∷ nat̂ 17 ∷ nat̂ 18 ∷ nat̂ 19 ∷ nat̂ 20 ∷ nat̂ 21 ∷ nat̂ 22 ∷ nat̂ 23
  ∷ nat̂ 24 ∷ []))

casc24 : Closed Γ₁ (obs natᵗ)
casc24 = scanᵉ step (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (mapᵉ burst24 (input zero)))

-- the subscribe frame contributes nothing: every layer below was grown
-- under the one arrival and not inherited from the root's own burst
burst₆ : carried ψ₆ (proj₁ ent₆) ≡ 0
burst₆ = refl

-- ONE unit of fuel is one arrival, and the reading is already the whole
-- source length; a second unit moves it no further, which is what says
-- the growth was one cascade's and not a queue drained one per unit
grow₁ : carried ψ₆ (drainAt 1 casc6 insLate) ≡ 6
grow₁ = refl

grow₂ : carried ψ₆ (drainAt 2 casc6 insLate) ≡ 6
grow₂ = refl

-- and the axis runs as far as one cares to push it, against a term
-- reading that does not move at all
term₂₄ : depthᵉ ψ₆ casc24 ≡ 1
term₂₄ = refl

grow₂₄ : carried ψ₆ (drainAt 1 casc24 insLate) ≡ 24
grow₂₄ = refl

-- THE ROW THAT MAKES THE REFUTATION A DESIGN FINDING RATHER THAN A
-- REPAIR ORDER.  The fit is false at this door too, yet the conclusion
-- it was introduced to support holds anyway — so what the door owes the
-- drain is not this comparison made satisfiable.
dry₂₄ : hasDry (drainAt 1 casc24 insLate) ≡ false
dry₂₄ = refl
