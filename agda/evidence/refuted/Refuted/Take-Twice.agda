-- AN ELABORATED `take` SUBSCRIBES ITS SOURCE TWICE, SO OVER A COLD WITH
-- A LIFETIME THE IMPL'S SCHEDULE HOLDS TWO ARRIVALS FOR EVERY ONE OF THE
-- PLAIN RUN'S, AND THE TWO RUNS STOP AGREEING AT EQUAL FUEL.
--
-- WHERE THE SECOND SUBSCRIPTION COMES FROM.  `takeᵖ` ends on a
-- take-until because the palette has no take-while: the counted stream
-- is a switch's first lane, and the cut is the first emit of a SECOND
-- subscription to the same count.  A share or a hot slot fans one
-- arrival out to both registrations inside one cascade, which is the
-- case the gadget was written for.  A cold is a dynamic source minted
-- per subscription, so the second subscription is a second live source
-- with the same ticks under a later ordinal, and every tick costs the
-- drain two units of fuel.  The TypeScript mirror ends on
-- `takeWhile(p, true)` over one subscription and pays one.
--
-- WHAT IT COSTS AT ONE ARRIVAL.  `take 2` over a cold whose script sends
-- 5 and then 6: the plain run puts out 6 at its second arrival; the impl
-- puts out nothing there, since that arrival is the cut lane's copy of
-- the 5, and puts the 6 out at its third and nothing at its fourth.
-- Every value still arrives, in order, so at this program it is a fuel
-- finding and not a disagreement about values; but the slice at arrival
-- 2 is empty on one side and not the other, and the whole run at fuel 2
-- holds one value against two.
--
-- AND THE TOP LINE'S ONE FUEL OF SLACK DOES NOT COVER IT.  The plain run
-- at fuel 2 holds 5 and 6, and the impl's batches joined at fuel 3 hold
-- only the 5: its third arrival delivers the 6, and the batcher is still
-- holding that group open for an arrival that would close it.
--
-- WHY NO FIXED SLACK REPAIRS IT.  Each `take` doubles the cold sources
-- beneath it, so nested takes, or a take re-subscribed through `μ`,
-- multiply the impl's arrivals per plain arrival without bound.
--
-- SO THE STATEMENTS GIVE THE IMPL ITS OWN FUEL, AND THE EQUAL-FUEL FORMS
-- ARE STATED HERE (Anthony).  `src` restated all three with an impl fuel
-- no less than the plain run's; what these refute is the form that tied
-- the two fuels together.
module Refuted.Take-Twice where

open import Data.Bool using (T)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_; map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Pointwise.Properties using (Pointwise-length)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; cold; after_,_)
open import Rx.Exp using (Ctx; natᵗ; isData)
open import SExp.Syntax using (SExp; Kinds; plainᵏ; inputˢ; takeˢ; natˢ; emptyˢ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Pipeline using (runᴵ; runᴾ)
open import Batchable.Inst-Extract using (instExtract)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Simulation.Statement using (Agrees; arrivalsOf; sliceAt; stampedAt; plainAt)
open import Left-To-Right.Statement using (joinedᴵ)

-- the slices at one fuel, impl against plain
Arrival-Values-Equal : Set
Arrival-Values-Equal =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) (k : ℕ) →
  Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
            (sliceAt (stampedAt κ e ins) k) (sliceAt (plainAt κ e ins) k)

-- the runs at one fuel, impl against plain
Simulation-Equal : Set
Simulation-Equal =
  ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Pointwise (λ p w → Agrees (plainᵏ Γ κ) Γ t (proj₂ p) w)
            (instExtract (runᴵ κ fuel e ins)) (runᴾ fuel e ins) ×
  Σ (ℕ → Id) λ name → (∀ {a b} → name a ≡ name b → a ≡ b) ×
    map proj₁ (instExtract (runᴵ κ fuel e ins)) ≡ map name (arrivalsOf fuel e ins)

-- the batches joined at one fuel and one more, against the plain run
Left-To-Right-Equal : Set
Left-To-Right-Equal =
  ∀ {n} {Γ : Ctx n} {t} (ok : T (isData t)) (κ : Kinds n) (fuel : Fuel)
    (e : SExp Γ [] [] [] t) (ins : SimulSlots Γ κ) →
  Prefix _≡_ (joinedᴵ ok κ fuel e ins) (runᴾ fuel e ins) ×
  Prefix _≡_ (runᴾ fuel e ins) (joinedᴵ ok κ (suc fuel) e ins)

-- the cold's script: 5 one tick in, 6 one tick after it
κ : Kinds 2
κ = κOf (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ []))

ins : SimulSlots Γ₂ κ
ins = mkSlots (cold [] ((after 1 , 5) ∷ (after 0 , 6) ∷ [])) emptyˢ

take-two : SExp Γ₂ [] [] [] natᵗ
take-two = takeˢ (natˢ 2) (inputˢ zero)

-- the impl's slice at arrival 2 is empty and the plain run's holds 6
arrival-values-false : ¬ Arrival-Values-Equal
arrival-values-false av with Pointwise-length (av κ take-two ins 2)
... | ()

-- at fuel 2 the impl has put out 5 and the plain run 5 and 6
simulation-false : ¬ Simulation-Equal
simulation-false sim with Pointwise-length (proj₁ (sim κ 2 take-two ins))
... | ()

-- the plain run at fuel 2 is 5 and 6; the impl's batches at fuel 3 join
-- to the 5 alone
left-to-right-false : ¬ Left-To-Right-Equal
left-to-right-false ltr with proj₂ (ltr tt κ 2 take-two ins)
... | refl ∷ ()
