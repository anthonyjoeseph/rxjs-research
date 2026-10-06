-- A SLOT'S READ NEEDS THE TWO SCHEDULES TO HOLD THE SAME SCRIPT AT IT,
-- AND NOTHING IN A STORE SAYS SO.
--
-- WHAT THIS KILLS.  `cold-read` as stated: any `Store` over a cold
-- slot, any related path, the plain subscribe and the impl's machine
-- read, and an `After` comes out.  A `Store` relates live sources,
-- rows, latches and node pairs; it never reads `Sched.slots`, so the
-- two runs' scripts at a slot are free of each other.
--
-- THE WITNESS IS TWO RUNS AT THEIR OPENING.  The plain run's slot is
-- cold with an asynchronous tail, the impl's is cold with none.  At the
-- opening neither has a live source, a row or a node, so the empty
-- store relates them.  The plain subscribe registers the tail as a live
-- source and the impl's registers nothing, so no store relates the two
-- results: `sources` would pair a one-element list with an empty one.
-- The kind agrees at the slot, so the repair is not a kind; it is the
-- script.
module Refuted.Slot-Scripts where

open import Level using (Level)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Fin using (zero)
open import Data.List.Relation.Binary.Pointwise using ([])
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.List.Relation.Unary.All using ([])
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Rx.Prim using (cold; after_,_)
open import Rx.Mint using (setAt; sourceᵏ)
open import Rx.Evaluator using (Sched; sched-init; st-init)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; rule)
open import SExp.Syntax using (SExp; inputˢ; emptyˢ)
open import Rx.Exp using (natᵗ)
open import Simulation.Schedules using ([])
open import SExp.Plain using (plainExp)
open import SExp.Elaborate using (stampedSlot)
open import SExp.Simul-Slots using (plainSlots)
open import SExp.Pipeline using (elaborateImpl; embedSlotsImpl)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Simulation.Stores using (Store; module Store; root~; [])
open import Simulation.Walk using (cold-read; read-machine; minted)
open import Simulation.After using (module Kept)
open Kept using () renaming (after to kept)

-- the type of an application, the application itself irrelevant
Type-of : ∀ {ℓ : Level} {A : Set ℓ} → .(claim : A) → Set ℓ
Type-of {A = A} _ = A

-- the plain run's slot has a tail; the impl's, built at the same kind,
-- does not
insA = mkSlots (cold (3 ∷ []) ((after 1 , 4) ∷ [])) emptyˢ
insB = mkSlots (cold (3 ∷ []) []) emptyˢ

κ = κOf (cold (3 ∷ []) ((after 1 , 4) ∷ []))

prog : SExp Γ₂ [] [] [] natᵗ
prog = inputˢ zero

-- the impl's opening schedule under the token its mint drew
sI = record (sched-init (elaborateImpl κ prog) (embedSlotsImpl insB))
       { mint = setAt sourceᵏ (suc (proj₁ (minted κ prog insB)))
                  (Sched.mint (sched-init (elaborateImpl κ prog) (embedSlotsImpl insB))) }

-- both openings related: nothing live, nothing registered, nothing paired
opening : Store κ (sched-init (plainExp prog) (plainSlots insA)) (st-init (plainExp prog)) sI (st-init (elaborateImpl κ prog))
opening = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; pairs-below = [] , []
  ; sources = []
  ; numbers = []
  ; distinct = [] , []
  ; sync    = []
  ; rows    = []
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = [] , []
  ; swept   = []
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  }

-- every hypothesis met, at the root, and the conclusion empty
slot-scripts-false : ¬ Type-of (cold-read κ zero refl (λ x → x) (λ ()) (stampedSlot Γ₂ κ zero) opening root~
                                  (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp prog) (plainSlots insA))))
                                  (read-machine (λ x → x) (stampedSlot Γ₂ κ zero) _ (proj₂ (proj₂ (minted κ prog insB)))))
slot-scripts-false (kept S _ _ _ _ , _) with Store.sources S
... | ()
