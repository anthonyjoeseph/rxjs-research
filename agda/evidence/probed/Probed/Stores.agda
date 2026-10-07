-- THE STORES THE ROOT SUBSCRIBES INSTALL, related
-- by hand at concrete programs: the relation `Simulation.Stores` states,
-- inhabited against the registries the two runs actually compute.
-- TARGET: defer-install @d90562
module Probed.Stores where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import SExp.Syntax using (inputˢ)
open import Data.Sum using (inj₂)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero; suc; _<?_) renaming (_≟_ to _≟ℕ_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; ¬?)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_; allPairs?)
open import Data.List.Relation.Unary.All using ([]; _∷_; all?)
open import Data.Bool using (true; false; _≟_)
open import Data.Nat.Properties using (<-trans; n<1+n)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import SExp.Plain using (plainExp)
open import SExp.Simul-Slots using (plainSlots)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰)
open import Simulation.Walk using (defer-install; init-store; minted)
open import Simulation.After using (module Kept)
open Kept using (module After)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (slot~; dyn~; data~; defer~; hop; elab; here; root~; []; _∷_)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; defer-in)

-- a deferred hot read: the hop pending, its body not yet subscribed

_ : Confirms (After.store (proj₁ (defer-install (κᵖ defer-in) (inputˢ zero) (λ x → x) (λ ()) refl
                       (init-store (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in) _ (<-trans (proj₁ (proj₂ (minted (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in)))) (n<1+n _)))
                       {now = 0} root~ refl refl refl refl refl refl refl refl)))
_ = record
  { π       = (0 , 0 ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = [] ∷ []
  ; pairs-below = toWitness {a? = all? (λ _ → _ <? _) _} tt , toWitness {a? = all? (λ _ → all? (_<? _) _) _} tt
  ; sources = defer~ (toWitness {a? = _ <? _} tt) (hop (elab (inputˢ zero) (λ x → x) (λ ())) ∷ []) ∷ data~ refl (refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []
  ; numbers = dyn~ (toWitness {a? = _ <? _} tt) (toWitness {a? = _ <? _} tt) ∷ slot~ zero refl ∷ []
  ; distinct = (((λ ()) ∷ []) ∷ [] ∷ []) , (((λ ()) ∷ []) ∷ [] ∷ [])
  ; sync    = (refl , refl ∷ []) ∷ (refl , []) ∷ []
  ; rows    = defer~ here (here refl) refl refl root~ refl ∷ []
  ; dlv-alike = refl , tt
  ; dying-alike = refl , tt
  ; latches = λ { zero → (λ _ → refl , refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; bounded = toWitness {a? = all? (_<? _) _} tt , toWitness {a? = all? (_<? _) _} tt
  ; swept   = refl ∷ refl ∷ []
  ; uncut   = toWitness {a? = all? (λ _ → _ ≟ false) _} tt , toWitness {a? = all? (λ _ → _ ≟ false) _} tt
  ; rids    = toWitness {a? = allPairs? (λ r r′ → ¬? (proj₁ r ≟ℕ proj₁ r′)) _} tt , toWitness {a? = allPairs? (λ r r′ → ¬? (proj₁ r ≟ℕ proj₁ r′)) _} tt
  ; fresh-ids = toWitness {a? = all? (λ r → proj₁ r <? _) _} tt , toWitness {a? = all? (λ r → proj₁ r <? _) _} tt
  ; above   = toWitness {a? = all? (λ _ → _ ≟ true) _} tt , toWitness {a? = all? (λ _ → _ ≟ true) _} tt
  ; census  = λ { zero _ → inj₂ (refl , refl , λ ()) ; (suc zero) () }
  ; owned   = (λ _ ()) ∷ []
  ; ruleP   = proj₂ (Σ⁰.snd⁰ (subscribe! (plainExp (Point.prog defer-in)) (plainSlots (insᵖ defer-in))))
  ; ruleI   = proj₂ (Σ⁰.snd⁰ (subscribe! (elaborateImpl (κᵖ defer-in) (Point.prog defer-in)) (embedSlotsImpl (insᵖ defer-in))))
  ; scripts = insᵖ defer-in , refl , refl
  }
