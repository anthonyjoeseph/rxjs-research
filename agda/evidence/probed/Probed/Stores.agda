-- THE STORES THE ROOT SUBSCRIBES INSTALL, related
-- by hand at concrete programs: the relation `Simulation.Stores` states,
-- inhabited against the registries the two runs actually compute.
-- TARGET: walk-input @1ab710
-- TARGET: walk-defer @cd22e2
module Probed.Stores where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Rx.Prim using (cold; after_,_)
open import SExp.Syntax using (inputˢ; emptyˢ)
open import Data.Sum using (inj₁)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero; suc)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import SExp.Plain using (plainExp)
open import SExp.Simul-Slots using (plainSlots)
open import Rx.Evaluator.Builder using (subscribe!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰)
open import Simulation.Walk using (walk-input; walk-defer; init-store; minted)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (data~; defer~; hop; elab; here; read~; cold~; root~; mach; hot~; block; []; _∷_)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals; defer-in)

-- each subscribe row is the walk's arm for the program's one former, at
-- the empty stores and the two root derivations, as `root-walk` calls it
_ : Confirms (proj₁ (walk-input (κᵖ two-arrivals) zero (λ x → x) (λ ())
                            (init-store (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals) _) root~
                            (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp (Point.prog two-arrivals)) (plainSlots (insᵖ two-arrivals)))))
                            (proj₂ (minted (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals)))))
_ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = data~ refl (refl ∷ refl ∷ []) ∷ []
  ; sync    = (refl , []) ∷ []
  ; rows    = read~ (inj₁ refl) root~ refl ∷ mach (hot~ refl (block refl refl refl) refl) []
  ; latches = λ { zero → (λ _ → refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ _ _ ()
  ; wfᴵ     = λ { 0 _ refl → refl ; 1 _ () ; 2 _ refl → refl ; (suc (suc (suc _))) _ () }
  }

-- a cold script: its subscribe runs the input block straight to the root
cold-in : Point
cold-in = record { d₀ = cold (3 ∷ []) ((after 1 , 4) ∷ []) ; prog = inputˢ zero ; d₁ = emptyˢ }

_ : Confirms (proj₁ (walk-input (κᵖ cold-in) zero (λ x → x) (λ ())
                       (init-store (κᵖ cold-in) (Point.prog cold-in) (insᵖ cold-in) _) root~
                       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp (Point.prog cold-in)) (plainSlots (insᵖ cold-in)))))
                       (proj₂ (minted (κᵖ cold-in) (Point.prog cold-in) (insᵖ cold-in)))))
_ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = data~ refl (refl ∷ []) ∷ []
  ; sync    = (refl , []) ∷ []
  ; rows    = cold~ here (block {m1 = 2} {b = 1} {m2 = 0} refl refl refl) root~ refl ∷ []
  ; latches = λ { zero → (λ ()) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ _ _ ()
  ; wfᴵ     = λ { 0 _ refl → refl ; 1 _ () ; 2 _ refl → refl ; (suc (suc (suc _))) _ () }
  }

-- a deferred hot read: the hop pending, its body not yet subscribed

_ : Confirms (proj₁ (walk-defer (κᵖ defer-in) (inputˢ zero) (λ x → x) (λ ())
                       (init-store (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in) _) root~
                       (proj₁ (Σ⁰.snd⁰ (subscribe! (plainExp (Point.prog defer-in)) (plainSlots (insᵖ defer-in)))))
                       (proj₂ (minted (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in)))))
_ = record
  { π       = (0 , 0 ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = [] ∷ []
  ; sources = defer~ (hop (elab (inputˢ zero) (λ x → x) (λ ())) ∷ []) ∷ data~ refl (refl ∷ []) ∷ []
  ; sync    = (refl , refl ∷ []) ∷ (refl , []) ∷ []
  ; rows    = defer~ here (here refl) refl refl root~ refl ∷ []
  ; latches = λ { zero → (λ _ → refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ { 0 _ refl → refl ; (suc _) _ () }
  ; wfᴵ     = λ { 0 _ refl → refl ; (suc _) _ () }
  }
