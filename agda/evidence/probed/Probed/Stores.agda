-- THE STORES THE ROOT SUBSCRIBES INSTALL, AND ONE CASCADE KEEPS, related
-- by hand at concrete programs: the relation `Simulation.Stores` states,
-- inhabited against the registries the two runs actually compute.
-- TARGET: subscribe-related @70be7d
-- TARGET: cascade-related @a3c004
module Probed.Stores where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Rx.Prim using (hot; cold; after_,_)
open import SExp.Syntax using (inputˢ; emptyˢ; deferˢ)
open import Data.Sum using (inj₁)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero; suc)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Simulation.Statement using (subscribe-related; cascade-related)
open import Simulation.Schedules using (sched-pop; []; _∷_)
open import Simulation.Stores using (data~; defer~; hop; elab; here; read~; cold~; root~; mach; hot~; block; []; _∷_)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals)

store₀ : Confirms (proj₁ (proj₂ (subscribe-related (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))))
store₀ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = data~ refl (refl ∷ refl ∷ []) ∷ []
  ; rows    = read~ (inj₁ refl) root~ refl ∷ mach (hot~ refl (block refl refl refl) refl) []
  ; latches = λ { zero → (λ _ → refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ _ _ ()
  ; wfᴵ     = λ { 0 _ refl → refl ; 1 _ () ; 2 _ refl → refl ; (suc (suc (suc _))) _ () }
  }

-- the first cascade of the same run: one arrival popped from each side
_ : Confirms (proj₁ (proj₂ (cascade-related (κᵖ two-arrivals) (Point.prog two-arrivals) store₀
                                            (sched-pop ((refl , []) ∷ []) (data~ refl (refl ∷ refl ∷ []) ∷ [])))))
_ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = data~ refl (refl ∷ []) ∷ []
  ; rows    = read~ (inj₁ refl) root~ refl ∷ mach (hot~ refl (block refl refl refl) refl) []
  ; latches = λ { zero → (λ _ → refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ _ _ ()
  ; wfᴵ     = λ { 0 _ refl → refl ; 1 _ () ; 2 _ refl → refl ; (suc (suc (suc _))) _ () }
  }

-- a cold script: its subscribe runs the input block straight to the root
cold-in : Point
cold-in = record { d₀ = cold (3 ∷ []) ((after 1 , 4) ∷ []) ; prog = inputˢ zero ; d₁ = emptyˢ }

_ : Confirms (proj₁ (proj₂ (subscribe-related (κᵖ cold-in) (Point.prog cold-in) (insᵖ cold-in))))
_ = record
  { π       = []
  ; π-keys  = []
  ; π-vals  = []
  ; sources = data~ refl (refl ∷ []) ∷ []
  ; rows    = cold~ here (block {m1 = 2} {b = 1} {m2 = 0} refl refl refl) root~ refl ∷ []
  ; latches = λ { zero → (λ ()) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ _ _ ()
  ; wfᴵ     = λ { 0 _ refl → refl ; 1 _ () ; 2 _ refl → refl ; (suc (suc (suc _))) _ () }
  }

-- a deferred hot read: the hop pending, its body not yet subscribed
defer-in : Point
defer-in = record { d₀ = hot ((after 1 , 5) ∷ []) ; prog = deferˢ (inputˢ zero) ; d₁ = emptyˢ }

_ : Confirms (proj₁ (proj₂ (subscribe-related (κᵖ defer-in) (Point.prog defer-in) (insᵖ defer-in))))
_ = record
  { π       = (0 , 0 ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = [] ∷ []
  ; sources = defer~ (hop (elab (inputˢ zero) (λ x → x) (λ ())) ∷ []) ∷ data~ refl (refl ∷ []) ∷ []
  ; rows    = defer~ here (here refl) refl refl root~ refl ∷ []
  ; latches = λ { zero → (λ _ → refl) , (λ ()) ; (suc zero) → (λ ()) , (λ _ → refl , refl) }
  ; wfᴾ     = λ { 0 _ refl → refl ; (suc _) _ () }
  ; wfᴵ     = λ { 0 _ refl → refl ; (suc _) _ () }
  }
