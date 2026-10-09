-- THE WALK'S LEAVES THAT COMPUTE ON A CONCRETE FORMER: an `of`'s emits
-- against its plain values, at concrete lists under a binder; the
-- scan's and the test's elaborated steps against the author's under a
-- binder; the opening stores' numbering.
-- TARGET: of-carries @3bec3d
-- TARGET: lifts-scan @caa990
-- TARGET: lifts-while @305435
-- TARGET: init-numbers @517377
-- TARGET: init-distinct @da0497
module Probed.Walk-Leaves where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Fin using (zero)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import Rx.Exp using (add; ltᵖ; natᵗ; unitᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; ofᵉ; []ᵉ; _∷ᵉ_)
open import SExp.Syntax using (varˢᵗ; natˢ; primˢ; pairˢ; inrˢ; inputˢ)

open import Simulation.Walk using (of-carries; lifts-scan; lifts-while; init-numbers; init-distinct)
open import Simulation.Arm using (module Arms)
open import Simulation.After using (module Kept)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (slot~; []; _∷_)
open import CLI.Unit-Test.Prelude using (Γ₂)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals)

open Kept using (module After; after)

open Arms {Γ = Γ₂} (κᵖ two-arrivals) using (Carries)

-- LOAD-BEARING: two values, the first read off the binder, under a
-- mint; fails if the impl's list splits them other than one per emit,
-- puts a value on the closing emit's own, reorders them, or reads the
-- binder through the mint at the wrong index
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         (varˢᵗ (here refl) ∷ natˢ 7 ∷ []) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                         {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl }) refl 3)
_ = Carries.one _ (refl ∷ []) (Carries.one _ (refl ∷ []) Carries.[])

-- LOAD-BEARING: no values, so the one emit carries only the frame and
-- the end; fails if the impl's empty `of` emits a value or nothing
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         {u = natᵗ} [] {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                         {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl }) refl 3)
_ = Carries.quiet _ [] Carries.[]

-- LOAD-BEARING: a pair reading the author's variable and a right sum,
-- at a renaming moving the variable past a value 8 it does not own;
-- fails if a component is read at its unrenamed slot, the sum's side
-- flips, or the pair is split across emits
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         {u = natᵗ ×ᵗ (unitᵗ +ᵗ natᵗ)} (pairˢ (varˢᵗ (here refl)) (inrˢ (natˢ 7)) ∷ [])
                         {Θ′ = natᵗ ∷ natᵗ ∷ uniqᵗ ∷ []} there
                         {ρ′ = 8 ∷ᵉ 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl }) refl 3)
_ = Carries.one _ ((refl , refl) ∷ []) Carries.[]

-- LOAD-BEARING: two author binders, the pair reading the outer one
-- first, at a renaming moving both past a value 8; fails if the outer
-- variable is read at the inner's slot, at the mint's, or unrenamed
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         {u = natᵗ ×ᵗ natᵗ} (pairˢ (varˢᵗ (there (here refl))) (varˢᵗ (here refl)) ∷ [])
                         {Θ′ = natᵗ ∷ natᵗ ∷ natᵗ ∷ uniqᵗ ∷ []} there
                         {ρ′ = 8 ∷ᵉ 4 ∷ᵉ 6 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ 6 ∷ᵉ []ᵉ}
                         (λ { (here refl) → refl ; (there (here refl)) → refl }) refl 3)
_ = Carries.one _ ((refl , refl) ∷ []) Carries.[]

-- LOAD-BEARING: a running sum plus the author's variable, seeded by it,
-- over an emit of one payload; fails if the step or the seed reads the
-- author's variable at the slot the mint's binder took, the carried
-- value drifts from the plain accumulator, an output is dropped, or the
-- stamp moves
_ : Confirms (proj₁ (lifts-scan {Γ = Γ₂} (κᵖ two-arrivals)
                       (primˢ add (pairˢ (primˢ add (varˢᵗ (here refl))) (varˢᵗ (there (here refl)))))
                       (varˢᵗ (here refl)) (inputˢ zero) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                       {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl)
               4 ([] , 0 , 0 , inj₁ tt) 4 (inj₂ (inj₁ 3) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
               (3 ∷ []) refl (refl ∷ []))
_ = refl , (refl ∷ []) , refl

-- LOAD-BEARING: the seed, read off the author's variable
_ : Confirms (proj₂ (lifts-scan {Γ = Γ₂} (κᵖ two-arrivals)
                       (primˢ add (pairˢ (primˢ add (varˢᵗ (here refl))) (varˢᵗ (there (here refl)))))
                       (varˢᵗ (here refl)) (inputˢ zero) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                       {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl))
_ = refl

-- LOAD-BEARING: a test below the author's variable, over a payload it
-- fails, then one it passes; fails if the cutter decides the cut apart from
-- the plain test, keeps a value the plain prefix drops or drops one it
-- keeps, leaves its budget unrelated when it does not cut, or moves the
-- stamp
_ : Confirms (lifts-while {Γ = Γ₂} (κᵖ two-arrivals)
                (primˢ ltᵖ (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl))))) (inputˢ zero)
                {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x) {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl
                tt 1 [] ([] , 0 , 0 , inj₁ tt) (inj₂ (inj₁ 5) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                (5 ∷ []) refl (refl ∷ []))
_ = (λ ()) , refl , (refl ∷ []) , refl

_ : Confirms (lifts-while {Γ = Γ₂} (κᵖ two-arrivals)
                (primˢ ltᵖ (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl))))) (inputˢ zero)
                {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x) {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl
                tt 1 [] ([] , 0 , 0 , inj₁ tt) (inj₂ (inj₁ 3) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                (3 ∷ []) refl (refl ∷ []))
_ = (λ _ → refl) , refl , (refl ∷ []) , refl

-- LOAD-BEARING: one hot script live at the opening, numbered by its
-- slot and alone on each side; fails if the impl numbers it apart from
-- its slot or lists it twice
_ : Confirms (init-numbers (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = slot~ zero refl ∷ []

_ : Confirms (init-distinct (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = ([] ∷ []) , ([] ∷ [])
