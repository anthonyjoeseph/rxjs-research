-- `adequacy.Engine.Trails.join-fed` over the fragment alone is false: a
-- joiner at the empty position, under a connect whose source is done, is
-- in the fragment, and joined under no head.
module adequacy.Engine.Trails.JoinFedRefuted where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import operation.PureObservable using (module Machine)
open Machine using (Ctx; CS; cs; top; inBody; doneS; joinS; plug)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Trails using (join-fed)

k : CS
k = cs false true false nothing nothing nothing [] []

e : Ctx ℕ (ℕ ∷ []) ℕ
e = inBody k doneS top

y : ℕ ∈ (ℕ ∷ [])
y = here refl

fs : Frag (plug e (joinS [] true y []))
fs = tt , tt , (λ ()) , (λ ())

refuted : ⊥
refuted = proj₁ (proj₁ (join-fed e [] y [] fs))
