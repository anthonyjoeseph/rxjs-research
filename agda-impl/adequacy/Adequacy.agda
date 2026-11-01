{-# OPTIONS --guardedness #-}

-- THE THEOREM: the pure semantics, run on a program, shows exactly what
-- a subscriber to the program's emission set is shown — the values and
-- end among the rows a reader meets (`denotation.Read.Meets`, the reader
-- the simultaneous spec reads by): each run shows what the reader meets
-- first, and whatever the reader meets, some run shows.
module adequacy.Adequacy where

open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Events using (Pos; root)
open import denotation.EmissionSet using (Ev; enter; ⟦_⟧)
open import operation.PureObservable using (PureObs; module Machine)
open Machine using (load)
open import denotation.Read using (Meets)
open import adequacy.Rows using (Steps; conv)
open import adequacy.Simulation using (sound)
open import adequacy.Told using (cursor)
open import adequacy.Complete using (complete)

-- The rows a reader of `o`'s emission set, subscribed at the root, meets
-- first.
Met : ∀ {R} → PureObs [] R → List (Pos × Ev R) → Set
Met o rs = Meets (enter (⟦ o ⟧ []ᴬ) root) rs

Sound : ∀ {R} → PureObs [] R → Set₁
Sound o = ∀ {rs} → Steps (load o) rs → Met o (conv rs)

Complete : ∀ {R} → PureObs [] R → Set₁
Complete o = ∀ {rs} → Met o rs → Σ _ λ rs′ → Steps (load o) rs′ × conv rs′ ≡ rs


adequacy : ∀ {R} (o : PureObs [] R) → Sound o × Complete o
adequacy o = (λ st → sound (cursor o) st) , complete o (cursor o)
