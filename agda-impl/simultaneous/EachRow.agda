{-# OPTIONS --guardedness #-}

-- THE REAL FLATMAP'S OUTER, READ AS `each valuesOf` OF THE HOT OUTER:
-- `simultaneous.ValsRow`'s rows of a merged `of`, at the elaborated tree.
module simultaneous.EachRow where

open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (mergeᶠ; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; hot; enter; DenEnv; module Op; out; end; Few; _≺_; at-out; on-out)
open import denotation.Laws.Worlds using (Lawful; ⊕-assoc)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.DenRows using (merge-out; hot-out)
open import simultaneous.InstEmit using (instEmit; value; mark; valuesOf)
open import simultaneous.HeldComb using (ev)
import simultaneous.ValsRow as VR

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; each)

-- A VALUE OF THE OUTER'S VALUES, READ THROUGH A HOT, lies a value step
-- below the hot's reading of a value row of it.
vals-row : ∀ {A} (t : EmissionSet (IE A)) p {q a} → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (valuesOf x)) (hot t)) p q (out a)
         → Σ Pos λ r → Σ _ λ n → t r (out (instEmit (value a) n)) × q ≡ r ⊕ (sub p ∷ ix 1 ∷ ix 0 ∷ [])
vals-row t p x with merge-out (λ x → Op.of (valuesOf x)) (hot t) p x
... | k , instEmit (value _) n , hk , (at-out , _) , _ with hot-out hk
...   | r , tr , _ , refl = r , n , tr , trans (⊕-assoc (r ⊕ [ sub p ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc r [ sub p ] (ix 1 ∷ ix 0 ∷ []))
vals-row t p x | k , instEmit (value _) n , hk , (on-out () , _) , _
vals-row t p x | k , instEmit (mark _) _ , hk , (() , _) , _

each-row : ∀ m {Θ A B} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) p {q a}
         → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p q (out a)
         → Σ Pos λ r → Σ _ λ n → t₁ r (out (instEmit (value a) n)) × q ≡ r ⊕ (sub p ∷ ix 1 ∷ ix 0 ∷ [])
each-row nothing  t₂ t₁ env₀ p = vals-row t₁ p
each-row (just _) t₂ t₁ env₀ p = vals-row t₁ p

-- A VALUE ROW OF THE OUTER PAST THE READER, WITH FEW ROWS BEFORE IT, IS
-- READ: its value a value step below the hot's reading of it.
each-at : ∀ m {Θ A B} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) → Lawful t₁ → ∀ p {c e₀ a n}
        → t₁ c e₀ → p ≺ c → Few t₁ c → e₀ ≡ out (instEmit (value a) n)
        → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p (((c ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out a)
each-at nothing  t₂ t₁ env₀ L p tc pc fc = VR.vals-at t₁ L p tc pc fc
each-at (just _) t₂ t₁ env₀ L p tc pc fc = VR.vals-at t₁ L p tc pc fc

-- AN END OF THE OUTER PAST THE READER, WITH FEW ROWS BEFORE IT, ENDS THE
-- READING one `sub` below it.
each-end : ∀ m {Θ A B} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) → Lawful t₁ → ∀ p {c}
         → t₁ c end → p ≺ c → Few t₁ c
         → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p (c ⊕ [ sub p ]) end
each-end nothing  t₂ t₁ env₀ L p tc pc fc = VR.vals-end t₁ L p tc pc fc refl
each-end (just _) t₂ t₁ env₀ L p tc pc fc = VR.vals-end t₁ L p tc pc fc refl

-- WHERE THE OUTER'S VALUES PRECEDE ITS ENDS, THE READING'S DO.
each-before : ∀ m {Θ A B} (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ) → Lawful t₁
            → (∀ {r x k} → t₁ r (out x) → t₁ k end → r ≺ k) → ∀ p {q a c}
            → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p q (out a)
            → enter (ev m (each valuesOf (connected (there (here refl)))) (hot t₂ ∷ hot t₁ ∷ env₀)) p c end → q ≺ c
each-before nothing  t₂ t₁ env₀ L pe p = VR.vals-before t₁ L p pe
each-before (just _) t₂ t₁ env₀ L pe p = VR.vals-before t₁ L p pe
