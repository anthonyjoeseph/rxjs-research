{-# OPTIONS --guardedness #-}

-- THE RELATIONS THE SIMULTANEOUS SPEC IS STATED IN: the three emission
-- sets a program is read through, the readings of what a subscriber to
-- each meets, and the relations between them.
module simultaneous.Relations where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; concat)
import Data.List as L
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (sym to ≡-sym; trans to ≡-trans)

open import denotation.Events using (_≟ᵖ_; Pos; Timeline; root; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Proper; Seen; _≺_; enter; ⟦_⟧)
open import denotation.Read using (Meets; After; cursor)
open import simultaneous.InstEmit using (InstEmit; valuesOf)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Spec as Spec
open Spec _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; stamped; closed)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (E; IE; elaborate; batchSimultaneous)

-- The program the author's stands for: elaborated, batched on top.
batchedObs : ∀ {A} → SObs [] A → E [] (IE (List A))
batchedObs o = batchSimultaneous (elaborate o)

-- A program's emission set, its elaborated program's, and the batcher's on top,
-- each subscribed at the root.
events : ∀ {A} → SObs [] A → EmissionSet A
events o = enter (⟦ o ⟧ []) root

elaborated : ∀ {A} → SObs [] A → EmissionSet (IE A)
elaborated o = enter (⟦ elaborate o ⟧ []) root

batched : ∀ {A} → SObs [] A → EmissionSet (IE (List A))
batched o = enter (⟦ batchedObs o ⟧ []) root

------------------------------------------------------------------------
-- Readings of the rows met

-- What a subscriber at the root is shown first.
Met : ∀ {A} → EmissionSet A → List (Pos × Ev A) → Set
Met = Meets

-- The values among them, each at its position.
outs : ∀ {A} → List (Pos × Ev A) → List (Pos × A)
outs []                 = []
outs ((q , out a) ∷ rs) = (q , a) ∷ outs rs
outs (_ ∷ rs)           = outs rs

values : ∀ {A} → List (Pos × Ev A) → List A
values rs = L.map proj₂ (outs rs)

batchesOut : ∀ {A} → List (Pos × Ev (IE (List A))) → List (Pos × List A)
batchesOut rs = stamped (values rs)

joined : ∀ {A} → List (Pos × Ev (IE (List A))) → List A
joined rs = concat (L.map proj₂ (batchesOut rs))

-- The values an elaborated run carries, marks dropped.
vals : ∀ {A} → List (Pos × Ev (IE A)) → List A
vals rs = L.map proj₂ (stamped (values rs))

-- The spec's grouping of the values met, its last group kept only once
-- its instant is over.
grouped : ∀ {A} → Bool → List (Pos × Ev (IE A)) → List (Pos × List A)
grouped ov rs = closed ov (batchSimultaneousᴰ (stamped (values rs)))

-- Past `c`, finitely many rows, each reached once those before it are.
Spent : ∀ {A} → EmissionSet A → Maybe Pos → Set
Spent t c = Σ (List Pos) λ ks → ∀ {k e} → t k e → After c k → k ∈ ks × Proper t k e

-- The instant the last value met belongs to.
lastInstant : ∀ {A} → List (Pos × Ev (IE A)) → Maybe Pos
lastInstant rs = L.last (L.map proj₁ (stamped (values rs)))

-- Past what was met, no value of instant `i`.
Left : ∀ {A} → EmissionSet (IE A) → List (Pos × Ev (IE A)) → Maybe Pos → Set
Left t rs nothing  = ⊤
Left t rs (just i) = ∀ {k x} → t k (out x) → After (cursor nothing rs) k → InstEmit.instant x ≡ i → valuesOf x ≡ []

-- A grouping may keep its last group only once its instant is over, run
-- over or not: batching shows what plain rxjs shows, as it shows it.
Closes : ∀ {A} → EmissionSet (IE A) → List (Pos × Ev (IE A)) → Bool → Set
Closes t rs false = ⊤
Closes t rs true  = Left t rs (lastInstant rs)

-- Past the row at `q`, the run leaves `q`'s instant: a reached row of
-- another instant or the completion, or finitely many rows after.
Exits : ∀ {A} → EmissionSet A → Pos → Set
Exits {A} t q = (Σ Pos λ k → Σ (Ev A) λ e → Seen t k e × q ≺ k × (instantOf k ≢ instantOf q ⊎ e ≡ end))
              ⊎ Spent t (just q)

-- Every instant a row is reached in is over.
FiniteInstants : ∀ {A} → EmissionSet A → Set
FiniteInstants t = ∀ {q e} → Seen t q e → Exits t q

------------------------------------------------------------------------
-- The three relations, between emission sets

-- The rows met include the completion.
Ends : ∀ {A} → List (Pos × Ev A) → Set
Ends rs = Any (λ r → proj₂ r ≡ end) rs

Joins : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet A → Set
Joins b e =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Met e rs′ × Prefix _≡_ (joined rs) (values rs′)) ×
  (FiniteInstants e → ∀ {rs′} → Met e rs′ → Σ _ λ rs → Met b rs × Prefix _≡_ (values rs′) (joined rs)) ×
  (∀ {rs} → Met b rs → Ends rs → Σ _ λ rs′ → Met e rs′ × Ends rs′ × joined rs ≡ values rs′) ×
  (∀ {rs′} → Met e rs′ → Ends rs′ → Σ _ λ rs → Met b rs × Ends rs × values rs′ ≡ joined rs)

Batches : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
Batches b x =
  (∀ {rs} → Met b rs → Σ _ λ rs′ → Σ Bool λ ov → Met x rs′ × Closes x rs′ ov × Prefix _≡_ (batchesOut rs) (grouped ov rs′)) ×
  (∀ {rs′ ov} → Met x rs′ → Closes x rs′ ov → Σ _ λ rs → Met b rs × Prefix _≡_ (grouped ov rs′) (batchesOut rs))

-- coherent: provenances agree exactly when instants do.
SameInstant : Pos × Pos → Pos × Pos → Set
SameInstant (p , i) (q , j) = (i ≡ j) ⇔ (instantOf p ≡ instantOf q)

-- An emit at its position, read as its position and its name.
named : ∀ {A} → Pos × IE A → Pos × Pos
named (p , x) = p , InstEmit.instant x

InstantsAgree : ∀ {A} → EmissionSet (IE A) → Set
InstantsAgree x = ∀ {rs} → Met x rs → AllPairs SameInstant (L.map named (outs rs))

------------------------------------------------------------------------
-- The pieces `left-to-right` is assembled from

-- THE ERASURE: the elaborated run, marks dropped, is the plain run:
-- the same values in order, and complete exactly when it is.
Erases : ∀ {A} → EmissionSet (IE A) → EmissionSet A → Set
Erases x e =
  (∀ {rx} → Met x rx → Σ _ λ rs′ → Met e rs′ × Prefix _≡_ (vals rx) (values rs′)) ×
  (∀ {rs′} → Met e rs′ → Σ _ λ rx → Met x rx × Prefix _≡_ (values rs′) (vals rx)) ×
  (∀ {rx} → Met x rx → Ends rx → Σ _ λ rs′ → Met e rs′ × Ends rs′ × vals rx ≡ values rs′) ×
  (∀ {rs′} → Met e rs′ → Ends rs′ → Σ _ λ rx → Met x rx × Ends rx × values rs′ ≡ vals rx)

-- The batcher completes exactly when what it batches does, all of it out.
EndsWith : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
EndsWith b x =
  (∀ {rs} → Met b rs → Ends rs → Σ _ λ rx → Met x rx × Ends rx × joined rs ≡ vals rx) ×
  (∀ {rx} → Met x rx → Ends rx → Σ _ λ rs → Met b rs × Ends rs × vals rx ≡ joined rs)

-- When the plain run's instants are finite, whatever of the elaborated run
-- was met runs on until the instant of its last value is over.
Settles : ∀ {A} → EmissionSet (IE A) → EmissionSet A → Set
Settles x e = FiniteInstants e → ∀ {rx} → Met x rx →
  Σ _ λ rx′ → Met x rx′ × Closes x rx′ true × Prefix _≡_ (vals rx) (vals rx′)
