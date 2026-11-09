{-# OPTIONS --guardedness #-}

-- THE RELATIONS THE SIMULTANEOUS SPEC IS STATED IN: the plain run, the
-- elaborated run and the batcher's on top, each read by a subscriber at
-- the root with every value stamped by its instant, and the one relation
-- between a batched run and a plain one that the spec asserts.
--
-- THE STAMP IS THE INSTANT'S RANK.  An instant is a frame or a cascade,
-- read off a position (`simultaneous.Readings`), but the plain program
-- and its elaboration are different trees, so a position in one names no
-- position in the other, and the batcher's rows need not share positions
-- with the elaboration's.  What the three runs share is the sequence of
-- instants: the elaboration adds no async step, so instant for instant
-- they pass through the same ones in the same order.  A row's stamp is
-- the number of instants before its own, counted over every row of its
-- run, shown or not: a reader meeting a row stamped 3 has, in any of the
-- three runs, passed three instants.  Nothing in a program can read a
-- stamp, and the elaboration carries names of its own that no relation
-- here reads.
module simultaneous.Relations where

open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; [_]; _++_; concat; length)
import Data.List as L
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Function using (_⇔_)
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong) renaming (trans to ≡-trans)

open import denotation.Position using (_≟ᵖ_; Pos; Instant; _<ⁱ_; root)
open import denotation.Events using (Timeline; fresh; finals)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Proper; Seen; _≺_; enter; ⟦_⟧)
open import denotation.Read using (Meets; After)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (SObs; module Elaborate)
import simultaneous.Spec as Grouping
open Grouping _≟_ using (batchSimultaneousᴰ)
open import simultaneous.Readings using (instantOf; stamped; closed)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) finals using (E; IE; elaborate; batchSimultaneous)

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
-- Stamps

-- The instants before `k`'s: those some row before `k` lies in, other
-- than `k`'s own.
-- Instants in order.
_≺ⁱ_ : Instant → Instant → Set
i ≺ⁱ j = T (i <ⁱ j)

Before : ∀ {A} → EmissionSet A → Pos → Instant → Set
Before t k i = i ≢ instantOf k × Σ Pos λ k′ → Σ _ λ e → t k′ e × k′ ≺ k × instantOf k′ ≡ i

-- `k`'s instant is the n-th the run passes through: the instants before
-- it, listed in order, are n.
Rank : ∀ {A} → EmissionSet A → Pos → ℕ → Set
Rank t k n = Σ (List Instant) λ is → AllPairs _≺ⁱ_ is × length is ≡ n × (∀ {i} → i ∈ is ⇔ Before t k i)

-- The run with every value row stamped by its instant's rank.
ranked : ∀ {A} → EmissionSet A → EmissionSet (ℕ × A)
ranked t k (out (n , a)) = t k (out a) × Rank t k n
ranked t k skip          = t k skip
ranked t k end           = t k end
ranked t k (pin p)       = t k (pin p)

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

outs-++ : ∀ {A : Set} (xs ys : List (Pos × Ev A)) → outs (xs ++ ys) ≡ outs xs ++ outs ys
outs-++ []                 ys = refl
outs-++ ((q , out a) ∷ xs) ys = cong ((q , a) ∷_) (outs-++ xs ys)
outs-++ ((q , skip) ∷ xs)  ys = outs-++ xs ys
outs-++ ((q , end) ∷ xs)   ys = outs-++ xs ys
outs-++ ((q , pin _) ∷ xs) ys = outs-++ xs ys

values-++ : ∀ {A : Set} (xs ys : List (Pos × Ev A)) → values (xs ++ ys) ≡ values xs ++ values ys
values-++ xs ys = ≡-trans (cong (L.map proj₂) (outs-++ xs ys)) (map-++ proj₂ (outs xs) (outs ys))

-- Each value the rows of a stamped run carry, at its position, with its
-- stamp: a plain row carries its one value, an InstEmit row what its emit
-- does, a mark nothing.
carried : ∀ {A B : Set} → (A → List B) → List (Pos × Ev (ℕ × A)) → List (Pos × ℕ × B)
carried f []                       = []
carried f ((q , out (n , a)) ∷ rs) = L.map (λ b → q , n , b) (f a) ++ carried f rs
carried f (_ ∷ rs)                 = carried f rs

-- The plain run's values, each with its stamp.
stampedᴰ : ∀ {A} → List (Pos × Ev (ℕ × A)) → List (ℕ × A)
stampedᴰ rs = L.map proj₂ (carried [_] rs)

-- The batcher's batches, each with its stamp; at element type `A`, the
-- elaborated run's values.
stampedᴮ : ∀ {A} → List (Pos × Ev (ℕ × IE A)) → List (ℕ × A)
stampedᴮ rs = L.map proj₂ (carried valuesOf rs)

-- The spec's grouping of stamped values, its last group kept only once
-- its instant is over: until then it may still grow.
grouped : ∀ {A} → Bool → List (ℕ × A) → List (ℕ × List A)
grouped ov ys = closed ov (batchSimultaneousᴰ ys)

-- The values the batches met carry, joined.
joined : ∀ {A} → List (Pos × Ev (IE (List A))) → List A
joined rs = concat (L.map proj₂ (stamped (values rs)))

-- The values an elaborated run carries, marks dropped.
vals : ∀ {A} → List (Pos × Ev (IE A)) → List A
vals rs = L.map proj₂ (stamped (values rs))

------------------------------------------------------------------------
-- An instant over

-- Past `c`, finitely many rows, each reached once those before it are.
Spent : ∀ {A} → EmissionSet A → Maybe Pos → Set
Spent t c = Σ (List Pos) λ ks → ∀ {k e} → t k e → After c k → k ∈ ks × Proper t k e

-- Past the row at `q`, the run leaves `q`'s instant: a reached row of
-- another instant or the completion, or finitely many rows after.
Exits : ∀ {A} → EmissionSet A → Pos → Set
Exits {A} t q = (Σ Pos λ k → Σ (Ev A) λ e → Seen t k e × q ≺ k × (instantOf k ≢ instantOf q ⊎ e ≡ end))
              ⊎ Spent t (just q)

-- Past `q`, no value of `q`'s instant.
Left : ∀ {A B : Set} → (A → List B) → EmissionSet A → Pos → Set
Left f t q = ∀ {k a} → t k (out a) → q ≺ k → instantOf k ≡ instantOf q → f a ≡ []

-- The instant of the value at `q` is over: nothing of it is left to
-- show, and the run leaves it.
Over : ∀ {A B : Set} → (A → List B) → EmissionSet A → Maybe Pos → Set
Over f t nothing  = ⊤
Over f t (just q) = Left f t q × Exits t q

-- The position of the last value met.
lastValue : ∀ {A B : Set} → (A → List B) → List (Pos × Ev (ℕ × A)) → Maybe Pos
lastValue f rs = L.last (L.map proj₁ (carried f rs))

-- A grouping may keep its last group only once its instant is over, run
-- over or not: batching shows what plain rxjs shows, as it shows it.
Closes : ∀ {A B : Set} → (A → List B) → EmissionSet A → List (Pos × Ev (ℕ × A)) → Bool → Set
Closes f t rs false = ⊤
Closes f t rs true  = Over f t (lastValue f rs)

-- The rows met include the completion.
Ends : ∀ {A} → List (Pos × Ev A) → Set
Ends rs = Any (λ r → proj₂ r ≡ end) rs

------------------------------------------------------------------------
-- The relation the spec asserts

-- `b` IS THE GROUPING OF `e`.  Whatever a subscriber to `b` has been
-- shown is within the grouping of what a subscriber to `e` has, the last
-- group counted only once its instant is over; whatever that grouping
-- allows, once its instant is over, `b` shows; and `b` completes exactly
-- when `e` does, its values all out.  A run need not end, so the first
-- two are directions over prefixes; an instant that never ends is never
-- released, so `ones` batched shows nothing, as specified.  At the end
-- the values alone are compared: the stamps of an ended run are pinned by
-- the two prefix directions over it.
--
-- RECOVERY: git show d9f6134:agda-impl/simultaneous/Flatten.agda restores
--   the grouping-flattening lemmas (joining the grouping gives back what
--   it grouped; a closed grouping joins to a prefix of it) that a
--   values-only prefix corollary of `spec` would consume.
Groups : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet A → Set
Groups b e =
  (∀ {rs} → Met (ranked b) rs → Σ _ λ rs′ → Σ Bool λ ov → Met (ranked e) rs′ × Closes [_] e rs′ ov × Prefix _≡_ (stampedᴮ rs) (grouped ov (stampedᴰ rs′))) ×
  (∀ {rs′ ov} → Met (ranked e) rs′ → Closes [_] e rs′ ov → Σ _ λ rs → Met (ranked b) rs × Prefix _≡_ (grouped ov (stampedᴰ rs′)) (stampedᴮ rs)) ×
  (∀ {rs} → Met b rs → Ends rs → Σ _ λ rs′ → Met e rs′ × Ends rs′ × joined rs ≡ values rs′) ×
  (∀ {rs′} → Met e rs′ → Ends rs′ → Σ _ λ rs → Met b rs × Ends rs × values rs′ ≡ joined rs)

------------------------------------------------------------------------
-- The pieces `spec` is assembled from

-- THE ERASURE: the elaborated run, marks dropped, is the plain run stamp
-- for stamp — a prefix of either, its last instant over or not, is a
-- prefix of the other with the same stamped values and the same instant
-- over — and complete exactly when it is.
Erases : ∀ {A} → EmissionSet (IE A) → EmissionSet A → Set
Erases x e =
  (∀ {rx ov} → Met (ranked x) rx → Closes valuesOf x rx ov → Σ _ λ rs′ → Met (ranked e) rs′ × Closes [_] e rs′ ov × stampedᴮ rx ≡ stampedᴰ rs′) ×
  (∀ {rs′ ov} → Met (ranked e) rs′ → Closes [_] e rs′ ov → Σ _ λ rx → Met (ranked x) rx × Closes valuesOf x rx ov × stampedᴰ rs′ ≡ stampedᴮ rx) ×
  (∀ {rx} → Met x rx → Ends rx → Σ _ λ rs′ → Met e rs′ × Ends rs′ × vals rx ≡ values rs′) ×
  (∀ {rs′} → Met e rs′ → Ends rs′ → Σ _ λ rx → Met x rx × Ends rx × values rs′ ≡ vals rx)

-- THE BATCHER: the batches, each with its stamp, are the spec's grouping
-- of the elaborated run's stamped values, the last group once its
-- instant is over.
Batches : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
Batches b x =
  (∀ {rs} → Met (ranked b) rs → Σ _ λ rx → Σ Bool λ ov → Met (ranked x) rx × Closes valuesOf x rx ov × Prefix _≡_ (stampedᴮ rs) (grouped ov (stampedᴮ rx))) ×
  (∀ {rx ov} → Met (ranked x) rx → Closes valuesOf x rx ov → Σ _ λ rs → Met (ranked b) rs × Prefix _≡_ (grouped ov (stampedᴮ rx)) (stampedᴮ rs))

-- The batcher completes exactly when what it batches does, all of it out.
EndsWith : ∀ {A} → EmissionSet (IE (List A)) → EmissionSet (IE A) → Set
EndsWith b x =
  (∀ {rs} → Met b rs → Ends rs → Σ _ λ rx → Met x rx × Ends rx × joined rs ≡ vals rx) ×
  (∀ {rx} → Met x rx → Ends rx → Σ _ λ rs → Met b rs × Ends rs × vals rx ≡ joined rs)
