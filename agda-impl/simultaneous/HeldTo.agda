{-# OPTIONS --guardedness #-}

-- HELD UP TO THE FIRST FAILURE.  A take reads its source's idleness only
-- up to the first row it fails at, so what it needs of its source is
-- `Held` with `idle` claimed only there.  Failing nothing, it is `Held`.
module simultaneous.HeldTo where

open import Data.Bool using (Bool; T; not; true)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; out; end; Few; _≺_; _≼_)
open import denotation.Read using (Visible; After; cursor)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; Early; Ex; Carried; Routing; Rest; cnt; nameOf; Valued; opos)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- No row failing `keep` has its first effect before `w`.
Unfailed : ∀ {X : Set} → (IE X → Bool) → EmissionSet (IE X) → Pos → Set
Unfailed keep t w = ∀ {f a} → t f (out a) → T (not (keep a)) → (f ⊕ [ ix 0 ]) ≺ w → ⊥

-- IDLE UP TO THE FIRST FAILURE: idle at every position no failing row's
-- first effect precedes.  All a take reads of its source's idleness.
IdleTo : ∀ {X : Set} → (IE X → Bool) → EmissionSet (IE X) → Set
IdleTo keep t = ∀ {rs} → Met t rs → (∀ {c} → (c , end) ∈ rs → ⊥) → ∀ {w} → Unfailed keep t w → Few t w → After (cursor nothing rs) w
              → (∀ {y e} → t y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

-- HELD UP TO THE FIRST FAILURE: held, idle only up to the first row
-- failing `keep`.  What a take needs of its source.
record HeldTo {X : Set} (keep : IE X → Bool) (t : EmissionSet (IE X)) (cs : List Pos) : Set where
  field
    named   : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    covered : ∀ {rs} → Met t rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ {rs} → Met t rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
    shut    : Shut t
    early   : ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
    ends    : ∀ {y} → t y end → Early y
    done    : ∀ {y n} → t y (out (instEmit (mark completed) n)) → Early y
    late    : ∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
    idle    : IdleTo keep t
    rest    : Rest t

held-to : ∀ {X : Set} {keep : IE X → Bool} {t cs} → Held t cs → HeldTo keep t cs
held-to h = record
  { named = H.named ; covered = H.covered ; exact = H.exact ; routing = H.routing ; shut = H.shut
  ; early = H.early ; ends = H.ends ; done = H.done ; late = H.late ; idle = λ m ne _ → H.idle m ne ; rest = H.rest }
  where module H = Held h

-- Failing nothing, held up to it is held.
held-from : ∀ {X : Set} {t : EmissionSet (IE X)} {cs} → HeldTo (λ _ → true) t cs → Held t cs
held-from h = record
  { named = H.named ; covered = H.covered ; exact = H.exact ; routing = H.routing ; shut = H.shut
  ; early = H.early ; ends = H.ends ; done = H.done ; late = H.late ; idle = λ m ne → H.idle m ne (λ _ ()) ; rest = H.rest }
  where module H = HeldTo h
