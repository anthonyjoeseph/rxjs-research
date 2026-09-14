-- THE TEMPLATE DROP, ASKED WITHOUT THE DATA HYPOTHESIS.
--
-- The proven statement says an observable a template emits is written
-- strictly shallower than the template — and it says it of a template
-- whose ARGUMENT type is data.  That hypothesis is not there to make a
-- proof go through, and this is the witness: where the argument is
-- itself observable, reifying it writes a `strmᵗ` the template never
-- wrote, so the substitution ADDS a level and the emitted reading is
-- the handed value's plus the template's rather than the template's
-- alone.
--
-- AND THE MARGIN IS UNBOUNDED, WHICH IS WHAT MAKES IT A CHANGE OF
-- STATEMENT RATHER THAN AN OFF-BY-ONE.  The template below passes its
-- argument through under one `strmᵗ`, so it reads one however deep the
-- argument is; hand it an observable of depth k and the emission reads
-- k + 1.  The row takes k at 2, which is the smallest that separates,
-- and nothing about the shape stops it being taken at any k.
module Refuted.Template-Passes where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (_<_; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Fn; natᵗ; obs; nat̂; varᵗ; strmᵗ; ofᵉ;
  applyFn)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵗ)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

-- THE STATEMENT, WITH THE DATA HYPOTHESIS TAKEN OUT AND NOTHING ELSE
-- CHANGED.  Everything else is the proven one's, so a repair that
-- weakens the conclusion weakens this witness in the same edit.
TemplateStrict : Set
TemplateStrict =
  ∀ {n} {Γ : Ctx n} {s u} (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
  obsDepthᵉ (applyFn fn v) < obsDepthᵗ fn

-- LOAD-BEARING: the handed observable, and the template that only
-- passes it through.
deep : Val Γ₀ (obs (obs (obs natᵗ)))
deep = ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])) ∷ [])

row-deep-handed : obsDepthᵉ deep ≡ 2
row-deep-handed = refl

passes : Fn Γ₀ [] [] [] (obs (obs (obs natᵗ))) (obs (obs (obs (obs natᵗ))))
passes = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

row-passes-template : obsDepthᵗ passes ≡ 1
row-passes-template = refl

row-passes-emitted : obsDepthᵉ (applyFn passes deep) ≡ 3
row-passes-emitted = refl

-- 3 is not below 1.
template-strict-false : TemplateStrict → ⊥
template-strict-false h with h passes deep
... | s≤s ()
