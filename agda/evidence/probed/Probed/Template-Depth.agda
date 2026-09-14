-- WHAT A TEMPLATE EMITS, INSTANTIATED — AND THE ROW THAT SAYS THE DATA
-- HYPOTHESIS IS LOAD-BEARING RATHER THAN DECORATIVE.
--
-- A SKETCH.  This file is not stamped and not typechecked: its
-- `-- TARGET:` carries no statement fingerprint, because the statement
-- it names lives in a module that does not yet typecheck either.  It is
-- here because the claim is CHEAP TO TEST and the campaign's rule is to
-- probe before proving — the rows below are what would refute the
-- substitution route in an afternoon if it were wrong.
--
-- WHAT IS AT RISK.  `applyFn-strict` says an observable a template
-- emits is written strictly shallower than the template.  That is a
-- statement about SUBSTITUTION, and the two ways it could be false are
-- the two ways the predecessor family was actually refuted: a template
-- that DROPS its argument (then the emitted observable owes nothing to
-- the input, and the claim should hold trivially — a degenerate row),
-- and a template that WRAPS it (then the input lands under a `strmᵗ`
-- the template wrote, and whether the reading still drops is the whole
-- question — the load-bearing row).
--
-- AND THE THIRD ROW IS A REFUTATION OF THE UNCONDITIONED FORM.  Where
-- the argument type is itself observable, `reify` writes a `strmᵗ` and
-- the substitution DOES add a level, without bound: the emitted
-- observable is as deep as whatever was handed in, plus the template's
-- own.  So the claim is false without `isData s ≡ true`, it is false by
-- an arbitrary margin rather than by one, and the hypothesis is not
-- there to make a proof go through.  That row is what turns the
-- conditioned statement from a weakening into the true statement
-- replacing a false one.
--
-- COVERAGE: templates whose body is `ofᵉ` of a term, at one and two
-- levels of `strmᵗ`.  NOT covered: a template writing a `μᵉ`, a
-- template writing a `deferᵉ` (the reading cuts both to zero, so they
-- are the shapes most likely to hide something), and every fold — the
-- accumulator is fed back, which is the open form and not this one.
--
-- TARGET: applyFn-strict @sketch
module Probed.Template-Depth where

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; Val; Fn; natᵗ; obs; nat̂; varᵗ; strmᵗ; ofᵉ;
  applyFn)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵗ)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

------------------------------------------------------------------
-- ROW 1 — DEGENERATE.  A template that drops its argument.
------------------------------------------------------------------

-- `nat → obs nat`, emitting a constant one-shot.  It could only fail if
-- `obsDepthᵗ` of a `strmᵗ` were not a successor, which is the
-- definition; the row is here because the predecessor's FREE
-- equal-bounds form died to exactly this shape, and it is worth having
-- on record that the new form does not.
drops : Fn Γ₀ [] [] [] natᵗ (obs natᵗ)
drops = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

row-drops-emitted : obsDepthᵉ (applyFn drops 3) ≡ 0
row-drops-emitted = refl

row-drops-template : obsDepthᵗ drops ≡ 1
row-drops-template = refl

------------------------------------------------------------------
-- ROW 2 — LOAD-BEARING.  A template that WRAPS its argument.
------------------------------------------------------------------

-- `nat → obs (obs nat)`: the argument is placed under TWO `strmᵗ`s the
-- template wrote.  This is the shape that refuted the symmetric pinned
-- form, and it is the one that would refute this statement too if
-- substitution moved the reading.  It fails if the emitted expression
-- reads 2 rather than 1 — i.e. if closing the environment left a level
-- behind.
wraps : Fn Γ₀ [] [] [] natᵗ (obs (obs natᵗ))
wraps = strmᵗ (ofᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])) ∷ []))

row-wraps-emitted : obsDepthᵉ (applyFn wraps 3) ≡ 1
row-wraps-emitted = refl

row-wraps-template : obsDepthᵗ wraps ≡ 2
row-wraps-template = refl

------------------------------------------------------------------
-- ROW 3 — LOAD-BEARING, AND IT IS A REFUTATION.
------------------------------------------------------------------

-- The same template shape with an OBSERVABLE argument type.  `reify`
-- writes `strmᵗ` for an observable value, so the substitution inserts a
-- level the template never wrote, and the emitted reading is the
-- HANDED value's plus the template's rather than the template's alone.
-- Take the handed observable as deep as you like and the gap is that
-- deep: the unconditioned claim is not off by one, it is unbounded.
deep : Val Γ₀ (obs natᵗ)
deep = ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])) ∷ [])

row-deep-handed : obsDepthᵉ deep ≡ 2
row-deep-handed = refl

passes : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
passes = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

row-passes-template : obsDepthᵗ passes ≡ 1
row-passes-template = refl

-- 3 is NOT below 1.  The conditioned statement is the true one.
row-passes-emitted : obsDepthᵉ (applyFn passes deep) ≡ 3
row-passes-emitted = refl
