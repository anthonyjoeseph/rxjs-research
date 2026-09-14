-- WHAT A TEMPLATE MUST WRITE, INSTANTIATED — AND WHY THE DATA
-- HYPOTHESIS UNDER IT IS THE STATEMENT RATHER THAN A CONVENIENCE.
--
-- WHAT IS AT RISK.  `dep-fn-pos` says a template returning an
-- observable reads at least one: it has to WRITE the observable it
-- returns, because the one other way to have one is to read it from a
-- binder and the only binder is data.  It is the positivity the strict
-- drop is spent through, and it is pure syntax — no environment, no
-- value, nothing the run supplies — so the way it could be false is a
-- template that gets an observable from somewhere the induction has not
-- looked.
--
-- COVERAGE: templates whose body is `ofᵉ` of a term, at one and two
-- levels of `strmᵗ`, with the argument dropped and with the argument
-- wrapped.  NOT covered: a template writing a `μᵉ`, a template writing
-- a `deferᵉ` (the reading cuts both to zero, so they are the shapes
-- most likely to hide something), and every head that BINDS — the
-- `caseᵗ` whose branches carry the positivity is the arm the induction
-- has to split on and no row here reaches it.
--
-- TARGET: dep-fn-pos @c824be
--
-- REFUTED: `Refuted.Template-Passes` — the drop this positivity is
--   spent through, asked without the data hypothesis.
module Probed.Template-Depth where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Fn; natᵗ; obs; nat̂; varᵗ; strmᵗ; ofᵉ)
open import Rx.Obs-Depth using (zeroη; obsDepthᵗ)
open import Rx.Obs-Depth.Substitution using (dep-fn-pos)
open import Probed.Apparatus using (Confirms)

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

row-drops-template : obsDepthᵗ drops ≡ 1
row-drops-template = refl

row-drops-pos : Confirms (dep-fn-pos zeroη refl drops)
row-drops-pos = s≤s z≤n

------------------------------------------------------------------
-- ROW 2 — LOAD-BEARING.  A template that WRAPS its argument.
------------------------------------------------------------------

-- `nat → obs (obs nat)`: the argument is placed under TWO `strmᵗ`s the
-- template wrote, so the head the positivity is read off is the outer
-- one while the argument sits under the inner.  It fails if a template
-- whose returned observable is not its own outermost construction is
-- read at nought.
wraps : Fn Γ₀ [] [] [] natᵗ (obs (obs natᵗ))
wraps = strmᵗ (ofᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])) ∷ []))

row-wraps-template : obsDepthᵗ wraps ≡ 2
row-wraps-template = refl

row-wraps-pos : Confirms (dep-fn-pos zeroη refl wraps)
row-wraps-pos = s≤s z≤n
