-- AND THE SAME ARM AGAIN, FROM THE OTHER SIDE: A BINDER READ ON BOTH
-- SIDES OF A `caseᵗ` IS CHARGED TWICE, SO THE OPEN READING IS NOT A
-- SUM.
--
-- The rebinding arm adds its scrutinee, which is what makes a branch
-- wrapping its binder priceable at all.  But SUBSTITUTION reaches the
-- scrutinee and the branch alike, so an environment entry occurring in
-- both is written into both, and the clause that adds them then counts
-- that one entry twice over.  A price stated as the template's reading
-- PLUS one bound on the environment cannot survive that: the second
-- copy arrives with no addend left to pay for it.
--
-- THE WITNESS.  One observable in the environment, reading one and so
-- measuring two through `reify`; a template that scrutinises that
-- binder and, in the branch, WRAPS the very same binder again.  The
-- template reads three and the environment two, so a sum claims five;
-- the instance lands at six, which is the entry paid once in the
-- scrutinee and once more under the branch's wrap.
--
-- WHAT THIS IS NOT.  It is not the join coming back.  A join at this
-- arm is separately refuted, at a scrutinee the TEMPLATE writes, where
-- no environment is involved at all — so the two witnesses close
-- opposite escapes and neither repair answers both.  What is left
-- between them is a currency question rather than a clause: the arm
-- composes, and composition is not priced by adding a constant.
--
-- NOT REACHED: how many times it can be paid.  One nesting doubles the
-- entry; whether a chain of `caseᵗ` multiplies it, and in what, is the
-- quantity nothing here instantiates.
module Refuted.Case-Twice where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; Tm; Val; natᵗ; unitᵗ; obs; _+ᵗ_; varᵗ;
  nat̂; inlᵗ; caseᵗ; strmᵗ; ofᵉ; emptyᵉ; evalWith)
open import Rx.Obs-Depth using (depᵗ; depᵛ)
open import Rx.Obs-Depth.Substitution using (envDepth; dep-eval-open)

open import Refuted.Apparatus using (zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

----------------------------------------------------------------------
-- 1.  THE ENVIRONMENT.  One observable, reading one; measured through
-- `reify` it carries the one wrap that reading does not have, so the
-- entry is two and that is the addend the statement is given.
----------------------------------------------------------------------

Inner : Ty
Inner = obs natᵗ

o : Val Γ₀ (obs Inner)
o = ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])

env : All (Val Γ₀) (obs Inner ∷ [])
env = o ∷ᵃ []ᵃ

entry-is : envDepth {Γ = Γ₀} zeroη env ≡ 2
entry-is = refl

----------------------------------------------------------------------
-- 2.  THE TEMPLATE, WHICH READS THAT ONE BINDER TWICE — once as the
-- thing scrutinised and once under the branch's wrap.  Neither
-- occurrence writes anything itself, so the whole template reads three
-- and every figure below comes from the environment.
----------------------------------------------------------------------

scrut : Tm Γ₀ [] [] (obs Inner ∷ []) (obs Inner +ᵗ unitᵗ)
scrut = inlᵗ (varᵗ (here refl))

-- the OUTER binder, reached past the one the `caseᵗ` itself binds
left : Tm Γ₀ [] [] (obs Inner ∷ obs Inner ∷ []) (obs (obs Inner))
left = strmᵗ (ofᵉ (varᵗ (there (here refl)) ∷ []))

right : Tm Γ₀ [] [] (unitᵗ ∷ obs Inner ∷ []) (obs (obs Inner))
right = strmᵗ emptyᵉ

tm : Tm Γ₀ [] [] (obs Inner ∷ []) (obs (obs (obs Inner)))
tm = strmᵗ (ofᵉ (caseᵗ scrut left right ∷ []))

template-is : depᵗ {Γ = Γ₀} zeroη tm ≡ 3
template-is = refl

----------------------------------------------------------------------
-- 3.  THE TWO FIGURES THAT MEET.  A sum claims five; the instance is
-- six, which is one more than every addend the statement has.
----------------------------------------------------------------------

emission-is : depᵛ {Γ = Γ₀} zeroη (obs (obs (obs Inner)))
                (evalWith tm env) ≡ 6
emission-is = refl

case-twice-false : ⊥
case-twice-false with dep-eval-open {Γ = Γ₀} zeroη tm env 2 (s≤s (s≤s z≤n))
... | s≤s (s≤s (s≤s (s≤s (s≤s ()))))

