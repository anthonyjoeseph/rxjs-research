-- ══════════════════════════════════════════════════════════════════
-- THE JOINED CEILING DOES NOT SURVIVE A μ UNFOLD EITHER, and that
-- closes the one route the entry's descent reading had left.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  `descW` descends into the UNFOLDING at a
-- μ head while `ceilᵉ` recurses into the BODY, so a comparison of the
-- two joins clause for clause needs the ceiling to be weakly monotone
-- across an unfold.  It reads plausible for the JOIN where it is known
-- false for the parked width alone: what breaks the parked reading is
-- that the plug exposes the μ's own outW, and `ownᵉ` joins that outW
-- in at every node, so the witness that kills the narrow reading is
-- under the wide one -- 6 against 6, measured, a tie and not a break.
--
-- WHERE IT BREAKS.  Copies.  The plug is substituted once per
-- occurrence, and the occurrences sit under an `ofᵉ` inside a defer,
-- where the parked width of the whole list is the SUM of its elements'
-- outW -- so k mentions of the μ-var become k copies of the μ's own
-- width, joined against a ceiling that counted the var at zero.  Three
-- mentions read eighteen against six, two read twelve, and k is a free
-- parameter of the program, so no constant closes it.  That is the
-- affine shape the parked width's own refutation predicted, arriving
-- at the join: widening the measure does not help, because the defect
-- is a multiplicity and not a missing summand.
--
-- WHAT IT LEAVES.  A ceiling that is free of any level cannot price an
-- unfold, so the entry's descent has to charge the μ edge the way the
-- caps face already does -- existentially in a level, with the width
-- half derived from the size hypothesis -- rather than by comparing
-- two syntactic joins at one fixed index.
--
-- WHAT IS HAND-BUILT.  Nothing: both sides are read off the syntax by
-- the real measure, at a slot telescope of one shared definition.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Ceil-Unfold-Mu where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; s≤s)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ctx; Exp; natᵗ; ofᵉ; mergeAllᵉ; deferᵉ; varᵉ; μᵉ; unfoldμ;
         emptyᵉ; strmᵗ; nat̂)
open import Rx.Slots using (Slots; shared)
open import Rx.Frame-Width using (ceilᵉ)

Γ : Ctx 1
Γ = natᵗ ∷ᵛ []ᵛ

sl : Slots Γ
sl i = shared emptyᵉ

-- THE TEMPLATE, WITH THREE MENTIONS OF THE μ-VAR.  The defer is what
-- makes the mentions visible to the parked half at all, and the `ofᵉ`
-- beside it is what gives the μ a width of its own to be copied.
body : Exp Γ (natᵗ ∷ []) [] [] natᵗ
body = mergeAllᵉ nothing
         (ofᵉ (strmᵗ (deferᵉ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (varᵉ (here refl))
                     ∷ strmᵗ (varᵉ (here refl))
                     ∷ strmᵗ (varᵉ (here refl)) ∷ []))))
             ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ []))

parked≡6 : ceilᵉ 1 sl (μᵉ body) ≡ 6
parked≡6 = refl

unfolded≡18 : ceilᵉ 1 sl (unfoldμ body) ≡ 18
unfolded≡18 = refl

Ceilᵉ-Unfoldμ-Monotone : Set
Ceilᵉ-Unfoldμ-Monotone = ∀ {n} {Γ′ : Ctx n} {t}
  (j : ℕ) (sl′ : Slots Γ′) (b : Exp Γ′ (t ∷ []) [] [] t) →
  ceilᵉ j sl′ (unfoldμ b) ≤ ceilᵉ j sl′ (μᵉ b)

ceil-unfoldμ-absurd : Ceilᵉ-Unfoldμ-Monotone → ⊥
ceil-unfoldμ-absurd h with h 1 sl body
... | s₁ = go s₁
  where
  go : 18 ≤ 6 → ⊥
  go (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

-- THE SAME DEFECT AT TWO MENTIONS, which is what says the gap is a
-- multiplicity: the reading moves with the copy count and not with the
-- shape.
body₂ : Exp Γ (natᵗ ∷ []) [] [] natᵗ
body₂ = mergeAllᵉ nothing
          (ofᵉ (strmᵗ (deferᵉ (mergeAllᵉ nothing
                  (ofᵉ (strmᵗ (mergeAllᵉ nothing
                          (ofᵉ (strmᵗ (varᵉ (here refl))
                              ∷ strmᵗ (varᵉ (here refl)) ∷ []))) ∷ []))))
              ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ []))

parked₂≡6 : ceilᵉ 1 sl (μᵉ body₂) ≡ 6
parked₂≡6 = refl

unfolded₂≡12 : ceilᵉ 1 sl (unfoldμ body₂) ≡ 12
unfolded₂≡12 = refl
