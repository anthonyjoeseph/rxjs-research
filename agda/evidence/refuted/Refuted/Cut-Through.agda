-- ══════════════════════════════════════════════════════════════════
-- CUT-THROUGH: the dying-source close bound, as stated, is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Cut-Through where

open import Data.Bool using (true; false)
open import Data.Nat  using (_≤_; _≡ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Maybe using (just)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Source)
open import Rx.Exp  using (Ctx; Closed; natᵗ; ofᵉ; nat̂)
open import Rx.Protocol using (countIn; applyEvents)
open import Rx.Evaluator using (EvalSt; st-init; NodeId; RegId; Chain; root; take-f; _↠_; cutThrough; memberSource;
  retagEvents)
open import Verify-Well-Formed.Part1 using (countRegs; closeCount)

----------------------------------------------------------------------
-- THE WITNESS.  One registration, on source 0, whose chain passes
-- through node 0 — so cutThrough names it a victim.  It has NOT been
-- delivered (st-init leaves `delivered = []`), so the guard
-- `delivered ∧ memberSource src dying` is FALSE and its close IS
-- emitted.  Source 0 is dying.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ (nat̂ 1 ∷ [])

victim : RegId × Source × Chain Γ₀ natᵗ
victim = 7 , 0 , (natᵗ , take-f 0 ↠ root)

st₀ : EvalSt e₀
st₀ = record (st-init e₀) { registry = victim ∷ [] ; dying = 0 ∷ [] }

----------------------------------------------------------------------
-- THE DEFECT.  `L₁` is universally quantified and the hypothesis
-- constrains it ONLY at NON-dying sources, while the conclusion speaks
-- ONLY about DYING ones.  So nothing stops L₁ = [], which satisfies the
-- hypothesis vacuously here (the registry's only source is the dying
-- one, so every non-dying source has countRegs = 0 = countIn s []) and
-- makes the conclusion demand 1 ≤ 0.
--
-- This is CLAUDE.md's first almost-always-wrong shape: a conclusion
-- needing information that appears in NO hypothesis.  The repair is a
-- restatement, not a proof — the (LAG) ledger in the postulate's own
-- header is the fact that must be hypothesised AT the dying source.
----------------------------------------------------------------------

cutThrough-close-bound-dying-absurd :
  (∀ {A : Set} {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (nid : NodeId) (st : EvalSt e) (L₁ : List Source) →
     (∀ s → memberSource s (EvalSt.dying st) ≡ false →
        countIn s L₁ ≡ countRegs s (EvalSt.registry st)) →
     ∀ s → memberSource s (EvalSt.dying st) ≡ true →
       closeCount s (retagEvents {B = A}
         (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                   (EvalSt.regWatermark st)
                                   (EvalSt.dying st) (EvalSt.registry st)))))
       ≤ countIn s L₁)
  → ⊥
cutThrough-close-bound-dying-absurd bound
  with bound {A = ⊥} 0 st₀ [] hyp 0 refl
  where
  hyp : ∀ s → memberSource s (EvalSt.dying st₀) ≡ false →
              countIn s [] ≡ countRegs s (EvalSt.registry st₀)
  hyp s p with s ≡ᵇ 0
  hyp s () | true
  hyp s p  | false = refl
... | ()

----------------------------------------------------------------------
-- THE TWIN HAS THE SAME DEFECT, and its `applyEvents` premise does not
-- repair it: that premise ties L′ to L₁, but L₁ itself is still
-- unconstrained at the dying source.  Take L₁ = 0 ∷ 0 ∷ [] — the
-- hypothesis still holds vacuously (every NON-dying source has
-- countIn s L₁ = 0 = countRegs s registry) — and the single emitted
-- `close 0 cut` removes one copy, landing L′ = 0 ∷ [].  The registry
-- keeps nothing (the lone entry was the victim), so the conclusion
-- demands 1 ≡ 0.
----------------------------------------------------------------------

cutThrough-live-dying-absurd :
  (∀ {A : Set} {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (nid : NodeId) (st : EvalSt e) (L₁ L′ : List Source) →
     (∀ s → memberSource s (EvalSt.dying st) ≡ false →
        countIn s L₁ ≡ countRegs s (EvalSt.registry st)) →
     applyEvents {A}
       (retagEvents (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                              (EvalSt.regWatermark st)
                                              (EvalSt.dying st)
                                              (EvalSt.registry st)))))
       L₁ [] false ≡ just (L′ , [] , false) →
     ∀ s → memberSource s (EvalSt.dying st) ≡ true →
       countIn s L′ ≡ countRegs s
         (proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                            (EvalSt.dying st) (EvalSt.registry st))))
  → ⊥
cutThrough-live-dying-absurd live
  with live {A = ⊥} 0 st₀ (0 ∷ 0 ∷ []) (0 ∷ []) hyp refl 0 refl
  where
  hyp : ∀ s → memberSource s (EvalSt.dying st₀) ≡ false →
              countIn s (0 ∷ 0 ∷ []) ≡ countRegs s (EvalSt.registry st₀)
  hyp s p with s ≡ᵇ 0
  hyp s () | true
  hyp s p  | false = refl
... | ()
