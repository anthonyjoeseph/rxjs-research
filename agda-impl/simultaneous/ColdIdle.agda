{-# OPTIONS --guardedness #-}

-- THE COLD IDLES ONLY INSIDE A STEP.  A route the cold's count holds was
-- opened by a step's begin, and the step's closing row (a value step's
-- over, a completion's end) lies in the begin's instant.  That row is
-- not yet met: a met over would have shut the route, and the run has met
-- no end.  So whatever the run waits before lies between the begin and
-- that row, in the step's instant, under its name (`idle`).
module simultaneous.ColdIdle where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Properties using (foldl-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-∃++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import denotation.Position using (Pos; cascade; ix; last; _∙_; _≟ᵖ_; instant; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; DenEnv; enter; Ev; out; end; _≺_; _≼_)
open import denotation.Read using (Run; []; _∷_; Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-absurd; ≼-refl; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≼-split)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; begin; over)
open import simultaneous.Routed using (Idle; nm; nameOf; cnt; nm-inst)
open import simultaneous.Relations using (Met; values; values-++)
open import simultaneous.Shut using (r₀)
open import simultaneous.Layers using (run-after; run-row)
open import simultaneous.ColdFew using (Fresh)
open import simultaneous.ColdShape using (ColdRow; now-value; now-end; step-begin; step-value; step-over; step-end; cold-rows)
open import simultaneous.ColdBegin using (same-≺)
open import simultaneous.ColdEnd using (aft?)
open import simultaneous.ColdClose using (cold-close)
open import simultaneous.Instants using (btw)
open import simultaneous.ColdRuns using (run-has-ex; after-in; values-∈; rise; B⁰; not-now; beg-name)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; count; coldˢ)

------------------------------------------------------------------------
-- Runs

-- The cursor past a run holding a row: a row of it, at or past that row.
cur : ∀ {A} {t : EmissionSet A} {c} rs {q e} → Run t c rs → (q , e) ∈ rs
    → Σ Pos λ c′ → cursor c rs ≡ just c′ × q ≼ c′ × Σ (Ev A) λ e′ → (c′ , e′) ∈ rs
cur []                       []        ()
cur ((q , e) ∷ [])           (_ ∷ [])  (here refl) = q , refl , ≼-refl {q} , e , here refl
cur ((q , e) ∷ ((r , f) ∷ rs)) (_ ∷ run) (here refl) with cur ((r , f) ∷ rs) run (here refl)
... | c′ , ec , rc , e′ , m = c′ , ec , ≺→≼ {q} {c′} (≺-≼-≺ {q} {r} {c′} (run-after run (here refl)) rc) , e′ , there m
cur (_ ∷ rs)                 (_ ∷ run) (there i) with cur rs run i
... | c′ , ec , rc , e′ , m = c′ , ec , rc , e′ , there m

-- A row of a run holding a row is past its cursor, or met.
aft-or-in : ∀ {A} {t : EmissionSet A} {rs y e q eq} → Run t nothing rs → t y e → Visible e → (q , eq) ∈ rs
          → After (cursor nothing rs) y ⊎ Σ (Ev A) λ e′ → (y , e′) ∈ rs
aft-or-in {rs = rs} {y} mt x vi qm with cur rs mt qm
... | c′ , ec , _ , _ , m with aft? c′ y
...   | inj₁ h  = inj₁ (subst (λ z → After z y) (sym ec) h)
...   | inj₂ yc = inj₂ (run-has-ex mt x vi tt yc m)

-- Past a met row and before a row of its instant, only that instant.
mid : ∀ q c w y → q ≼ c → c ≺ w → w ≼ y → instant q ≡ instant y → instant w ≡ instant q
mid q c w y qc cw wy eq with ≼-split {w} {y} wy
... | inj₂ refl = sym eq
... | inj₁ wy′  = btw q w y (≼-≺-≺ {q} {c} {w} qc cw) wy′ eq

-- Past an over, a route open was begun after it.
reopen : ∀ {A} (a : List (Pos × Ev (IE A))) {y m b n k} → cnt (a ++ (y , out (instEmit (mark over) m)) ∷ b) ≡ (n , suc k)
       → instEmit (mark begin) n ∈ values b
reopen {A} a {y} {m} {b} eq with rise (count {A} (cnt a) (instEmit (mark over) m)) (values b)
                               (trans (sym (trans (cong (L.foldl count r₀) (values-++ a ((y , out (instEmit (mark over) m)) ∷ b)))
                                                  (foldl-++ count r₀ (values a) _))) eq)
... | inj₁ i       = i
... | inj₂ (_ , ())

------------------------------------------------------------------------
-- A cold's idles

module Idles {A : Set} (p : Pos) (t : EmissionSet (IE A)) (row : ∀ {y e} → t y e → Visible e → ColdRow p y e)
  (close : ∀ {T e l} → t (B⁰ (cascade T e l)) (out (instEmit (mark begin) (nm (cascade T e l ∙ []))))
         → (Σ ℕ λ i → l ≡ ix i × t (cascade T e l ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])) (out (instEmit (mark over) (nm (cascade T e l ∙ [])))))
         ⊎ (l ≡ last × t (cascade T e l ∙ (ix 1 ∷ last ∷ [])) end))
  where

  -- The row where a fresh value step closes is its over.
  at-over : ∀ {k e T e₀ i} → ColdRow {A} p k e → k ≡ (cascade T e₀ (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []))
          → Fresh p (cascade T e₀ (ix i)) → e ≡ out (instEmit (mark over) (nm (cascade T e₀ (ix i) ∙ [])))
  at-over (now-value _ zs) eq f = ⊥-elim (not-now eq f)
  at-over (now-end _ zs)   eq f = ⊥-elim (not-now eq f)
  at-over (step-begin _) ()
  at-over (step-value _) ()
  at-over (step-over _)  refl f = refl
  at-over (step-end _)   ()

  -- The row where a fresh completion closes is the end.
  at-end : ∀ {k e T e₀} → ColdRow {A} p k e → k ≡ (cascade T e₀ last ∙ (ix 1 ∷ last ∷ [])) → Fresh p (cascade T e₀ last) → e ≡ end
  at-end (now-value _ zs) eq f = ⊥-elim (not-now eq f)
  at-end (now-end _ zs)   eq f = ⊥-elim (not-now eq f)
  at-end (step-begin _) ()
  at-end (step-value _) ()
  at-end (step-over _)  ()
  at-end (step-end _)   refl f = refl

  -- What the run waits before, past a met row and before an unmet row of its instant, is of that instant.
  near : ∀ {rs q eq w y} → Met t rs → (q , eq) ∈ rs → After (cursor nothing rs) w → w ≼ y → instant q ≡ instant y
       → nm (instant q ∙ []) ≡ nameOf w
  near {rs} {q} {_} {w} {y} mt qm aw wy iy with cur rs mt qm
  ... | c′ , ec , qc , _ = cong (λ z → nm (z ∙ [])) (sym (mid q c′ w y qc (subst (λ z → After z w) ec aw) wy iy))

  idle : Idle t
  idle {rs} mt ne {w} _ aw low with cnt rs in ec
  ... | (n , zero)  = inj₁ refl
  ... | (n , suc k) with rise r₀ (values rs) ec
  ...   | inj₂ (_ , ())
  ...   | inj₁ bi with values-∈ rs bi
  ...     | q , qm with row (proj₁ (run-row mt qm)) (proj₂ (run-row mt qm))
  ...       | step-begin {T} {e} {l} fK with close (proj₁ (run-row mt qm))
  ...         | inj₂ (refl , xe) with aft-or-in mt xe tt qm
  ...           | inj₁ ay = inj₂ (near {y = cascade T e last ∙ (ix 1 ∷ last ∷ [])} mt qm aw (low xe tt ay) refl)
  ...           | inj₂ (e′ , ym) =
    ⊥-elim (ne (subst (λ z → (_ , z) ∈ rs) (at-end (row (proj₁ (run-row mt ym)) (proj₂ (run-row mt ym))) refl fK) ym))
  idle {rs} mt ne {w} _ aw low | (n , suc k) | inj₁ bi | q , qm | step-begin {T} {e} {l} fK | inj₁ (i , refl , xo)
    with aft-or-in mt xo tt qm
  ... | inj₁ ay = inj₂ (near {y = cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])} mt qm aw (low xo tt ay) refl)
  ... | inj₂ (e′ , ym) with at-over (row (proj₁ (run-row mt ym)) (proj₂ (run-row mt ym))) refl fK
  ...   | refl with ∈-∃++ ym
  ...     | a , b , refl with values-∈ b (reopen a ec)
  ...       | q′ , qm′ with beg-name (row (proj₁ (run-row mt (∈-++⁺ʳ a (there qm′)))) (proj₂ (run-row mt (∈-++⁺ʳ a (there qm′)))))
  ...         | K′ , refl , eqK , _ = ⊥-elim (
    ≺-absurd {B⁰ K′} {cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])}
      (subst (λ z → B⁰ z ≺ (cascade T e (ix i) ∙ (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ [])))
             (trans (sym (nm-inst (cascade T e (ix i)))) (trans (cong instant eqK) (nm-inst K′)))
             (same-≺ (cascade T e (ix i)) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ix 0 ∷ ix 1 ∷ ix 2 ∷ []) tt))
      (after-in a mt qm′))

------------------------------------------------------------------------
-- The cold

cold-idle : ∀ m {Δ A} (c : Timeline A) (env : DenEnv Δ) p → Idle (enter (ev m (coldˢ c) env) p)
cold-idle m c env p = Idles.idle p (enter (ev m (coldˢ c) env) p) (cold-rows m c env p)
  (λ {T} {e} {l} → cold-close m c env p {T} {e} {l})
