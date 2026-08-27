------------------------------------------------------------------
-- closSize READS σ ONLY AT THE INPUTS ITS TERM ACTUALLY CONTAINS.
--
-- Its own mutual family over Exp/Tm/List Tm, and nothing else is
-- mutual with it -- `Rx.Slot-Clos` consumes it as a finished fact,
-- which is an import.  The statement is the structural congruence:
-- environments agreeing below k agree on any term whose inputs all
-- sit below k.  Only the `input` clause reads σ, and `inputsBelowᵉ`
-- hands over exactly the guard the agreement hypothesis wants.
-- TWIN: `Rx.Hop-Eta-Cong.hopD-η-congᵉ`, the same induction at the hop
--   measure; this one is shorter only because no clause carries a
--   coefficient.
------------------------------------------------------------------
module Rx.Clos-Eta-Cong where

open import Data.Bool using (T; _∧_)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; suc; _+_; _<ᵇ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ctx; Exp; Tm;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Clos-Size using (closSizeᵉ; closSizeᵗ; closSizeᵗˢ)
open import Decide using (∧ʳ; ∧ˡ)

mutual
  clos-σ-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {σ₁ σ₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → σ₁ j ≡ σ₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    closSizeᵉ σ₁ e ≡ closSizeᵉ σ₂ e
  -- THE ONLY CLAUSE THAT READS σ
  clos-σ-congᵉ k ag (input i)         ok = ag i ok
  clos-σ-congᵉ k ag (ofᵉ ts)          ok = cong suc (clos-σ-congᵗˢ k ag ts ok)
  clos-σ-congᵉ k ag emptyᵉ            ok = refl
  clos-σ-congᵉ k ag (mapᵉ f e)        ok =
    cong suc (cong₂ _+_
      (clos-σ-congᵗ k ag f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
      (clos-σ-congᵉ k ag e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok)))
  clos-σ-congᵉ k ag (takeᵉ c e)       ok =
    cong suc (cong₂ _+_
      (clos-σ-congᵗ k ag c (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
      (clos-σ-congᵉ k ag e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok)))
  clos-σ-congᵉ k ag (scanᵉ f z e)     ok =
    cong suc (cong₂ _+_
      (cong₂ _+_ (clos-σ-congᵗ k ag f (∧ˡ (inputsBelowᵗ k f) zbe ok))
                 (clos-σ-congᵗ k ag z
                    (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
      (clos-σ-congᵉ k ag e (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
    zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  clos-σ-congᵉ k ag (mergeAllᵉ lim e) ok = cong suc (clos-σ-congᵉ k ag e ok)
  clos-σ-congᵉ k ag (switchAllᵉ e)    ok = cong suc (clos-σ-congᵉ k ag e ok)
  clos-σ-congᵉ k ag (exhaustAllᵉ e)   ok = cong suc (clos-σ-congᵉ k ag e ok)
  clos-σ-congᵉ k ag (μᵉ e)            ok = cong suc (clos-σ-congᵉ k ag e ok)
  clos-σ-congᵉ k ag (varᵉ x)          ok = refl
  -- cut at the gate, so its body's inputs are irrelevant here
  clos-σ-congᵉ k ag (deferᵉ e)        ok = refl

  clos-σ-congᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {σ₁ σ₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → σ₁ j ≡ σ₂ j) →
    (f : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k f) →
    closSizeᵗ σ₁ f ≡ closSizeᵗ σ₂ f
  clos-σ-congᵗ k ag (varᵗ x)      ok = refl
  clos-σ-congᵗ k ag unit̂          ok = refl
  clos-σ-congᵗ k ag (bool̂ _)      ok = refl
  clos-σ-congᵗ k ag (nat̂ _)       ok = refl
  clos-σ-congᵗ k ag (pairᵗ a b)   ok =
    cong suc (cong₂ _+_
      (clos-σ-congᵗ k ag a (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
      (clos-σ-congᵗ k ag b (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok)))
  clos-σ-congᵗ k ag (fstᵗ p)      ok = cong suc (clos-σ-congᵗ k ag p ok)
  clos-σ-congᵗ k ag (sndᵗ p)      ok = cong suc (clos-σ-congᵗ k ag p ok)
  clos-σ-congᵗ k ag (inlᵗ a)      ok = cong suc (clos-σ-congᵗ k ag a ok)
  clos-σ-congᵗ k ag (inrᵗ a)      ok = cong suc (clos-σ-congᵗ k ag a ok)
  clos-σ-congᵗ k ag (caseᵗ s l r) ok =
    cong suc (cong₂ _+_
      (cong₂ _+_ (clos-σ-congᵗ k ag s (∧ˡ (inputsBelowᵗ k s) lr ok))
                 (clos-σ-congᵗ k ag l (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
      (clos-σ-congᵗ k ag r (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
    lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  clos-σ-congᵗ k ag (ifᵗ c a b)   ok =
    cong suc (cong₂ _+_
      (cong₂ _+_ (clos-σ-congᵗ k ag c (∧ˡ (inputsBelowᵗ k c) ab ok))
                 (clos-σ-congᵗ k ag a (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
      (clos-σ-congᵗ k ag b (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
    where
    ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  clos-σ-congᵗ k ag (primᵗ _ a)   ok = cong suc (clos-σ-congᵗ k ag a ok)
  clos-σ-congᵗ k ag (strmᵗ e)     ok = cong suc (clos-σ-congᵉ k ag e ok)

  clos-σ-congᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {σ₁ σ₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → σ₁ j ≡ σ₂ j) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ts) →
    closSizeᵗˢ σ₁ ts ≡ closSizeᵗˢ σ₂ ts
  clos-σ-congᵗˢ k ag []       ok = refl
  clos-σ-congᵗˢ k ag (y ∷ ys) ok =
    cong₂ _+_
      (clos-σ-congᵗ  k ag y (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
      (clos-σ-congᵗˢ k ag ys (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
