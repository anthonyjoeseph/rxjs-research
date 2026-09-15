------------------------------------------------------------------
-- THE READING TOUCHES η ONLY AT THE INPUTS ITS TERM ACTUALLY CONTAINS.
--
-- It lives in its own module because it is a NEW mutual family over
-- Exp/Tm/List Tm and nothing in the measure is mutual with it —
-- `Rx.Slot-Depth` consumes it as a finished fact, which is an import
-- rather than mutuality, and that keeps the measure's own block the
-- size it was.
--
-- WHY IT IS THE LOAD-BEARING HALF RATHER THAN PLUMBING.  The staged
-- environment is built by recursion on the slot index, so what it holds
-- at stage k is right BELOW k and nought at and above it.  Turning that
-- into the fixpoint equation a connect spends needs exactly one fact:
-- a definition confined below k cannot tell the stage from the answer.
-- This is that fact, and `inputsBelowᵉ` — the telescope's own
-- stratification side condition — hands each clause the guard its
-- agreement hypothesis wants.
--
-- THE BOOLS ARE EXPLICIT ON PURPOSE, and it is the one place this
-- module is awkward.  `T` is a FUNCTION on Bool rather than a datatype,
-- so `T ?a =?= T (inputsBelowᵗ k f)` cannot be inverted while the
-- argument is stuck on a variable term — which it always is here — and
-- with the Bools implicit every call site raises an unsolved meta.
-- Passing them costs verbosity and buys total independence from
-- inference; `Data.Bool.Properties.T-∧` has the same problem behind
-- a ⇔.
------------------------------------------------------------------
module Rx.Obs-Depth.Eta-Cong where

open import Data.Bool using (true; false; T; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _⊔_; _<ᵇ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

open import Rx.Exp using (Ctx; Exp; Tm;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ; bindᵃᵗ; bindᵃᵉ; bindˢᵗ)

private
  -- the two projections out of a Bool conjunction's truth, with the
  -- Bools where inference can see them
  ∧ˡ : ∀ a b → T (a ∧ b) → T a
  ∧ˡ true  b p = tt
  ∧ˡ false b ()

  ∧ʳ : ∀ a b → T (a ∧ b) → T b
  ∧ʳ true  b p = p
  ∧ʳ false b ()

mutual
  dep-η-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ) (m : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    depᵉ η₁ m e ≡ depᵉ η₂ m e
  -- THE ONLY CLAUSE THAT READS η, and the guard is definitionally the
  -- agreement hypothesis's own side condition
  dep-η-congᵉ k m ag (input i)        ok = ag i ok
  dep-η-congᵉ k m ag (ofᵉ ts)         ok = dep-η-congᵗˢ k m ag ts ok
  dep-η-congᵉ k m ag emptyᵉ           ok = refl
  dep-η-congᵉ k m {η₁} {η₂} ag (mapᵉ f e)       ok =
    trans (cong (λ b → depᵗ η₁ b f ⊔ depᵉ η₁ m e) beq)
          (cong₂ _⊔_ (dep-η-congᵗ k (bindᵃᵉ η₂ m e) ag f
                        (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
                     eeq)
    where
    eeq = dep-η-congᵉ k m ag e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok)
    beq : bindᵃᵉ η₁ m e ≡ bindᵃᵉ η₂ m e
    beq = cong (_⊔ m) eeq
  dep-η-congᵉ k m {η₁} {η₂} ag (takeᵉ c e)      ok =
    trans (cong (λ b → depᵗ η₁ b c ⊔ depᵉ η₁ m e) beq)
          (cong₂ _⊔_ (dep-η-congᵗ k (bindᵃᵉ η₂ m e) ag c
                        (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
                     eeq)
    where
    eeq = dep-η-congᵉ k m ag e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok)
    beq : bindᵃᵉ η₁ m e ≡ bindᵃᵉ η₂ m e
    beq = cong (_⊔ m) eeq
  dep-η-congᵉ k m {η₁} {η₂} ag (scanᵉ f z e)    ok =
    trans (cong (λ b → depᵗ η₁ b f ⊔ depᵗ η₁ m z ⊔ depᵉ η₁ m e) beq)
          (cong₂ _⊔_ (cong₂ _⊔_ (dep-η-congᵗ k (bindˢᵗ η₂ m z e) ag f
                                   (∧ˡ (inputsBelowᵗ k f) ze ok))
                                zeq)
                     eeq)
    where
    ze   = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    rest = ∧ʳ (inputsBelowᵗ k f) ze ok
    zeq  = dep-η-congᵗ k m ag z (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)
    eeq  = dep-η-congᵉ k m ag e (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)
    beq : bindˢᵗ η₁ m z e ≡ bindˢᵗ η₂ m z e
    beq = cong₂ (λ a b → (a ⊔ m) ⊔ b) eeq zeq
  dep-η-congᵉ k m ag (mergeAllᵉ lim e) ok = dep-η-congᵉ k m ag e ok
  dep-η-congᵉ k m ag (switchAllᵉ e)   ok = dep-η-congᵉ k m ag e ok
  dep-η-congᵉ k m ag (exhaustAllᵉ e)  ok = dep-η-congᵉ k m ag e ok
  dep-η-congᵉ k m ag (μᵉ e)           ok = dep-η-congᵉ k m ag e ok
  dep-η-congᵉ k m ag (varᵉ x)         ok = refl
  -- the reading cuts a `deferᵉ`, so its body's inputs are irrelevant here
  dep-η-congᵉ k m ag (deferᵉ e)       ok = refl

  dep-η-congᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ) (m : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (f : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k f) →
    depᵗ η₁ m f ≡ depᵗ η₂ m f
  dep-η-congᵗ k m ag (varᵗ x)      ok = refl
  dep-η-congᵗ k m ag unit̂          ok = refl
  dep-η-congᵗ k m ag (bool̂ _)      ok = refl
  dep-η-congᵗ k m ag (nat̂ _)       ok = refl
  dep-η-congᵗ k m ag (pairᵗ a b)   ok =
    cong₂ _⊔_ (dep-η-congᵗ k m ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
              (dep-η-congᵗ k m ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  dep-η-congᵗ k m ag (fstᵗ p)      ok = dep-η-congᵗ k m ag p ok
  dep-η-congᵗ k m ag (sndᵗ p)      ok = dep-η-congᵗ k m ag p ok
  dep-η-congᵗ k m ag (inlᵗ a)      ok = dep-η-congᵗ k m ag a ok
  dep-η-congᵗ k m ag (inrᵗ a)      ok = dep-η-congᵗ k m ag a ok
  dep-η-congᵗ k m {η₁} {η₂} ag (caseᵗ s l r) ok =
    trans (cong (λ b → depᵗ η₁ b l ⊔ depᵗ η₁ b r) beq)
          (cong₂ _⊔_ (dep-η-congᵗ k (bindᵃᵗ η₂ m s) ag l
                        (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
                     (dep-η-congᵗ k (bindᵃᵗ η₂ m s) ag r
                        (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
    lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    rest = ∧ʳ (inputsBelowᵗ k s) lr ok
    beq  : bindᵃᵗ η₁ m s ≡ bindᵃᵗ η₂ m s
    beq  = cong (λ x → suc x ⊔ m)
             (dep-η-congᵗ k m ag s (∧ˡ (inputsBelowᵗ k s) lr ok))
  dep-η-congᵗ k m ag (ifᵗ c a b)   ok =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-η-congᵗ k m ag c (∧ˡ (inputsBelowᵗ k c) ab ok))
                         (dep-η-congᵗ k m ag a
                            (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
              (dep-η-congᵗ k m ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
    where
    ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  dep-η-congᵗ k m ag (primᵗ _ a)   ok = dep-η-congᵗ k m ag a ok
  dep-η-congᵗ k m ag (strmᵗ e)     ok = cong suc (dep-η-congᵉ k m ag e ok)

  dep-η-congᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ) (m : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ts) →
    depᵗˢ η₁ m ts ≡ depᵗˢ η₂ m ts
  dep-η-congᵗˢ k m ag []       ok = refl
  dep-η-congᵗˢ k m ag (y ∷ ys) ok =
    cong₂ _⊔_ (dep-η-congᵗ  k m ag y
                 (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
              (dep-η-congᵗˢ k m ag ys
                 (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
