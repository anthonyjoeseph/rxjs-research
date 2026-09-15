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
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _<ᵇ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ctx; Exp; Tm;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ)

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
  dep-η-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    depᵉ η₁ e ≡ depᵉ η₂ e
  -- THE ONLY CLAUSE THAT READS η, and the guard is definitionally the
  -- agreement hypothesis's own side condition
  dep-η-congᵉ k ag (input i)        ok = ag i ok
  dep-η-congᵉ k ag (ofᵉ ts)         ok = dep-η-congᵗˢ k ag ts ok
  dep-η-congᵉ k ag emptyᵉ           ok = refl
  dep-η-congᵉ k ag (mapᵉ f e)       ok =
    cong₂ _⊔_ (dep-η-congᵗ k ag f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
              (dep-η-congᵉ k ag e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
  dep-η-congᵉ k ag (takeᵉ c e)      ok =
    cong₂ _⊔_ (dep-η-congᵗ k ag c (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
              (dep-η-congᵉ k ag e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
  dep-η-congᵉ k ag (scanᵉ f z e)    ok =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-η-congᵗ k ag f (∧ˡ (inputsBelowᵗ k f) ze ok))
                         (dep-η-congᵗ k ag z (∧ˡ (inputsBelowᵗ k z)
                                                 (inputsBelowᵉ k e) rest)))
              (dep-η-congᵉ k ag e (∧ʳ (inputsBelowᵗ k z)
                                      (inputsBelowᵉ k e) rest))
    where
    ze   = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    rest = ∧ʳ (inputsBelowᵗ k f) ze ok
  dep-η-congᵉ k ag (mergeAllᵉ lim e) ok = dep-η-congᵉ k ag e ok
  dep-η-congᵉ k ag (switchAllᵉ e)   ok = dep-η-congᵉ k ag e ok
  dep-η-congᵉ k ag (exhaustAllᵉ e)  ok = dep-η-congᵉ k ag e ok
  dep-η-congᵉ k ag (μᵉ e)           ok = dep-η-congᵉ k ag e ok
  dep-η-congᵉ k ag (varᵉ x)         ok = refl
  -- the reading cuts a `deferᵉ`, so its body's inputs are irrelevant here
  dep-η-congᵉ k ag (deferᵉ e)       ok = refl

  dep-η-congᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (f : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k f) →
    depᵗ η₁ f ≡ depᵗ η₂ f
  dep-η-congᵗ k ag (varᵗ x)      ok = refl
  dep-η-congᵗ k ag unit̂          ok = refl
  dep-η-congᵗ k ag (bool̂ _)      ok = refl
  dep-η-congᵗ k ag (nat̂ _)       ok = refl
  dep-η-congᵗ k ag (pairᵗ a b)   ok =
    cong₂ _⊔_ (dep-η-congᵗ k ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
              (dep-η-congᵗ k ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  dep-η-congᵗ k ag (fstᵗ p)      ok = dep-η-congᵗ k ag p ok
  dep-η-congᵗ k ag (sndᵗ p)      ok = dep-η-congᵗ k ag p ok
  dep-η-congᵗ k ag (inlᵗ a)      ok = dep-η-congᵗ k ag a ok
  dep-η-congᵗ k ag (inrᵗ a)      ok = dep-η-congᵗ k ag a ok
  dep-η-congᵗ k ag (caseᵗ s l r) ok =
    cong suc (cong₂ _+_ (dep-η-congᵗ k ag s (∧ˡ (inputsBelowᵗ k s) lr ok))
                        (cong₂ _⊔_ (dep-η-congᵗ k ag l
                                      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
                                   (dep-η-congᵗ k ag r
                                      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))))
    where
    lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  dep-η-congᵗ k ag (ifᵗ c a b)   ok =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-η-congᵗ k ag c (∧ˡ (inputsBelowᵗ k c) ab ok))
                         (dep-η-congᵗ k ag a
                            (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
              (dep-η-congᵗ k ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
    where
    ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  dep-η-congᵗ k ag (primᵗ _ a)   ok = dep-η-congᵗ k ag a ok
  dep-η-congᵗ k ag (strmᵗ e)     ok = cong suc (dep-η-congᵉ k ag e ok)

  dep-η-congᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ts) →
    depᵗˢ η₁ ts ≡ depᵗˢ η₂ ts
  dep-η-congᵗˢ k ag []       ok = refl
  dep-η-congᵗˢ k ag (y ∷ ys) ok =
    cong₂ _⊔_ (dep-η-congᵗ  k ag y
                 (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
              (dep-η-congᵗˢ k ag ys
                 (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
