------------------------------------------------------------------
-- THE READING READS ψ ONLY AT THE INPUTS ITS TERM ACTUALLY CONTAINS.
--
-- The obvious structural congruence: slot environments agreeing below
-- k agree on any term all of whose inputs sit below k.  Only the
-- `input` clause touches ψ at all — every other clause either ignores
-- it (`varᵉ`, `deferᵉ`, `primᵗ`, the ground literals) or is a
-- congruence over its subterms — and `inputsBelowᵉ` hands exactly the
-- guard the agreement hypothesis wants.
--
-- THE BINDERS NEED THEIR OWN CONGRUENCES, and the fold's is an
-- induction rather than a `cong`.  A binder's clause consumes a
-- READING and a TERM together, so rewriting the reading under the old
-- environment and then swapping the environment at a fixed reading are
-- two separate steps; at the fold the accumulator is itself a reading,
-- so each refold's congruence is taken at the accumulator the previous
-- one just rewrote.
--
-- IT LIVES IN ITS OWN MODULE BECAUSE IT IS A NEW MUTUAL FAMILY over
-- Exp/Tm/List Tm and nothing in the measure is mutual with it:
-- `Rx.Slot-Read` consumes it as a finished fact, which is an import
-- rather than mutuality, and putting it beside the measure would grow
-- that module's checking unit for nothing.
--
-- WHAT IT IS SPENT ON: `slotRd-fix`, the equation saying a shared
-- slot's staged reading IS its def's reading under the full
-- environment.  That is what the walk's input clause charges against,
-- and it is assembled from this plus the staging lemma next to it.
------------------------------------------------------------------
module Rx.Rd-Slot-Cong where

open import Data.Bool using (T; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _⊔′_; _<ᵇ_)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Rx.Exp using (Ctx; Exp; Tm; Fn;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Hop-Depth using (Rd; Rd₃; Env; _▸_; _⊔ᴿ_; litOf; flatten;
                                topOf; rdᵉ; rdᵗ; rdᵗˢ;
                                mapStep; scanStep; foldGo; caseStep)
open import Decide using (∧ʳ; ∧ˡ)

mutual
  rd-ψ-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    rdᵉ ψ₁ ρ e ≡ rdᵉ ψ₂ ρ e
  -- THE ONLY CLAUSE THAT READS ψ, and the guard is definitionally the
  -- agreement hypothesis's own side condition
  rd-ψ-congᵉ k ρ ag (input i)         ok = ag i ok
  rd-ψ-congᵉ k ρ ag (ofᵉ ts)          ok =
    cong (litOf (length ts)) (rd-ψ-congᵗˢ k ρ ag ts ok)
  rd-ψ-congᵉ k ρ ag emptyᵉ            ok = refl
  rd-ψ-congᵉ k ρ ag (mapᵉ f e)        ok =
    trans (cong (λ p → mapStep _ ρ p f)
                (rd-ψ-congᵉ k ρ ag e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok)))
          (mapStep-ψ-cong k ρ _ ag f
             (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
  -- the count is a natᵗ term: the reading does not read it, so neither
  -- does this
  rd-ψ-congᵉ k ρ ag (takeᵉ c e)       ok =
    rd-ψ-congᵉ k ρ ag e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok)
  rd-ψ-congᵉ k ρ ag (scanᵉ f z e)     ok =
    trans (cong (λ p → scanStep _ ρ p z f)
                (rd-ψ-congᵉ k ρ ag e
                   (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
          (scanStep-ψ-cong k ρ _ ag z f
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)
             (∧ˡ (inputsBelowᵗ k f) zbe ok))
    where
    zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  rd-ψ-congᵉ k ρ ag (mergeAllᵉ lim e) ok = cong flatten (rd-ψ-congᵉ k ρ ag e ok)
  rd-ψ-congᵉ k ρ ag (switchAllᵉ e)    ok = cong flatten (rd-ψ-congᵉ k ρ ag e ok)
  rd-ψ-congᵉ k ρ ag (exhaustAllᵉ e)   ok = cong flatten (rd-ψ-congᵉ k ρ ag e ok)
  rd-ψ-congᵉ k ρ ag (μᵉ e)            ok = rd-ψ-congᵉ k ρ ag e ok
  rd-ψ-congᵉ k ρ ag (varᵉ x)          ok = refl
  -- the reading cuts a defer, so its body's inputs are irrelevant here
  rd-ψ-congᵉ k ρ ag (deferᵉ e)        ok = refl

  mapStep-ψ-cong : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) (p : Rd₃) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (f : Fn Γ Δᵍ Δ Θ s t) → T (inputsBelowᵗ k f) →
    mapStep ψ₁ ρ p f ≡ mapStep ψ₂ ρ p f
  mapStep-ψ-cong k ρ (d , ev , h) ag f ok =
    cong (λ r → d , proj₁ r , proj₂ r ⊔′ h)
         (rd-ψ-congᵗ k (ρ ▸ (ev , h)) ag f ok)

  scanStep-ψ-cong : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) (p : Rd₃) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (z : Tm Γ Δᵍ Δ Θ t) (f : Fn Γ Δᵍ Δ Θ s t) →
    T (inputsBelowᵗ k z) → T (inputsBelowᵗ k f) →
    scanStep ψ₁ ρ p z f ≡ scanStep ψ₂ ρ p z f
  scanStep-ψ-cong k ρ (d , ev , h) ag z f okz okf =
    cong (λ a → d , proj₁ a , proj₂ a ⊔′ h)
      (trans (cong (λ s → foldGo _ ρ s (ev , h) d f) (rd-ψ-congᵗ k ρ ag z okz))
             (foldGo-ψ-cong k ρ _ (ev , h) d ag f okf))

  -- the fold's own congruence, by induction on the refold count.  It
  -- is general in the accumulator because the step changes it, so the
  -- inductive call is at a reading the previous line just rewrote
  foldGo-ψ-cong : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) (acc src : Rd) (R : ℕ) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (f : Fn Γ Δᵍ Δ Θ s t) → T (inputsBelowᵗ k f) →
    foldGo ψ₁ ρ acc src R f ≡ foldGo ψ₂ ρ acc src R f
  foldGo-ψ-cong k ρ acc src zero    ag f ok = refl
  foldGo-ψ-cong k ρ acc src (suc R) ag f ok =
    cong (acc ⊔ᴿ_)
      (trans (cong (λ a → foldGo _ ρ a src R f)
                   (rd-ψ-congᵗ k (ρ ▸ (acc ⊔ᴿ src)) ag f ok))
             (foldGo-ψ-cong k ρ _ src R ag f ok))

  rd-ψ-congᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (f : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k f) →
    rdᵗ ψ₁ ρ f ≡ rdᵗ ψ₂ ρ f
  rd-ψ-congᵗ k ρ ag (varᵗ x)      ok = refl
  rd-ψ-congᵗ k ρ ag unit̂          ok = refl
  rd-ψ-congᵗ k ρ ag (bool̂ _)      ok = refl
  rd-ψ-congᵗ k ρ ag (nat̂ _)       ok = refl
  rd-ψ-congᵗ k ρ ag (pairᵗ a b)   ok =
    cong₂ _⊔ᴿ_ (rd-ψ-congᵗ k ρ ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
               (rd-ψ-congᵗ k ρ ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  rd-ψ-congᵗ k ρ ag (fstᵗ p)      ok = rd-ψ-congᵗ k ρ ag p ok
  rd-ψ-congᵗ k ρ ag (sndᵗ p)      ok = rd-ψ-congᵗ k ρ ag p ok
  rd-ψ-congᵗ k ρ ag (inlᵗ a)      ok = rd-ψ-congᵗ k ρ ag a ok
  rd-ψ-congᵗ k ρ ag (inrᵗ a)      ok = rd-ψ-congᵗ k ρ ag a ok
  rd-ψ-congᵗ k ρ ag (caseᵗ s l r) ok =
    trans (cong (λ p → caseStep _ ρ p l r)
                (rd-ψ-congᵗ k ρ ag s (∧ˡ (inputsBelowᵗ k s) lr ok)))
          (caseStep-ψ-cong k ρ _ ag l r
             (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)
             (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
    where
    lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  rd-ψ-congᵗ k ρ ag (ifᵗ c a b)   ok =
    cong₂ _⊔ᴿ_ (rd-ψ-congᵗ k ρ ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
               (rd-ψ-congᵗ k ρ ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
    where
    ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  -- a PrimOp lands in natᵗ or boolᵗ: the reading reads it as zero
  rd-ψ-congᵗ k ρ ag (primᵗ _ a)   ok = refl
  rd-ψ-congᵗ k ρ ag (strmᵗ e)     ok = cong topOf (rd-ψ-congᵉ k ρ ag e ok)

  caseStep-ψ-cong : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) (p : Rd) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (l : Fn Γ Δᵍ Δ Θ s t) (r : Fn Γ Δᵍ Δ Θ u t) →
    T (inputsBelowᵗ k l) → T (inputsBelowᵗ k r) →
    caseStep ψ₁ ρ p l r ≡ caseStep ψ₂ ρ p l r
  caseStep-ψ-cong k ρ p ag l r okl okr =
    cong₂ _⊔ᴿ_ (rd-ψ-congᵗ k (ρ ▸ p) ag l okl)
               (rd-ψ-congᵗ k (ρ ▸ p) ag r okr)

  rd-ψ-congᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ)
    {ψ₁ ψ₂ : Fin n → Rd₃} (ρ : Env) →
    (∀ j → T (toℕ j <ᵇ k) → ψ₁ j ≡ ψ₂ j) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ts) →
    rdᵗˢ ψ₁ ρ ts ≡ rdᵗˢ ψ₂ ρ ts
  rd-ψ-congᵗˢ k ρ ag []       ok = refl
  rd-ψ-congᵗˢ k ρ ag (y ∷ ys) ok =
    cong₂ _⊔ᴿ_ (rd-ψ-congᵗ  k ρ ag y
                 (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
               (rd-ψ-congᵗˢ k ρ ag ys
                 (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
