------------------------------------------------------------------
-- hopD READS η ONLY AT THE INPUTS ITS TERM ACTUALLY CONTAINS.
--
-- Ex-postulate (2026-08-14), formerly `hopD-η-congᵉ` in Rx.Slot-Hop.
-- It lives in its own module because it is a NEW mutual family over
-- Exp/Tm/List Tm and nothing else here is mutual with it — Slot-Hop
-- consumes it as a finished fact, which is an import, not mutuality.
--
-- WHY IT MATTERS rather than being plumbing: `slotHop-fix` is the
-- equation the walk face's input clause spends after the input-wet
-- refutation, and it was assembled from THIS plus `ηAt-agrees`.  While
-- both were postulates the whole restatement rested on two unproven
-- claims; Demand-Probe series T probed them, but a probe is a receipt
-- and this is a proof.
--
-- THE STATEMENT is the obvious structural congruence: environments that
-- agree below k agree on any term all of whose inputs sit below k.  Only
-- the `input` clause touches η at all, and `inputsBelowᵉ` hands exactly
-- the guard the agreement hypothesis wants — every other clause either
-- ignores η (varᵉ, deferᵉ, primᵗ, the ground literals) or is a
-- congruence over its subterms.  `pm` never appears on the η side, so
-- the coefficients pass through untouched.
------------------------------------------------------------------
module Rx.Hop-Eta-Cong where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Unit using (tt)
open import Data.Nat  using (ℕ; suc; _+_; _*_; _^_; _⊔_; _<ᵇ_)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ctx; Exp; Tm;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; pmᵗ)

-- The two projections out of a Bool conjunction's truth.
--
-- THE BOOLS ARE EXPLICIT ON PURPOSE, and this is the one place the
-- module is awkward.  `T` is a FUNCTION on Bool, not a datatype, so
-- `T ?a =?= T (inputsBelowᵗ k f)` cannot be inverted while the argument
-- is stuck on a variable term — which it always is here.  With the
-- Bools implicit every call site raises an unsolved meta (measured).
-- Passing them costs verbosity and buys total independence from
-- inference; `T-∧` in Data.Bool.Properties has the same problem behind
-- a ⇔.
∧ˡ : ∀ (a b : Bool) → T (a ∧ b) → T a
∧ˡ true  b _  = tt
∧ˡ false b ()

∧ʳ : ∀ (a b : Bool) → T (a ∧ b) → T b
∧ʳ true  b h = h
∧ʳ false b ()

mutual
  hopD-η-congᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (e : Exp Γ Δᵍ Δ Θ t) → T (inputsBelowᵉ k e) →
    hopDᵉ V η₁ e ≡ hopDᵉ V η₂ e
  -- THE ONLY CLAUSE THAT READS η, and the guard is definitionally the
  -- agreement hypothesis's own side condition
  hopD-η-congᵉ V k ag (input i)       ok = ag i ok
  hopD-η-congᵉ V k ag (ofᵉ ts)        ok = hopD-η-congᵗˢ V k ag ts ok
  hopD-η-congᵉ V k ag emptyᵉ          ok = refl
  hopD-η-congᵉ V k ag (mapᵉ f e)      ok =
    cong₂ _+_ (hopD-η-congᵗ V k ag f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
              (cong ((pmᵗ V 0 f ⊔ 1) *_)
                    (hopD-η-congᵉ V k ag e
                       (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok)))
  -- the count is a natᵗ term: hopD does not read it, so neither does this
  hopD-η-congᵉ V k ag (takeᵉ c e)     ok =
    hopD-η-congᵉ V k ag e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok)
  hopD-η-congᵉ V k ag (scanᵉ f z e)   ok =
    cong (((2 + pmᵗ V 0 f) ^ V) *_)
         (cong₂ _+_ (cong₂ _+_ (hopD-η-congᵗ V k ag f
                                  (∧ˡ (inputsBelowᵗ k f) zbe ok))
                               (hopD-η-congᵗ V k ag z
                                  (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
                    (hopD-η-congᵉ V k ag e
                       (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
    zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
    rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  hopD-η-congᵉ V k ag (mergeAllᵉ e)   ok = cong suc (hopD-η-congᵉ V k ag e ok)
  hopD-η-congᵉ V k ag (concatAllᵉ e)  ok = cong suc (hopD-η-congᵉ V k ag e ok)
  hopD-η-congᵉ V k ag (switchAllᵉ e)  ok = cong suc (hopD-η-congᵉ V k ag e ok)
  hopD-η-congᵉ V k ag (exhaustAllᵉ e) ok = cong suc (hopD-η-congᵉ V k ag e ok)
  hopD-η-congᵉ V k ag (μᵉ e)          ok = hopD-η-congᵉ V k ag e ok
  hopD-η-congᵉ V k ag (varᵉ x)        ok = refl
  -- hopD cuts deferᵉ, so its body's inputs are irrelevant here
  hopD-η-congᵉ V k ag (deferᵉ e)      ok = refl

  hopD-η-congᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (f : Tm Γ Δᵍ Δ Θ t) → T (inputsBelowᵗ k f) →
    hopDᵗ V η₁ f ≡ hopDᵗ V η₂ f
  hopD-η-congᵗ V k ag (varᵗ x)      ok = refl
  hopD-η-congᵗ V k ag unit̂          ok = refl
  hopD-η-congᵗ V k ag (bool̂ _)      ok = refl
  hopD-η-congᵗ V k ag (nat̂ _)       ok = refl
  hopD-η-congᵗ V k ag (pairᵗ a b)   ok =
    cong₂ _⊔_ (hopD-η-congᵗ V k ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
              (hopD-η-congᵗ V k ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  hopD-η-congᵗ V k ag (fstᵗ p)      ok = hopD-η-congᵗ V k ag p ok
  hopD-η-congᵗ V k ag (sndᵗ p)      ok = hopD-η-congᵗ V k ag p ok
  hopD-η-congᵗ V k ag (inlᵗ a)      ok = hopD-η-congᵗ V k ag a ok
  hopD-η-congᵗ V k ag (inrᵗ a)      ok = hopD-η-congᵗ V k ag a ok
  hopD-η-congᵗ V k ag (caseᵗ s l r) ok =
    cong₂ _+_ (cong₂ _⊔_ (hopD-η-congᵗ V k ag l
                            (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
                         (hopD-η-congᵗ V k ag r
                            (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
              (cong ((pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1) *_)
                    (hopD-η-congᵗ V k ag s (∧ˡ (inputsBelowᵗ k s) lr ok)))
    where
    lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
    rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  hopD-η-congᵗ V k ag (ifᵗ c a b)   ok =
    cong₂ _⊔_ (hopD-η-congᵗ V k ag a
                 (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
              (hopD-η-congᵗ V k ag b
                 (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
    where
    ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
    rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  -- a PrimOp lands in natᵗ or boolᵗ: hopD reads it as 0
  hopD-η-congᵗ V k ag (primᵗ _ a)   ok = refl
  hopD-η-congᵗ V k ag (strmᵗ e)     ok = hopD-η-congᵉ V k ag e ok

  hopD-η-congᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ)
    {η₁ η₂ : Fin n → ℕ} →
    (∀ j → T (toℕ j <ᵇ k) → η₁ j ≡ η₂ j) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → T (inputsBelowᵗˢ k ts) →
    hopDᵗˢ V η₁ ts ≡ hopDᵗˢ V η₂ ts
  hopD-η-congᵗˢ V k ag []       ok = refl
  hopD-η-congᵗˢ V k ag (y ∷ ys) ok =
    cong₂ _⊔_ (hopD-η-congᵗ  V k ag y
                 (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
              (hopD-η-congᵗˢ V k ag ys
                 (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
