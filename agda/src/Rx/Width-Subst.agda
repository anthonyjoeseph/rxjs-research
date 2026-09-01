------------------------------------------------------------------
-- THE WIDTH FAMILY IS BLIND TO A μ SUBSTITUTION, every member of it.
--
-- A Δᵍ variable is reachable only from under a `deferᵉ`, and every
-- measure in this family reads a defer as zero -- a defer crosses a
-- tick, so nothing under it belongs to this frame.  So the plug an
-- unfolding substitutes lands where nothing is looking, and the whole
-- family is UNCHANGED rather than merely bounded.  That is the same
-- mechanism `hopD-elimGᵉ` runs on, and the induction is its shape: a
-- congruence at every constructor, `refl` at the variable and at the
-- defer.
--
-- WHAT IT IS FOR.  The descent's ceiling has to survive the unfold its
-- μ clause performs, and the JOINED ceiling does not -- it descends
-- into defers, so it sees the plug once per occurrence.
-- REFUTED: `Refuted.Ceil-Unfold-Mu` -- eighteen against six at three
--   mentions of the variable, which is what the join costs and what
--   these equalities are the alternative to.
------------------------------------------------------------------
module Rx.Width-Subst where

open import Data.Bool using (true; false)
open import Data.Nat.Properties using (⊔-assoc; ⊔-idem)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_)
open import Data.Fin  using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Rx.Exp
  using (Ctx; Exp; Tm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
         switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
         varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ;
         primᵗ; strmᵗ; elimGExp; elimGTm; elimGTms; unfoldμ)
open import Rx.Slots using (Slots)
open import Rx.Frame-Width
  using (pmOⱽ; pmIⱽ; pmIᵗⱽ; pmIᵗˢⱽ; outWⱽ; innWⱽ; innWᵗⱽ; innWᵗˢⱽ; _∈ᵇ_)
open import Rx.Slots using (scripted; shared)

open import Rx.Burst-Ceil using (bCeilᵉ; bKidsᵉ)

len-elimGTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
  length (elimGTms x cl ts) ≡ length ts
len-elimGTms x cl []       = refl
len-elimGTms x cl (y ∷ ys) = cong suc (len-elimGTms x cl ys)

mutual
  pmO-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (k : ℕ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (e : Exp Γ Δᵍ Δ Θ u) →
    pmOⱽ j vs sl k (elimGExp x cl e) ≡ pmOⱽ j vs sl k e
  pmO-elimGᵉ j vs sl k x cl (input i)         = refl
  pmO-elimGᵉ j vs sl k x cl (ofᵉ ts)          = refl
  pmO-elimGᵉ j vs sl k x cl emptyᵉ            = refl
  pmO-elimGᵉ j vs sl k x cl (mapᵉ f e)        = pmO-elimGᵉ j vs sl k x cl e
  pmO-elimGᵉ j vs sl k x cl (takeᵉ c e)       = pmO-elimGᵉ j vs sl k x cl e
  pmO-elimGᵉ j vs sl k x cl (scanᵉ f z e)     = pmO-elimGᵉ j vs sl k x cl e
  pmO-elimGᵉ j vs sl k x cl (mergeAllᵉ lim e) =
    cong₂ _+_ (cong₂ _*_ (outW-elimGᵉ j vs sl x cl e) (pmI-elimGᵉ j vs sl k x cl e))
              (cong₂ _*_ (pmO-elimGᵉ j vs sl k x cl e) (innW-elimGᵉ j vs sl x cl e))
  pmO-elimGᵉ j vs sl k x cl (switchAllᵉ e)    =
    cong₂ _+_ (cong₂ _*_ (outW-elimGᵉ j vs sl x cl e) (pmI-elimGᵉ j vs sl k x cl e))
              (cong₂ _*_ (pmO-elimGᵉ j vs sl k x cl e) (innW-elimGᵉ j vs sl x cl e))
  pmO-elimGᵉ j vs sl k x cl (exhaustAllᵉ e)   =
    cong₂ _+_ (cong₂ _*_ (outW-elimGᵉ j vs sl x cl e) (pmI-elimGᵉ j vs sl k x cl e))
              (cong₂ _*_ (pmO-elimGᵉ j vs sl k x cl e) (innW-elimGᵉ j vs sl x cl e))
  pmO-elimGᵉ j vs sl k x cl (μᵉ e)            = pmO-elimGᵉ j vs sl k (there x) cl e
  pmO-elimGᵉ j vs sl k x cl (varᵉ y)          = refl
  pmO-elimGᵉ j vs sl k x cl (deferᵉ e)        = refl

  pmI-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (k : ℕ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (e : Exp Γ Δᵍ Δ Θ u) →
    pmIⱽ j vs sl k (elimGExp x cl e) ≡ pmIⱽ j vs sl k e
  pmI-elimGᵉ j vs sl k x cl (input i)         = refl
  pmI-elimGᵉ j vs sl k x cl (ofᵉ ts)          = pmI-elimGᵗˢ j vs sl k x cl ts
  pmI-elimGᵉ j vs sl k x cl emptyᵉ            = refl
  pmI-elimGᵉ j vs sl k x cl (mapᵉ f e)        =
    cong₂ _+_ (pmI-elimGᵗ j vs sl (suc k) x cl f)
              (cong₂ _*_ (cong₂ _⊔_ (pmI-elimGᵗ j vs sl 0 x cl f) refl)
                         (pmI-elimGᵉ j vs sl k x cl e))
  pmI-elimGᵉ j vs sl k x cl (takeᵉ c e)       = pmI-elimGᵉ j vs sl k x cl e
  pmI-elimGᵉ j vs sl k x cl (scanᵉ f z e)     =
    cong₂ _*_ (cong₂ _^_ (cong₂ _⊔_ (pmI-elimGᵗ j vs sl 0 x cl f) refl)
                         (outW-elimGᵉ j vs sl x cl e))
              (cong₂ _+_ (cong₂ _+_ (pmI-elimGᵗ j vs sl (suc k) x cl f)
                                    (pmI-elimGᵗ j vs sl k x cl z))
                         (pmI-elimGᵉ j vs sl k x cl e))
  pmI-elimGᵉ j vs sl k x cl (mergeAllᵉ lim e) = pmI-elimGᵉ j vs sl k x cl e
  pmI-elimGᵉ j vs sl k x cl (switchAllᵉ e)    = pmI-elimGᵉ j vs sl k x cl e
  pmI-elimGᵉ j vs sl k x cl (exhaustAllᵉ e)   = pmI-elimGᵉ j vs sl k x cl e
  pmI-elimGᵉ j vs sl k x cl (μᵉ e)            = pmI-elimGᵉ j vs sl k (there x) cl e
  pmI-elimGᵉ j vs sl k x cl (varᵉ y)          = refl
  pmI-elimGᵉ j vs sl k x cl (deferᵉ e)        = refl

  pmI-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (k : ℕ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (f : Tm Γ Δᵍ Δ Θ u) →
    pmIᵗⱽ j vs sl k (elimGTm x cl f) ≡ pmIᵗⱽ j vs sl k f
  pmI-elimGᵗ j vs sl k x cl (varᵗ y)      = refl
  pmI-elimGᵗ j vs sl k x cl unit̂          = refl
  pmI-elimGᵗ j vs sl k x cl (bool̂ b)      = refl
  pmI-elimGᵗ j vs sl k x cl (nat̂ m)       = refl
  pmI-elimGᵗ j vs sl k x cl (pairᵗ a b)   =
    cong₂ _⊔_ (pmI-elimGᵗ j vs sl k x cl a) (pmI-elimGᵗ j vs sl k x cl b)
  pmI-elimGᵗ j vs sl k x cl (fstᵗ p)      = pmI-elimGᵗ j vs sl k x cl p
  pmI-elimGᵗ j vs sl k x cl (sndᵗ p)      = pmI-elimGᵗ j vs sl k x cl p
  pmI-elimGᵗ j vs sl k x cl (inlᵗ a)      = pmI-elimGᵗ j vs sl k x cl a
  pmI-elimGᵗ j vs sl k x cl (inrᵗ a)      = pmI-elimGᵗ j vs sl k x cl a
  pmI-elimGᵗ j vs sl k x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (pmI-elimGᵗ j vs sl (suc k) x cl l)
                         (pmI-elimGᵗ j vs sl (suc k) x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pmI-elimGᵗ j vs sl 0 x cl l)
                                               (pmI-elimGᵗ j vs sl 0 x cl r))
                                    refl)
                         (pmI-elimGᵗ j vs sl k x cl s))
  pmI-elimGᵗ j vs sl k x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (pmI-elimGᵗ j vs sl k x cl a) (pmI-elimGᵗ j vs sl k x cl b)
  pmI-elimGᵗ j vs sl k x cl (primᵗ op a)  = refl
  pmI-elimGᵗ j vs sl k x cl (strmᵗ e)     = pmO-elimGᵉ j vs sl k x cl e

  pmI-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (k : ℕ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    pmIᵗˢⱽ j vs sl k (elimGTms x cl ts) ≡ pmIᵗˢⱽ j vs sl k ts
  pmI-elimGᵗˢ j vs sl k x cl []       = refl
  pmI-elimGᵗˢ j vs sl k x cl (y ∷ ys) =
    cong₂ _⊔_ (pmI-elimGᵗ j vs sl k x cl y) (pmI-elimGᵗˢ j vs sl k x cl ys)

  outW-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (e : Exp Γ Δᵍ Δ Θ u) →
    outWⱽ j vs sl (elimGExp x cl e) ≡ outWⱽ j vs sl e
  outW-elimGᵉ zero vs sl x cl (input i)         = refl
  outW-elimGᵉ zero vs sl x cl (ofᵉ ts)          = len-elimGTms x cl ts
  outW-elimGᵉ zero vs sl x cl emptyᵉ            = refl
  outW-elimGᵉ zero vs sl x cl (mapᵉ f e)        = outW-elimGᵉ zero vs sl x cl e
  outW-elimGᵉ zero vs sl x cl (takeᵉ c e)       = outW-elimGᵉ zero vs sl x cl e
  outW-elimGᵉ zero vs sl x cl (scanᵉ f z e)     = outW-elimGᵉ zero vs sl x cl e
  outW-elimGᵉ zero vs sl x cl (mergeAllᵉ lim e) =
    cong₂ _*_ (outW-elimGᵉ zero vs sl x cl e) (innW-elimGᵉ zero vs sl x cl e)
  outW-elimGᵉ zero vs sl x cl (switchAllᵉ e)    =
    cong₂ _*_ (outW-elimGᵉ zero vs sl x cl e) (innW-elimGᵉ zero vs sl x cl e)
  outW-elimGᵉ zero vs sl x cl (exhaustAllᵉ e)   =
    cong₂ _*_ (outW-elimGᵉ zero vs sl x cl e) (innW-elimGᵉ zero vs sl x cl e)
  outW-elimGᵉ zero vs sl x cl (μᵉ e)            = outW-elimGᵉ zero vs sl (there x) cl e
  outW-elimGᵉ zero vs sl x cl (varᵉ y)          = refl
  outW-elimGᵉ zero vs sl x cl (deferᵉ e)        = refl
  -- THE ONE CLAUSE THAT DOES NOT REDUCE ON ITS OWN.  A slot head is a
  -- three-way split -- fuel, revisit, slot -- so the measure is STUCK
  -- while those are variables, and the substitution the equation is
  -- about passes straight through a slot reference without touching
  -- it.  Abstracting the two decisions is what makes both readings the
  -- same term.
  outW-elimGᵉ (suc j) vs sl x cl (input i)         with i ∈ᵇ vs
  ... | true  = refl
  ... | false with sl i
  ...   | scripted _ = refl
  ...   | shared d   = refl
  outW-elimGᵉ (suc j) vs sl x cl (ofᵉ ts)          = len-elimGTms x cl ts
  outW-elimGᵉ (suc j) vs sl x cl emptyᵉ            = refl
  outW-elimGᵉ (suc j) vs sl x cl (mapᵉ f e)        = outW-elimGᵉ (suc j) vs sl x cl e
  outW-elimGᵉ (suc j) vs sl x cl (takeᵉ c e)       = outW-elimGᵉ (suc j) vs sl x cl e
  outW-elimGᵉ (suc j) vs sl x cl (scanᵉ f z e)     = outW-elimGᵉ (suc j) vs sl x cl e
  outW-elimGᵉ (suc j) vs sl x cl (mergeAllᵉ lim e) =
    cong₂ _*_ (outW-elimGᵉ (suc j) vs sl x cl e) (innW-elimGᵉ (suc j) vs sl x cl e)
  outW-elimGᵉ (suc j) vs sl x cl (switchAllᵉ e)    =
    cong₂ _*_ (outW-elimGᵉ (suc j) vs sl x cl e) (innW-elimGᵉ (suc j) vs sl x cl e)
  outW-elimGᵉ (suc j) vs sl x cl (exhaustAllᵉ e)   =
    cong₂ _*_ (outW-elimGᵉ (suc j) vs sl x cl e) (innW-elimGᵉ (suc j) vs sl x cl e)
  outW-elimGᵉ (suc j) vs sl x cl (μᵉ e)            = outW-elimGᵉ (suc j) vs sl (there x) cl e
  outW-elimGᵉ (suc j) vs sl x cl (varᵉ y)          = refl
  outW-elimGᵉ (suc j) vs sl x cl (deferᵉ e)        = refl

  innW-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (e : Exp Γ Δᵍ Δ Θ u) →
    innWⱽ j vs sl (elimGExp x cl e) ≡ innWⱽ j vs sl e
  innW-elimGᵉ zero vs sl x cl (input i)         = refl
  innW-elimGᵉ zero vs sl x cl (ofᵉ ts)          = innW-elimGᵗˢ zero vs sl x cl ts
  innW-elimGᵉ zero vs sl x cl emptyᵉ            = refl
  innW-elimGᵉ zero vs sl x cl (mapᵉ f e)        =
    cong₂ _+_ (innW-elimGᵗ zero vs sl x cl f)
              (cong₂ _*_ (cong₂ _⊔_ (pmI-elimGᵗ zero vs sl 0 x cl f) refl)
                         (innW-elimGᵉ zero vs sl x cl e))
  innW-elimGᵉ zero vs sl x cl (takeᵉ c e)       = innW-elimGᵉ zero vs sl x cl e
  innW-elimGᵉ zero vs sl x cl (scanᵉ f z e)     =
    cong₂ _*_ (cong₂ _^_ (cong₂ _⊔_ (pmI-elimGᵗ zero vs sl 0 x cl f) refl)
                         (outW-elimGᵉ zero vs sl x cl e))
              (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (innW-elimGᵗ zero vs sl x cl f)
                                               (innW-elimGᵗ zero vs sl x cl z))
                                    (innW-elimGᵉ zero vs sl x cl e))
                         refl)
  innW-elimGᵉ zero vs sl x cl (mergeAllᵉ lim e) = innW-elimGᵉ zero vs sl x cl e
  innW-elimGᵉ zero vs sl x cl (switchAllᵉ e)    = innW-elimGᵉ zero vs sl x cl e
  innW-elimGᵉ zero vs sl x cl (exhaustAllᵉ e)   = innW-elimGᵉ zero vs sl x cl e
  innW-elimGᵉ zero vs sl x cl (μᵉ e)            = innW-elimGᵉ zero vs sl (there x) cl e
  innW-elimGᵉ zero vs sl x cl (varᵉ y)          = refl
  innW-elimGᵉ zero vs sl x cl (deferᵉ e)        = refl
  -- THE ONE CLAUSE THAT DOES NOT REDUCE ON ITS OWN.  A slot head is a
  -- three-way split -- fuel, revisit, slot -- so the measure is STUCK
  -- while those are variables, and the substitution the equation is
  -- about passes straight through a slot reference without touching
  -- it.  Abstracting the two decisions is what makes both readings the
  -- same term.
  innW-elimGᵉ (suc j) vs sl x cl (input i)         with i ∈ᵇ vs
  ... | true  = refl
  ... | false with sl i
  ...   | scripted _ = refl
  ...   | shared d   = refl
  innW-elimGᵉ (suc j) vs sl x cl (ofᵉ ts)          = innW-elimGᵗˢ (suc j) vs sl x cl ts
  innW-elimGᵉ (suc j) vs sl x cl emptyᵉ            = refl
  innW-elimGᵉ (suc j) vs sl x cl (mapᵉ f e)        =
    cong₂ _+_ (innW-elimGᵗ (suc j) vs sl x cl f)
              (cong₂ _*_ (cong₂ _⊔_ (pmI-elimGᵗ (suc j) vs sl 0 x cl f) refl)
                         (innW-elimGᵉ (suc j) vs sl x cl e))
  innW-elimGᵉ (suc j) vs sl x cl (takeᵉ c e)       = innW-elimGᵉ (suc j) vs sl x cl e
  innW-elimGᵉ (suc j) vs sl x cl (scanᵉ f z e)     =
    cong₂ _*_ (cong₂ _^_ (cong₂ _⊔_ (pmI-elimGᵗ (suc j) vs sl 0 x cl f) refl)
                         (outW-elimGᵉ (suc j) vs sl x cl e))
              (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (innW-elimGᵗ (suc j) vs sl x cl f)
                                               (innW-elimGᵗ (suc j) vs sl x cl z))
                                    (innW-elimGᵉ (suc j) vs sl x cl e))
                         refl)
  innW-elimGᵉ (suc j) vs sl x cl (mergeAllᵉ lim e) = innW-elimGᵉ (suc j) vs sl x cl e
  innW-elimGᵉ (suc j) vs sl x cl (switchAllᵉ e)    = innW-elimGᵉ (suc j) vs sl x cl e
  innW-elimGᵉ (suc j) vs sl x cl (exhaustAllᵉ e)   = innW-elimGᵉ (suc j) vs sl x cl e
  innW-elimGᵉ (suc j) vs sl x cl (μᵉ e)            = innW-elimGᵉ (suc j) vs sl (there x) cl e
  innW-elimGᵉ (suc j) vs sl x cl (varᵉ y)          = refl
  innW-elimGᵉ (suc j) vs sl x cl (deferᵉ e)        = refl

  innW-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (f : Tm Γ Δᵍ Δ Θ u) →
    innWᵗⱽ j vs sl (elimGTm x cl f) ≡ innWᵗⱽ j vs sl f
  innW-elimGᵗ j vs sl x cl (varᵗ y)      = refl
  innW-elimGᵗ j vs sl x cl unit̂          = refl
  innW-elimGᵗ j vs sl x cl (bool̂ b)      = refl
  innW-elimGᵗ j vs sl x cl (nat̂ m)       = refl
  innW-elimGᵗ j vs sl x cl (pairᵗ a b)   =
    cong₂ _⊔_ (innW-elimGᵗ j vs sl x cl a) (innW-elimGᵗ j vs sl x cl b)
  innW-elimGᵗ j vs sl x cl (fstᵗ p)      = innW-elimGᵗ j vs sl x cl p
  innW-elimGᵗ j vs sl x cl (sndᵗ p)      = innW-elimGᵗ j vs sl x cl p
  innW-elimGᵗ j vs sl x cl (inlᵗ a)      = innW-elimGᵗ j vs sl x cl a
  innW-elimGᵗ j vs sl x cl (inrᵗ a)      = innW-elimGᵗ j vs sl x cl a
  innW-elimGᵗ j vs sl x cl (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (innW-elimGᵗ j vs sl x cl l) (innW-elimGᵗ j vs sl x cl r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_ (pmI-elimGᵗ j vs sl 0 x cl l)
                                               (pmI-elimGᵗ j vs sl 0 x cl r))
                                    refl)
                         (innW-elimGᵗ j vs sl x cl s))
  innW-elimGᵗ j vs sl x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (innW-elimGᵗ j vs sl x cl a) (innW-elimGᵗ j vs sl x cl b)
  innW-elimGᵗ j vs sl x cl (primᵗ op a)  = refl
  innW-elimGᵗ j vs sl x cl (strmᵗ e)     = outW-elimGᵉ j vs sl x cl e

  innW-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (vs : List (Fin n))
    (sl : Slots Γ) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    innWᵗˢⱽ j vs sl (elimGTms x cl ts) ≡ innWᵗˢⱽ j vs sl ts
  innW-elimGᵗˢ j vs sl x cl []       = refl
  innW-elimGᵗˢ j vs sl x cl (y ∷ ys) =
    cong₂ _⊔_ (innW-elimGᵗ j vs sl x cl y) (innW-elimGᵗˢ j vs sl x cl ys)

------------------------------------------------------------------
-- AND THE BURST CEILING WITH THEM.  Its own reading is `outWⱽ` and its
-- children are the same constructors, so the equality lifts clause for
-- clause -- and the two clauses where an unfolding could have shown
-- through are the two this ceiling already reads as zero.
------------------------------------------------------------------
mutual
  bCeil-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (sl : Slots Γ)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (e : Exp Γ Δᵍ Δ Θ u) →
    bCeilᵉ j sl (elimGExp x cl e) ≡ bCeilᵉ j sl e
  bCeil-elimGᵉ j sl x cl e =
    cong₂ _⊔_ (outW-elimGᵉ j [] sl x cl e) (bKids-elimGᵉ j sl x cl e)

  bKids-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (j : ℕ) (sl : Slots Γ)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (e : Exp Γ Δᵍ Δ Θ u) →
    bKidsᵉ j sl (elimGExp x cl e) ≡ bKidsᵉ j sl e
  bKids-elimGᵉ j sl x cl (input i)         = refl
  bKids-elimGᵉ j sl x cl (ofᵉ ts)          = refl
  bKids-elimGᵉ j sl x cl emptyᵉ            = refl
  bKids-elimGᵉ j sl x cl (mapᵉ f e)        = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (takeᵉ c e)       = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (scanᵉ f z e)     = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (mergeAllᵉ lim e) = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (switchAllᵉ e)    = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (exhaustAllᵉ e)   = bCeil-elimGᵉ j sl x cl e
  bKids-elimGᵉ j sl x cl (μᵉ e)            = bCeil-elimGᵉ j sl (there x) cl e
  bKids-elimGᵉ j sl x cl (varᵉ y)          = refl
  bKids-elimGᵉ j sl x cl (deferᵉ e)        = refl

-- A μ HEAD READS ITS OWN BODY TWICE, once as the node's own payload
-- count and once as its only child, so the equation is idempotence and
-- not reduction.
outW-mu : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (vs : List (Fin n))
  (sl : Slots Γ) (b : Exp Γ (t ∷ Δᵍ) Δ Θ t) →
  outWⱽ j vs sl (μᵉ b) ≡ outWⱽ j vs sl b
outW-mu zero    vs sl b = refl
outW-mu (suc j) vs sl b = refl

bCeil-mu : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (j : ℕ) (sl : Slots Γ)
  (b : Exp Γ (t ∷ Δᵍ) Δ Θ t) → bCeilᵉ j sl (μᵉ b) ≡ bCeilᵉ j sl b
bCeil-mu j sl b =
  trans (cong (_⊔ bCeilᵉ j sl b) (outW-mu j [] sl b))
        (trans (sym (⊔-assoc (outWⱽ j [] sl b) (outWⱽ j [] sl b) (bKidsᵉ j sl b)))
               (cong (_⊔ bKidsᵉ j sl b) (⊔-idem (outWⱽ j [] sl b))))

-- THE EDGE THE DESCENT'S μ CLAUSE SPENDS, and it is an equality rather
-- than a bound -- there is no slack to lose and none to find.
bCeil-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (j : ℕ) (sl : Slots Γ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  bCeilᵉ j sl (unfoldμ body) ≡ bCeilᵉ j sl (μᵉ body)
bCeil-unfoldμ j sl body =
  trans (bCeil-elimGᵉ j sl (here refl) (μᵉ body) body)
        (sym (bCeil-mu j sl body))
