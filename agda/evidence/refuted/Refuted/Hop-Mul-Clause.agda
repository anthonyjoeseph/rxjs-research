-- ══════════════════════════════════════════════════════════════════
-- THE MULTIPLIER IN hopD's mapᵉ CLAUSE CANNOT BE DELETED.
--
-- `hopDᵉ V η (mapᵉ f e) = hopDᵗ V η f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ V η e`
-- and the question this file answers is whether the `(… ⊔ 1) *` is
-- load-bearing or decoration — whether the clause could read
-- `hopDᵗ V η f + hopDᵉ V η e` and the measure survive.
--
-- IT IS LOAD-BEARING, and the witness is one map over a one-value
-- source.  `ahopD` below is hopD with every multiplier deleted and
-- nothing else changed.  The template `dup` mentions its bound
-- variable TWICE, in the two positions the mapᵉ clause ADDS — once as
-- an inner map's template and once inside that map's source — so the
-- source's depth lands twice while the additive clause charges for it
-- once.  Measured on a source of depth 1: the map's own additive
-- reading is 1 and its first emission reads 2.
--
-- The multiplicative clause prices the same program at 2 and the same
-- emission at 2, which is what a multiplier is FOR: it is the slope of
-- hopD in a substituted value's depth, and a template whose bound
-- variable reaches two added positions has slope 2.
--
-- THIS IS NOT `mul-exceeds` (Rx.Hop-Depth's header, the witness that
-- refutes the per-binder COUNT `occs0ᵗ`).  That one is internal to a
-- design in which mapᵉ already multiplies: it says a count cannot see
-- an INNER map's factor.  Delete the multiplication and there is no
-- inner factor to be blind to, so mul-exceeds says nothing about the
-- additive clause.  This file is the witness that was missing — the
-- header's "a first draft used a bare `+` and did not survive a nested
-- map", restated as numbers.
--
-- WHAT IT LEAVES OPEN, deliberately: the multiplier being necessary
-- does not pin the SLOPE to `pmᵗ`.  Once the clause multiplies, pm's
-- own recursion is forced to multiply with it (the slope of
-- `hopDᵗ f + c(f) * hopDᵉ e` in a plug at index k is
-- `pmᵗ (suc k) f + c(f) * pmᵉ k e`), which is exactly pm's mapᵉ clause
-- — so the two stand or fall together, and this witness kills both
-- additive readings at once.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Hop-Mul-Clause where

open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []) renaming (_∷_ to _∷ᵛ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using
  (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
   Ctx; Exp; Tm; Val; Closed; Fn; applyFn;
   input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
   mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
   varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
   inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵛ)

------------------------------------------------------------------
-- hopD WITH EVERY MULTIPLIER DELETED.  Clause for clause the same
-- function, except that `mapᵉ`, `caseᵗ` and `scanᵉ` add where hopD
-- multiplies.  V drops out entirely — it was only ever the scan
-- clause's exponent — which is the shape of the saving the additive
-- reading would have bought.
------------------------------------------------------------------

mutual
  ahopDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) →
           Exp Γ Δᵍ Δ Θ t → ℕ
  ahopDᵉ η (input i)          = η i
  ahopDᵉ η (ofᵉ ts)           = ahopDᵗˢ η ts
  ahopDᵉ η emptyᵉ             = 0
  ahopDᵉ η (mapᵉ f e)         = ahopDᵗ η f + ahopDᵉ η e
  ahopDᵉ η (takeᵉ c e)        = ahopDᵉ η e
  ahopDᵉ η (scanᵉ f z e)      = ahopDᵗ η f + ahopDᵗ η z + ahopDᵉ η e
  ahopDᵉ η (mergeAllᵉ lim e)  = suc (ahopDᵉ η e)
  ahopDᵉ η (switchAllᵉ e)     = suc (ahopDᵉ η e)
  ahopDᵉ η (exhaustAllᵉ e)    = suc (ahopDᵉ η e)
  ahopDᵉ η (μᵉ e)             = ahopDᵉ η e
  ahopDᵉ η (varᵉ x)           = 0
  ahopDᵉ η (deferᵉ e)         = 0

  ahopDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) →
           Tm Γ Δᵍ Δ Θ t → ℕ
  ahopDᵗ η (varᵗ x)      = 0
  ahopDᵗ η unit̂          = 0
  ahopDᵗ η (bool̂ _)      = 0
  ahopDᵗ η (nat̂ _)       = 0
  ahopDᵗ η (pairᵗ a b)   = ahopDᵗ η a ⊔ ahopDᵗ η b
  ahopDᵗ η (fstᵗ p)      = ahopDᵗ η p
  ahopDᵗ η (sndᵗ p)      = ahopDᵗ η p
  ahopDᵗ η (inlᵗ a)      = ahopDᵗ η a
  ahopDᵗ η (inrᵗ a)      = ahopDᵗ η a
  ahopDᵗ η (caseᵗ s l r) = (ahopDᵗ η l ⊔ ahopDᵗ η r) + ahopDᵗ η s
  ahopDᵗ η (ifᵗ c a b)   = ahopDᵗ η a ⊔ ahopDᵗ η b
  ahopDᵗ η (primᵗ _ a)   = 0
  ahopDᵗ η (strmᵗ e)     = ahopDᵉ η e

  ahopDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) →
            List (Tm Γ Δᵍ Δ Θ t) → ℕ
  ahopDᵗˢ η []       = 0
  ahopDᵗˢ η (y ∷ ys) = ahopDᵗ η y ⊔ ahopDᵗˢ η ys

ahopDᵛ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (t : Ty) → Val Γ t → ℕ
ahopDᵛ η unitᵗ    _        = 0
ahopDᵛ η boolᵗ    _        = 0
ahopDᵛ η natᵗ     _        = 0
ahopDᵛ η (s ×ᵗ t) (a , b)  = ahopDᵛ η s a ⊔ ahopDᵛ η t b
ahopDᵛ η (s +ᵗ t) (inj₁ a) = ahopDᵛ η s a
ahopDᵛ η (s +ᵗ t) (inj₂ b) = ahopDᵛ η t b
ahopDᵛ η (obs t)  e        = ahopDᵉ η e

------------------------------------------------------------------
-- THE WITNESS.  No slots, so η is empty and neither measure can be
-- reading anything off the environment.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []

η₀ : Fin 0 → ℕ
η₀ ()

V₀ : ℕ
V₀ = 8

-- an observable of depth one: a mergeAll over a single inner
carrier : Closed Γ₀ natᵗ
carrier = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- the source emits exactly `carrier`, so the map's source has depth one
src : Closed Γ₀ (obs natᵗ)
src = ofᵉ (strmᵗ carrier ∷ [])

-- THE TEMPLATE.  Its bound variable (index 0, type `obs natᵗ`) occurs
-- twice: as the inner map's template, and inside the inner map's
-- source.  Those are the two positions hopD's mapᵉ clause ADDS.
dup : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dup = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

prog : Closed Γ₀ (obs (obs natᵗ))
prog = mapᵉ dup src

emitted : Val Γ₀ (obs (obs natᵗ))
emitted = applyFn dup carrier

------------------------------------------------------------------
-- THE FIGURES, every one of them by refl.
------------------------------------------------------------------

src-depth : ahopDᵉ η₀ src ≡ 1
src-depth = refl

-- the additive clause charges the source's depth once
add-prog : ahopDᵉ η₀ prog ≡ 1
add-prog = refl

-- and the very first emission reads twice that
add-emitted : ahopDᵛ η₀ (obs (obs natᵗ)) emitted ≡ 2
add-emitted = refl

-- the multiplicative clause charges it twice, which is what the
-- emission costs
mul-prog : hopDᵉ V₀ η₀ prog ≡ 2
mul-prog = refl

mul-emitted : hopDᵛ V₀ η₀ (obs (obs natᵗ)) emitted ≡ 2
mul-emitted = refl

------------------------------------------------------------------
-- THE REFUTATION.  Anything claiming the multiplier-free clause
-- dominates a map's own one-step image is inhabited only by ⊥.
------------------------------------------------------------------

AdditiveClauseDominates : Set
AdditiveClauseDominates =
  ∀ {n} {Γ : Ctx n} {s t} (η : Fin n → ℕ)
    (f : Fn Γ [] [] [] s t) (e : Closed Γ s) (v : Val Γ s) →
    ahopDᵛ η s v ≤ ahopDᵉ η e →
    ahopDᵛ η t (applyFn f v) ≤ ahopDᵉ η (mapᵉ f e)

hop-mul-clause-absurd : AdditiveClauseDominates → ⊥
hop-mul-clause-absurd dom =
  <-irrefl refl (dom η₀ dup src carrier (s≤s z≤n))
