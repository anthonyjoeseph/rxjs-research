------------------------------------------------------------------
-- THE HOP PEEL'S MEASURE, AND IT CONSULTS NOTHING BUT THE SYNTAX.
-- `strmᵗ` is the only head that writes an observable, so the nesting of
-- those heads is a quantity the PROGRAM carries; every other clause
-- joins.  That is the whole difference from the reading this replaces:
-- a reading prices what a subtree will EMIT, which multiplies as a
-- flattener re-wraps, while this counts how deep observables are
-- WRITTEN, which a run can only walk down.
--
-- AND IT TAKES NO SLOT ENVIRONMENT, WHICH IS THE POINT RATHER THAN A
-- CONVENIENCE.  The rank the evaluator descends on stops being a
-- function of the schedule, so a step that changes the slot telescope
-- cannot change what the descent is standing at, and the peel's
-- obligation stops mentioning the machine at all.
--
-- THE ONE PLACE THAT COSTS SOMETHING IS THE CONNECT, AND THE EDGE PAYS
-- IT.  A reference reads ZERO here while the definition it stands for
-- may be written arbitrarily deep, so a connect keeping the rank it
-- entered at would owe exactly the staged fixpoint the reading needs an
-- environment for.  It keeps nothing: the connect edge descends the
-- unconnected count and leaves the rank free, so the definition is
-- entered at its OWN nesting and the obligation is reflexivity.  That
-- is why the environment can go, and it is the only reason.
--
-- TWO CLAUSES CUT TO ZERO AND BOTH ARE THE SAME FACT ABOUT THE
-- SCHEDULE.  A `deferᵉ` body and a recursion variable are subscribed
-- from an ARRIVAL rather than from inside a burst, so neither is
-- reachable by the peel this measure bounds, and counting them would
-- price hops that happen at another instant.  What an arrival owes
-- instead is a seed of its own, which is what the entry's third
-- argument is for.
------------------------------------------------------------------
module Rx.Obs-Depth where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Closed; Exp; Tm; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  elimGExp; elimGTm; elimGTms; unfoldμ)

mutual
  obsDepthᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  obsDepthᵉ (input i)          = 0
  obsDepthᵉ (ofᵉ ts)           = obsDepthᵗˢ ts
  obsDepthᵉ emptyᵉ             = 0
  obsDepthᵉ (mapᵉ f e)         = obsDepthᵗ f ⊔ obsDepthᵉ e
  obsDepthᵉ (takeᵉ c e)        = obsDepthᵗ c ⊔ obsDepthᵉ e
  obsDepthᵉ (scanᵉ f z e)      = obsDepthᵗ f ⊔ obsDepthᵗ z ⊔ obsDepthᵉ e
  obsDepthᵉ (mergeAllᵉ lim e)  = obsDepthᵉ e
  obsDepthᵉ (switchAllᵉ e)     = obsDepthᵉ e
  obsDepthᵉ (exhaustAllᵉ e)    = obsDepthᵉ e
  obsDepthᵉ (μᵉ e)             = obsDepthᵉ e
  obsDepthᵉ (varᵉ x)           = 0
  obsDepthᵉ (deferᵉ e)         = 0

  obsDepthᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  obsDepthᵗ (varᵗ x)      = 0
  obsDepthᵗ unit̂          = 0
  obsDepthᵗ (bool̂ _)      = 0
  obsDepthᵗ (nat̂ _)       = 0
  obsDepthᵗ (pairᵗ a b)   = obsDepthᵗ a ⊔ obsDepthᵗ b
  obsDepthᵗ (fstᵗ p)      = obsDepthᵗ p
  obsDepthᵗ (sndᵗ p)      = obsDepthᵗ p
  obsDepthᵗ (inlᵗ a)      = obsDepthᵗ a
  obsDepthᵗ (inrᵗ a)      = obsDepthᵗ a
  obsDepthᵗ (caseᵗ s l r) = obsDepthᵗ s ⊔ obsDepthᵗ l ⊔ obsDepthᵗ r
  obsDepthᵗ (ifᵗ c a b)   = obsDepthᵗ c ⊔ obsDepthᵗ a ⊔ obsDepthᵗ b
  obsDepthᵗ (primᵗ _ a)   = obsDepthᵗ a
  obsDepthᵗ (strmᵗ e)     = suc (obsDepthᵉ e)

  obsDepthᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  obsDepthᵗˢ []       = 0
  obsDepthᵗˢ (y ∷ ys) = obsDepthᵗ y ⊔ obsDepthᵗˢ ys

-- A VALUE'S OWN, mirroring the reading's value clauses so the two
-- currencies can be compared clause by clause where anything still has
-- to.  Only the observable type carries anything: at every other type a
-- value is data the run cannot subscribe.
obsDepthᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
obsDepthᵛ unitᵗ    _        = 0
obsDepthᵛ boolᵗ    _        = 0
obsDepthᵛ natᵗ     _        = 0
obsDepthᵛ (s ×ᵗ t) (a , b)  = obsDepthᵛ s a ⊔ obsDepthᵛ t b
obsDepthᵛ (s +ᵗ t) (inj₁ a) = obsDepthᵛ s a
obsDepthᵛ (s +ᵗ t) (inj₂ b) = obsDepthᵛ t b
obsDepthᵛ (obs t)  e        = obsDepthᵉ e

-- AND UNFOLDING A `μ` LEAVES THE READING WHERE IT WAS, WHICH IS WHAT
-- LETS THE PEEL KEEP THE RANK IT ENTERED AT.  The naive reading says
-- otherwise: unfolding substitutes the whole `μᵉ body` at every
-- occurrence, so a body writing its own recursive occurrence under a
-- `strmᵗ` would gain that term's nesting on top of its own.  What rules
-- it out is the TYPE and not the arithmetic — `μᵉ` binds into the
-- guarded context while `varᵉ` reads the usable one, so an occurrence is
-- reachable only past a `deferᵉ`, and this reading cuts a `deferᵉ` to
-- zero whatever sits beneath it.  The substitution therefore happens
-- only where the measure has already stopped looking.
--
-- TWIN: `Rx.Sync-Size.syncSize-elimG` — the same commutation for the
--   size, clause for clause, with the same defer argument under it.
--   That one drops by the constructor `μᵉ` adds; this one holds equal,
--   since the reading passes a `μᵉ` through unchanged.
mutual
  obsDepth-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    obsDepthᵉ (elimGExp x cl e) ≡ obsDepthᵉ e
  obsDepth-elimG x cl (input i)       = refl
  obsDepth-elimG x cl (ofᵉ ts)        = obsDepth-elimGᵗˢ x cl ts
  obsDepth-elimG x cl emptyᵉ          = refl
  obsDepth-elimG x cl (mapᵉ f e)      =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl f) (obsDepth-elimG x cl e)
  obsDepth-elimG x cl (takeᵉ c e)     =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl c) (obsDepth-elimG x cl e)
  obsDepth-elimG x cl (scanᵉ f z e)   =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl f)
                         (obsDepth-elimGᵗ x cl z))
              (obsDepth-elimG x cl e)
  obsDepth-elimG x cl (mergeAllᵉ _ e) = obsDepth-elimG x cl e
  obsDepth-elimG x cl (switchAllᵉ e)  = obsDepth-elimG x cl e
  obsDepth-elimG x cl (exhaustAllᵉ e) = obsDepth-elimG x cl e
  obsDepth-elimG x cl (μᵉ e)          = obsDepth-elimG (there x) cl e
  obsDepth-elimG x cl (varᵉ y)        = refl
  obsDepth-elimG x cl (deferᵉ e)      = refl

  obsDepth-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    obsDepthᵗ (elimGTm x cl f) ≡ obsDepthᵗ f
  obsDepth-elimGᵗ x cl (varᵗ y)      = refl
  obsDepth-elimGᵗ x cl unit̂          = refl
  obsDepth-elimGᵗ x cl (bool̂ b)      = refl
  obsDepth-elimGᵗ x cl (nat̂ k)       = refl
  obsDepth-elimGᵗ x cl (pairᵗ a b)   =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl a) (obsDepth-elimGᵗ x cl b)
  obsDepth-elimGᵗ x cl (fstᵗ p)      = obsDepth-elimGᵗ x cl p
  obsDepth-elimGᵗ x cl (sndᵗ p)      = obsDepth-elimGᵗ x cl p
  obsDepth-elimGᵗ x cl (inlᵗ a)      = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (inrᵗ a)      = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (caseᵗ s l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl s)
                         (obsDepth-elimGᵗ x cl l))
              (obsDepth-elimGᵗ x cl r)
  obsDepth-elimGᵗ x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl c)
                         (obsDepth-elimGᵗ x cl a))
              (obsDepth-elimGᵗ x cl b)
  obsDepth-elimGᵗ x cl (primᵗ op a)  = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (strmᵗ e)     = cong suc (obsDepth-elimG x cl e)

  obsDepth-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    obsDepthᵗˢ (elimGTms x cl ts) ≡ obsDepthᵗˢ ts
  obsDepth-elimGᵗˢ x cl []       = refl
  obsDepth-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl y) (obsDepth-elimGᵗˢ x cl ys)

-- THE FORM THE μ ARM ASKS FOR, WORD FOR WORD.  The peel steps the
-- descent on the SIZE and keeps the rank, so what re-establishes the
-- entry invariant at the unfolding is this — and it is an equality
-- rather than a drop, since `obsDepthᵉ` passes a `μᵉ` through unchanged.
obsDepth-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  obsDepthᵉ (unfoldμ body) ≡ obsDepthᵉ body
obsDepth-unfoldμ body = obsDepth-elimG (here refl) (μᵉ body) body

unfoldμ-no-deeper : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  obsDepthᵉ (unfoldμ body) ≤ obsDepthᵉ (μᵉ body)
unfoldμ-no-deeper body rewrite obsDepth-unfoldμ body = ≤-refl
