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
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

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
