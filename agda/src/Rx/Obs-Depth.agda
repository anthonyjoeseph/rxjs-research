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
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  elimGExp; elimGTm; elimGTms; unfoldμ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)

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

------------------------------------------------------------------
-- SUBSTITUTING FOR A GUARDED VARIABLE LEAVES THE MEASURE ALONE, which
-- is what the μ peel re-establishes its conjunct with.  The content is
-- the `deferᵉ` clause and nothing else: a guarded occurrence sits under
-- a `deferᵉ`, the measure cuts a `deferᵉ` to zero, so the substituted
-- term is never read at all and every other clause is a congruence.
--
-- AND THE GUARD IS WHAT MAKES IT TRUE RATHER THAN A CONVENIENCE.  An
-- UNGUARDED self-reference under a `strmᵗ` would grow the measure by a
-- whole nesting per unfolding and nothing would bound it — `μ z. of
-- (strm z)` is the shape, and it is exactly the program that flattens
-- forever.  The syntax does not admit it: a recursion variable is
-- reachable only through the clause the measure zeroes.
------------------------------------------------------------------

mutual
  obsDepth-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    obsDepthᵉ (elimGExp x cl b) ≡ obsDepthᵉ b
  obsDepth-elimGᵉ x cl (input i)         = refl
  obsDepth-elimGᵉ x cl (ofᵉ ts)          = obsDepth-elimGᵗˢ x cl ts
  obsDepth-elimGᵉ x cl emptyᵉ            = refl
  obsDepth-elimGᵉ x cl (mapᵉ f b)        =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl f) (obsDepth-elimGᵉ x cl b)
  obsDepth-elimGᵉ x cl (takeᵉ c b)       =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl c) (obsDepth-elimGᵉ x cl b)
  obsDepth-elimGᵉ x cl (scanᵉ f z b)     =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl f) (obsDepth-elimGᵗ x cl z))
              (obsDepth-elimGᵉ x cl b)
  obsDepth-elimGᵉ x cl (mergeAllᵉ lim b) = obsDepth-elimGᵉ x cl b
  obsDepth-elimGᵉ x cl (switchAllᵉ b)    = obsDepth-elimGᵉ x cl b
  obsDepth-elimGᵉ x cl (exhaustAllᵉ b)   = obsDepth-elimGᵉ x cl b
  obsDepth-elimGᵉ x cl (μᵉ b)            = obsDepth-elimGᵉ (there x) cl b
  obsDepth-elimGᵉ x cl (varᵉ y)          = refl
  obsDepth-elimGᵉ x cl (deferᵉ b)        = refl

  obsDepth-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (c : Tm Γ Δᵍ Δ Θ u) →
    obsDepthᵗ (elimGTm x cl c) ≡ obsDepthᵗ c
  obsDepth-elimGᵗ x cl (varᵗ y)      = refl
  obsDepth-elimGᵗ x cl unit̂          = refl
  obsDepth-elimGᵗ x cl (bool̂ _)      = refl
  obsDepth-elimGᵗ x cl (nat̂ _)       = refl
  obsDepth-elimGᵗ x cl (pairᵗ a b)   =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl a) (obsDepth-elimGᵗ x cl b)
  obsDepth-elimGᵗ x cl (fstᵗ p)      = obsDepth-elimGᵗ x cl p
  obsDepth-elimGᵗ x cl (sndᵗ p)      = obsDepth-elimGᵗ x cl p
  obsDepth-elimGᵗ x cl (inlᵗ a)      = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (inrᵗ a)      = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (caseᵗ s l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl s) (obsDepth-elimGᵗ x cl l))
              (obsDepth-elimGᵗ x cl r)
  obsDepth-elimGᵗ x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-elimGᵗ x cl c) (obsDepth-elimGᵗ x cl a))
              (obsDepth-elimGᵗ x cl b)
  obsDepth-elimGᵗ x cl (primᵗ _ a)   = obsDepth-elimGᵗ x cl a
  obsDepth-elimGᵗ x cl (strmᵗ b)     = cong suc (obsDepth-elimGᵉ x cl b)

  obsDepth-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    obsDepthᵗˢ (elimGTms x cl ts) ≡ obsDepthᵗˢ ts
  obsDepth-elimGᵗˢ x cl []       = refl
  obsDepth-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _⊔_ (obsDepth-elimGᵗ x cl y) (obsDepth-elimGᵗˢ x cl ys)

-- THE μ PEEL'S CONJUNCT, and it is the one edge of the three the
-- measure has to say anything about at all: the unfolding is read
-- exactly where the redex is, so the component is re-established by
-- reflexivity and nothing is spent.
obsDepth-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  obsDepthᵉ (unfoldμ body) ≡ obsDepthᵉ (μᵉ body)
obsDepth-unfoldμ body = obsDepth-elimGᵉ (here refl) (μᵉ body) body
