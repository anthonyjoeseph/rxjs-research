------------------------------------------------------------------
-- THE HOP PEEL'S MEASURE, AND IT CONSULTS THE SYNTAX PLUS ONE READING
-- OF THE SLOTS.  `strmᵗ` is the only head that writes an observable, so
-- the nesting of those heads is a quantity the PROGRAM carries; every
-- clause that binds nothing joins.  That is the whole difference from
-- the reading this replaces: a reading prices what a subtree will EMIT,
-- which multiplies as a flattener re-wraps, while this counts how deep
-- observables are WRITTEN, which a run can only walk down.
--
-- ONE CLAUSE ADDS, AND IT IS THE ONLY HEAD OF THE TERM LANGUAGE THAT
-- MAKES ITS OWN ENVIRONMENT.  A `caseᵗ` evaluates its scrutinee and
-- BINDS what came out, so a branch that wraps its binder writes on top
-- of the scrutinee's nesting rather than beside it; a join over the
-- three subterms prices the two as alternatives when the run composes
-- them.  The `suc` is the `reify` the binding goes through, which
-- writes a `strmᵗ` the scrutinee's own reading has already peeled, and
-- it is OUTERMOST so that the strict drop the door is entered on
-- reduces at this head rather than blocking on a sum.  `ifᵗ` binds
-- nothing and still joins.
--
-- THE ENVIRONMENT IS WHAT A SLOT REFERENCE COSTS, AND IT IS FORCED.  A
-- reference is ONE SYMBOL standing for a definition of any nesting, so a
-- clause pricing it at nought prices a program by a symbol rather than
-- by what the connect will plumb out through it.  `η` is what the symbol
-- is worth, and `Rx.Slot-Depth` is where the only environment anyone
-- means gets built — the staged fixpoint that stratification makes
-- total.  Everything here is generic in it, so nothing in the measure
-- itself has to know that the number came from a telescope.
--
-- TWO CLAUSES CUT TO ZERO AND BOTH ARE THE SAME FACT ABOUT THE
-- SCHEDULE.  A `deferᵉ` body and a recursion variable are subscribed
-- from an ARRIVAL rather than from inside a burst, so neither is
-- reachable by the peel this measure bounds, and counting them would
-- price hops that happen at another instant.  What an arrival owes
-- instead is a seed of its own, which is what the entry's third
-- argument is for.
--
-- REFUTED: `Refuted.Case-Binds` — the JOIN this reading used to take
--   at the rebinding arm, at a scrutinee written three deep under a
--   branch that writes two.  It kills the reading itself and not merely
--   a statement over it, which is why the repair is a clause here and
--   not a premise anywhere above.
--
-- REFUTED: `Refuted.Carried-Derived` — the ZERO environment, read as
--   the entry invariant's rank at a fresh share whose definition writes
--   an observable.  That witness is why `η` is here at all, and why no
--   reading without one is stated here: the zero environment is now
--   apparatus of the trees that refute it, not a measure this one
--   offers.
------------------------------------------------------------------
module Rx.Obs-Depth where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Closed; Exp; Tm; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  elimGExp; elimGTm; elimGTms; unfoldμ)

mutual
  depᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  depᵉ η (input i)          = η i
  depᵉ η (ofᵉ ts)           = depᵗˢ η ts
  depᵉ η emptyᵉ             = 0
  depᵉ η (mapᵉ f e)         = depᵗ η f ⊔ depᵉ η e
  depᵉ η (takeᵉ c e)        = depᵗ η c ⊔ depᵉ η e
  depᵉ η (scanᵉ f z e)      = depᵗ η f ⊔ depᵗ η z ⊔ depᵉ η e
  depᵉ η (mergeAllᵉ lim e)  = depᵉ η e
  depᵉ η (switchAllᵉ e)     = depᵉ η e
  depᵉ η (exhaustAllᵉ e)    = depᵉ η e
  depᵉ η (μᵉ e)             = depᵉ η e
  depᵉ η (varᵉ x)           = 0
  depᵉ η (deferᵉ e)         = 0

  depᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  depᵗ η (varᵗ x)      = 0
  depᵗ η unit̂          = 0
  depᵗ η (bool̂ _)      = 0
  depᵗ η (nat̂ _)       = 0
  depᵗ η (pairᵗ a b)   = depᵗ η a ⊔ depᵗ η b
  depᵗ η (fstᵗ p)      = depᵗ η p
  depᵗ η (sndᵗ p)      = depᵗ η p
  depᵗ η (inlᵗ a)      = depᵗ η a
  depᵗ η (inrᵗ a)      = depᵗ η a
  depᵗ η (caseᵗ s l r) = suc (depᵗ η s + (depᵗ η l ⊔ depᵗ η r))
  depᵗ η (ifᵗ c a b)   = depᵗ η c ⊔ depᵗ η a ⊔ depᵗ η b
  depᵗ η (primᵗ _ a)   = depᵗ η a
  depᵗ η (strmᵗ e)     = suc (depᵉ η e)

  depᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  depᵗˢ η []       = 0
  depᵗˢ η (y ∷ ys) = depᵗ η y ⊔ depᵗˢ η ys

-- A VALUE'S OWN, mirroring the reading's value clauses so the two
-- currencies can be compared clause by clause where anything still has
-- to.  Only the observable type carries anything: at every other type a
-- value is data the run cannot subscribe.
depᵛ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (t : Ty) → Val Γ t → ℕ
depᵛ η unitᵗ    _        = 0
depᵛ η boolᵗ    _        = 0
depᵛ η natᵗ     _        = 0
depᵛ η (s ×ᵗ t) (a , b)  = depᵛ η s a ⊔ depᵛ η t b
depᵛ η (s +ᵗ t) (inj₁ a) = depᵛ η s a
depᵛ η (s +ᵗ t) (inj₂ b) = depᵛ η t b
depᵛ η (obs t)  e        = depᵉ η e

-- AND UNFOLDING A `μ` LEAVES THE READING WHERE IT WAS, WHICH IS WHAT
-- LETS THE PEEL KEEP THE RANK IT ENTERED AT.  The naive reading says
-- otherwise: unfolding substitutes the whole `μᵉ body` at every
-- occurrence, so a body writing its own recursive occurrence under a
-- `strmᵗ` would gain that term's nesting on top of its own.  What rules
-- it out is the TYPE and not the arithmetic — `μᵉ` binds into the
-- guarded context while `varᵉ` reads the usable one, so an occurrence is
-- reachable only past a `deferᵉ`, and this reading cuts a `deferᵉ` to
-- zero whatever sits beneath it.  The substitution therefore happens
-- only where the measure has already stopped looking.  The environment
-- passes through untouched for the same reason the syntax does: no
-- clause here rebinds an input.
--
-- TWIN: `Rx.Sync-Size.syncSize-elimG` — the same commutation for the
--   size, clause for clause, with the same defer argument under it.
--   That one drops by the constructor `μᵉ` adds; this one holds equal,
--   since the reading passes a `μᵉ` through unchanged.
mutual
  dep-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    depᵉ η (elimGExp x cl e) ≡ depᵉ η e
  dep-elimG η x cl (input i)       = refl
  dep-elimG η x cl (ofᵉ ts)        = dep-elimGᵗˢ η x cl ts
  dep-elimG η x cl emptyᵉ          = refl
  dep-elimG η x cl (mapᵉ f e)      =
    cong₂ _⊔_ (dep-elimGᵗ η x cl f) (dep-elimG η x cl e)
  dep-elimG η x cl (takeᵉ c e)     =
    cong₂ _⊔_ (dep-elimGᵗ η x cl c) (dep-elimG η x cl e)
  dep-elimG η x cl (scanᵉ f z e)   =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-elimGᵗ η x cl f)
                         (dep-elimGᵗ η x cl z))
              (dep-elimG η x cl e)
  dep-elimG η x cl (mergeAllᵉ _ e) = dep-elimG η x cl e
  dep-elimG η x cl (switchAllᵉ e)  = dep-elimG η x cl e
  dep-elimG η x cl (exhaustAllᵉ e) = dep-elimG η x cl e
  dep-elimG η x cl (μᵉ e)          = dep-elimG η (there x) cl e
  dep-elimG η x cl (varᵉ y)        = refl
  dep-elimG η x cl (deferᵉ e)      = refl

  dep-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    depᵗ η (elimGTm x cl f) ≡ depᵗ η f
  dep-elimGᵗ η x cl (varᵗ y)      = refl
  dep-elimGᵗ η x cl unit̂          = refl
  dep-elimGᵗ η x cl (bool̂ b)      = refl
  dep-elimGᵗ η x cl (nat̂ k)       = refl
  dep-elimGᵗ η x cl (pairᵗ a b)   =
    cong₂ _⊔_ (dep-elimGᵗ η x cl a) (dep-elimGᵗ η x cl b)
  dep-elimGᵗ η x cl (fstᵗ p)      = dep-elimGᵗ η x cl p
  dep-elimGᵗ η x cl (sndᵗ p)      = dep-elimGᵗ η x cl p
  dep-elimGᵗ η x cl (inlᵗ a)      = dep-elimGᵗ η x cl a
  dep-elimGᵗ η x cl (inrᵗ a)      = dep-elimGᵗ η x cl a
  dep-elimGᵗ η x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (dep-elimGᵗ η x cl s)
                        (cong₂ _⊔_ (dep-elimGᵗ η x cl l)
                                   (dep-elimGᵗ η x cl r)))
  dep-elimGᵗ η x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-elimGᵗ η x cl c)
                         (dep-elimGᵗ η x cl a))
              (dep-elimGᵗ η x cl b)
  dep-elimGᵗ η x cl (primᵗ op a)  = dep-elimGᵗ η x cl a
  dep-elimGᵗ η x cl (strmᵗ e)     = cong suc (dep-elimG η x cl e)

  dep-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    depᵗˢ η (elimGTms x cl ts) ≡ depᵗˢ η ts
  dep-elimGᵗˢ η x cl []       = refl
  dep-elimGᵗˢ η x cl (y ∷ ys) =
    cong₂ _⊔_ (dep-elimGᵗ η x cl y) (dep-elimGᵗˢ η x cl ys)

-- THE FORM THE μ ARM ASKS FOR, WORD FOR WORD.  The peel steps the
-- descent on the SIZE and keeps the rank, so what re-establishes the
-- entry invariant at the unfolding is this — and it is an equality
-- rather than a drop, since the reading passes a `μᵉ` through unchanged.
dep-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (η : Fin n → ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  depᵉ η (unfoldμ body) ≡ depᵉ η body
dep-unfoldμ η body = dep-elimG η (here refl) (μᵉ body) body

dep-unfoldμ-no-deeper : ∀ {n} {Γ : Ctx n} {t} (η : Fin n → ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  depᵉ η (unfoldμ body) ≤ depᵉ η (μᵉ body)
dep-unfoldμ-no-deeper η body rewrite dep-unfoldμ η body = ≤-refl
