------------------------------------------------------------------
-- THE HOP PEEL'S MEASURE, AND IT CONSULTS THE SYNTAX PLUS ONE READING
-- OF THE SLOTS.  `strmᵗ` is the only head that writes an observable, so
-- the nesting of those heads is a quantity the PROGRAM carries; every
-- clause that binds nothing joins.  That is the whole difference from
-- the reading this replaces: a reading prices what a subtree will EMIT,
-- which multiplies as a flattener re-wraps, while this counts how deep
-- observables are WRITTEN, which a run can only walk down.
--
-- THE READING CARRIES ITS ENVIRONMENT'S BOUND AS AN ARGUMENT, AND THAT
-- IS WHAT PRICES A FREE VARIABLE AT ALL.  A `varᵗ` is a symbol standing
-- for whatever the run will substitute, so what it is worth is not a
-- property of the term: `m` is the bound the caller holds on the
-- environment, and the variable clause hands it straight back.  The
-- closed reading is this one at nought, since a term with nothing free
-- never reaches that clause.
--
-- ONE CLAUSE COMPOSES RATHER THAN COUNTING, AND IT IS THE ONLY HEAD OF
-- THE TERM LANGUAGE THAT MAKES ITS OWN ENVIRONMENT.  A `caseᵗ`
-- evaluates its scrutinee and BINDS what came out, so the branches are
-- read against a LARGER environment than the one handed in — larger by
-- exactly the bound the scrutinee's own reading gives, plus the `suc`
-- of the `reify` the binding goes through.  So the clause threads
-- `suc (depᵗ η m s) ⊔ m` into both branches instead of doing
-- arithmetic on the outside, and no fixed sum or join over the three
-- subterms is involved.  That is forced rather than chosen: the
-- multiplicity of a binder inside a branch is a function of the branch,
-- so any clause pricing the arm by an operation on three numbers is
-- either false where a binder is read twice or false where it is read
-- once.  `ifᵗ` binds nothing and still joins.
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
  depᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) (m : ℕ) → Exp Γ Δᵍ Δ Θ t → ℕ
  depᵉ η m (input i)          = η i
  depᵉ η m (ofᵉ ts)           = depᵗˢ η m ts
  depᵉ η m emptyᵉ             = 0
  depᵉ η m (mapᵉ f e)         = depᵗ η (bindᵃᵉ η m e) f ⊔ depᵉ η m e
  depᵉ η m (takeᵉ c e)        = depᵗ η (bindᵃᵉ η m e) c ⊔ depᵉ η m e
  depᵉ η m (scanᵉ f z e)      = depᵗ η (bindˢᵗ η m z e) f ⊔ depᵗ η m z ⊔ depᵉ η m e
  depᵉ η m (mergeAllᵉ lim e)  = depᵉ η m e
  depᵉ η m (switchAllᵉ e)     = depᵉ η m e
  depᵉ η m (exhaustAllᵉ e)    = depᵉ η m e
  depᵉ η m (μᵉ e)             = depᵉ η m e
  depᵉ η m (varᵉ x)           = 0
  depᵉ η m (deferᵉ e)         = 0

  depᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) (m : ℕ) → Tm Γ Δᵍ Δ Θ t → ℕ
  depᵗ η m (varᵗ x)      = m
  depᵗ η m unit̂          = 0
  depᵗ η m (bool̂ _)      = 0
  depᵗ η m (nat̂ _)       = 0
  depᵗ η m (pairᵗ a b)   = depᵗ η m a ⊔ depᵗ η m b
  depᵗ η m (fstᵗ p)      = depᵗ η m p
  depᵗ η m (sndᵗ p)      = depᵗ η m p
  depᵗ η m (inlᵗ a)      = depᵗ η m a
  depᵗ η m (inrᵗ a)      = depᵗ η m a
  depᵗ η m (caseᵗ s l r) = depᵗ η (bindᵃᵗ η m s) l ⊔ depᵗ η (bindᵃᵗ η m s) r
  depᵗ η m (ifᵗ c a b)   = depᵗ η m c ⊔ depᵗ η m a ⊔ depᵗ η m b
  depᵗ η m (primᵗ _ a)   = depᵗ η m a
  depᵗ η m (strmᵗ e)     = suc (depᵉ η m e)

  -- THE BOUND A BRANCH IS READ AT.  The run binds `evalWith s env` and
  -- the binding goes through `reify`, which writes one `strmᵗ` at
  -- observable type and none elsewhere; every older entry keeps its own
  -- bound.  So this is the environment bound the branches inherit, and
  -- it is a definition rather than a `let` so that the two branches and
  -- every lemma about them name one expression.
  bindᵃᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (η : Fin n → ℕ) (m : ℕ)
    → Tm Γ Δᵍ Δ Θ (s +ᵗ t) → ℕ
  bindᵃᵗ η m sc = suc (depᵗ η m sc) ⊔ m

  -- AND THE BOUND A TEMPLATE IS READ AT, WHICH IS THE SAME CONSTRUCTION
  -- ONE LEVEL UP.  An operator's template runs on what its SOURCE
  -- emitted, and an emission at observable type is already reified by
  -- the time it reaches the binder — so unlike a `caseᵗ`'s scrutinee
  -- there is no wrap to add, and what the binder is worth is the
  -- source's own reading.  The join with the incoming bound is there for
  -- the reason it is there above: entries older than this binder keep
  -- the bound they were admitted under.
  bindᵃᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) (m : ℕ)
    → Exp Γ Δᵍ Δ Θ t → ℕ
  bindᵃᵉ η m e = depᵉ η m e ⊔ m

  -- and the fold's, which admits the seed beside the source because the
  -- accumulator starts there
  bindˢᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (η : Fin n → ℕ) (m : ℕ)
    → Tm Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ s → ℕ
  bindˢᵗ η m z e = bindᵃᵉ η m e ⊔ depᵗ η m z

  depᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (η : Fin n → ℕ) (m : ℕ) → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  depᵗˢ η m []       = 0
  depᵗˢ η m (y ∷ ys) = depᵗ η m y ⊔ depᵗˢ η m ys

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
depᵛ η (obs t)  e        = depᵉ η 0 e

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
  dep-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (m : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    depᵉ η m (elimGExp x cl e) ≡ depᵉ η m e
  dep-elimG η m x cl (input i)       = refl
  dep-elimG η m x cl (ofᵉ ts)        = dep-elimGᵗˢ η m x cl ts
  dep-elimG η m x cl emptyᵉ          = refl
  dep-elimG η m x cl (mapᵉ f e)
    rewrite dep-elimG η m x cl e =
    cong₂ _⊔_ (dep-elimGᵗ η (bindᵃᵉ η m e) x cl f) refl
  dep-elimG η m x cl (takeᵉ c e)
    rewrite dep-elimG η m x cl e =
    cong₂ _⊔_ (dep-elimGᵗ η (bindᵃᵉ η m e) x cl c) refl
  dep-elimG η m x cl (scanᵉ f z e)
    rewrite dep-elimG η m x cl e | dep-elimGᵗ η m x cl z =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-elimGᵗ η (bindˢᵗ η m z e) x cl f) refl) refl
  dep-elimG η m x cl (mergeAllᵉ _ e) = dep-elimG η m x cl e
  dep-elimG η m x cl (switchAllᵉ e)  = dep-elimG η m x cl e
  dep-elimG η m x cl (exhaustAllᵉ e) = dep-elimG η m x cl e
  dep-elimG η m x cl (μᵉ e)          = dep-elimG η m (there x) cl e
  dep-elimG η m x cl (varᵉ y)        = refl
  dep-elimG η m x cl (deferᵉ e)      = refl

  dep-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (m : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    depᵗ η m (elimGTm x cl f) ≡ depᵗ η m f
  dep-elimGᵗ η m x cl (varᵗ y)      = refl
  dep-elimGᵗ η m x cl unit̂          = refl
  dep-elimGᵗ η m x cl (bool̂ b)      = refl
  dep-elimGᵗ η m x cl (nat̂ k)       = refl
  dep-elimGᵗ η m x cl (pairᵗ a b)   =
    cong₂ _⊔_ (dep-elimGᵗ η m x cl a) (dep-elimGᵗ η m x cl b)
  dep-elimGᵗ η m x cl (fstᵗ p)      = dep-elimGᵗ η m x cl p
  dep-elimGᵗ η m x cl (sndᵗ p)      = dep-elimGᵗ η m x cl p
  dep-elimGᵗ η m x cl (inlᵗ a)      = dep-elimGᵗ η m x cl a
  dep-elimGᵗ η m x cl (inrᵗ a)      = dep-elimGᵗ η m x cl a
  dep-elimGᵗ η m x cl (caseᵗ s l r)
    rewrite dep-elimGᵗ η m x cl s =
    cong₂ _⊔_ (dep-elimGᵗ η (bindᵃᵗ η m s) x cl l)
              (dep-elimGᵗ η (bindᵃᵗ η m s) x cl r)
  dep-elimGᵗ η m x cl (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-elimGᵗ η m x cl c)
                         (dep-elimGᵗ η m x cl a))
              (dep-elimGᵗ η m x cl b)
  dep-elimGᵗ η m x cl (primᵗ op a)  = dep-elimGᵗ η m x cl a
  dep-elimGᵗ η m x cl (strmᵗ e)     = cong suc (dep-elimG η m x cl e)

  dep-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (η : Fin n → ℕ) (m : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    depᵗˢ η m (elimGTms x cl ts) ≡ depᵗˢ η m ts
  dep-elimGᵗˢ η m x cl []       = refl
  dep-elimGᵗˢ η m x cl (y ∷ ys) =
    cong₂ _⊔_ (dep-elimGᵗ η m x cl y) (dep-elimGᵗˢ η m x cl ys)

-- THE FORM THE μ ARM ASKS FOR, WORD FOR WORD.  The peel steps the
-- descent on the SIZE and keeps the rank, so what re-establishes the
-- entry invariant at the unfolding is this — and it is an equality
-- rather than a drop, since the reading passes a `μᵉ` through unchanged.
dep-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (η : Fin n → ℕ) (m : ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  depᵉ η m (unfoldμ body) ≡ depᵉ η m body
dep-unfoldμ η m body = dep-elimG η m (here refl) (μᵉ body) body

dep-unfoldμ-no-deeper : ∀ {n} {Γ : Ctx n} {t} (η : Fin n → ℕ) (m : ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  depᵉ η m (unfoldμ body) ≤ depᵉ η m (μᵉ body)
dep-unfoldμ-no-deeper η m body rewrite dep-unfoldμ η m body = ≤-refl
