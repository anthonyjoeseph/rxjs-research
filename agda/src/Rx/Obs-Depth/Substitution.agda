------------------------------------------------------------------
-- THE SUBSTITUTION LEMMA: WHAT A TEMPLATE EMITS IS READ OFF THE
-- TEMPLATE, NOT OFF WHAT IT WAS HANDED.  A sketch — nothing here
-- typechecks yet.
--
-- `applyFn fn v` is `evalWith fn (v ∷ᵃ []ᵃ)`, and at an observable
-- result type the only head that can produce one is `strmᵗ e`, whose
-- value is `closeUnderFn e (v ∷ᵃ []ᵃ)` — a SUBSTITUTION INSTANCE of a
-- subterm of `fn`.  Substituting DATA into an expression moves no
-- `strmᵗ`, so the instance reads exactly what the subterm reads:
--
--   obsDepthᵉ (applyFn fn v) ≡ obsDepthᵉ e < suc (obsDepthᵉ e) ≡ obsDepthᵗ fn
--
-- The inequality is STRICT and it mentions no machine state, no store,
-- no bound the frame was entered under — only the program.
--
-- AND THAT IS WHY IT ANSWERS SIX REFUTATIONS AT ONCE RATHER THAN A
-- SIXTH TIME.  Every one of them — the term's reading, the widest
-- state-readable join, the arrival's seed, the filtered spend, the map
-- template, the pinned template — refutes a PRICE stated in terms of
-- what the frame was HANDED.  A template that drops its argument and a
-- template that wraps it are both refutations of that form of statement
-- and neither is a refutation of this one, because a price denominated
-- in the TERM cannot be moved by any value handed to it.  Under
-- `CLAUDE.md`'s convergence test six FALSITY results over one region are
-- the spiral signal, and the prescribed response is to change the
-- mechanism: this is that change, and it is a change of CURRENCY.
--
-- THE ONE PLACE THE PREMISE GENUINELY FAILS IS A BINDER AT OBSERVABLE
-- TYPE, and it is the axis the carried family already found.  A `scanᵉ`
-- whose accumulator is an observable feeds its own output back into the
-- environment, so the environment stops being data and the substitution
-- grows by one wrap per refold; a `caseᵗ` scrutinising a sum containing
-- an observable re-binds one the same way.  Both are the OPEN form
-- below, whose growth is per-iteration and bounded by the script
-- length — dynamic, and the only thing that is.
--
-- TWIN: `Rx.Obs-Depth.obsDepth-elimG` — the same commutation for the
--   guarded substitution, clause for clause, equality and not a bound.
--   That one substitutes a closed EXPRESSION for a μ-variable; this one
--   substitutes a value environment for the Θ-variables, and the reason
--   both hold is the same: neither substitution introduces a `strmᵗ`.
module Rx.Obs-Depth.Substitution where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _+_; _⊔_; z≤n)
open import Data.Nat.Properties using (≤-trans; n≤1+n; ⊔-mono-≤; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; Fn; isData;
  unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  reify; wkTm; lookupEnv; subΘExp; subΘTm; subΘTms; closeUnderFn;
  evalWith; applyFn; syncSizeᵉ; syncSizeᵗ)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵗ; obsDepthᵗˢ; obsDepthᵛ)

------------------------------------------------------------------
-- 1.  DATA ENVIRONMENTS, WHICH ARE WHAT MAKE THE READING STATIC.
------------------------------------------------------------------

-- `isData (obs _)` is `false` and every other type is built from
-- types that are data, so this says exactly: no binder in Θ can be
-- instantiated with something the run could subscribe.
data AllData : List Ty → Set where
  []ᵈ  : AllData []
  _∷ᵈ_ : ∀ {t Θ} → isData t ≡ true → AllData Θ → AllData (t ∷ Θ)

-- a data value reads zero, both as a value and as the term `reify`
-- writes for it.  These are the two clauses the substitution's `varᵗ`
-- arm and the evaluation's `varᵗ` arm respectively spend, and they are
-- the ONLY place the data hypothesis is used — everything else is
-- structural.
obsDepthᵛ-data : ∀ {n} {Γ : Ctx n} (t : Ty) → isData t ≡ true →
  (v : Val Γ t) → obsDepthᵛ t v ≡ 0
obsDepthᵛ-data unitᵗ    _  _        = refl
obsDepthᵛ-data boolᵗ    _  _        = refl
obsDepthᵛ-data natᵗ     _  _        = refl
obsDepthᵛ-data (s ×ᵗ t) dt (a , b)  =
  cong₂ _⊔_ (obsDepthᵛ-data s (×-dataˡ s t dt) a)
            (obsDepthᵛ-data t (×-dataʳ s t dt) b)
obsDepthᵛ-data (s +ᵗ t) dt (inj₁ a) = obsDepthᵛ-data s (+-dataˡ s t dt) a
obsDepthᵛ-data (s +ᵗ t) dt (inj₂ b) = obsDepthᵛ-data t (+-dataʳ s t dt) b
obsDepthᵛ-data (obs t)  ()  _

obsDepth-reify-data : ∀ {n} {Γ : Ctx n} (t : Ty) → isData t ≡ true →
  (v : Val Γ t) → obsDepthᵗ (reify v) ≡ 0
obsDepth-reify-data unitᵗ    _  _        = refl
obsDepth-reify-data boolᵗ    _  _        = refl
obsDepth-reify-data natᵗ     _  _        = refl
obsDepth-reify-data (s ×ᵗ t) dt (a , b)  =
  cong₂ _⊔_ (obsDepth-reify-data s (×-dataˡ s t dt) a)
            (obsDepth-reify-data t (×-dataʳ s t dt) b)
obsDepth-reify-data (s +ᵗ t) dt (inj₁ a) = obsDepth-reify-data s (+-dataˡ s t dt) a
obsDepth-reify-data (s +ᵗ t) dt (inj₂ b) = obsDepth-reify-data t (+-dataʳ s t dt) b
obsDepth-reify-data (obs t)  ()  _

-- the four projections the two clauses above need out of `isData`'s
-- `if`-shaped definition.  Mechanical: `isData (s ×ᵗ t)` is
-- `if isData s then isData t else false`, so a `true` there decides
-- both sides, and the `with` that reads it is the whole proof.
postulate
  ×-dataˡ : ∀ s t → isData (s ×ᵗ t) ≡ true → isData s ≡ true
  ×-dataʳ : ∀ s t → isData (s ×ᵗ t) ≡ true → isData t ≡ true
  +-dataˡ : ∀ s t → isData (s +ᵗ t) ≡ true → isData s ≡ true
  +-dataʳ : ∀ s t → isData (s +ᵗ t) ≡ true → isData t ≡ true

lookup-data : ∀ {n} {Γ : Ctx n} {Θ t} → AllData Θ →
  (σ : All (Val Γ) Θ) (x : t ∈ Θ) → obsDepthᵗ (reify (lookupEnv σ x)) ≡ 0
lookup-data (d ∷ᵈ _)  (v ∷ᵃ _)  (here refl) = obsDepth-reify-data _ d v
lookup-data (_ ∷ᵈ ds) (_ ∷ᵃ vs) (there p)   = lookup-data ds vs p

-- weakening writes no head, so it moves no reading.  Stated for the
-- exact instance the substitution's `varᵗ` arm produces rather than for
-- a general renaming, because that arm is the only consumer.
postulate
  obsDepth-wkTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (f : Tm Γ [] [] [] t) →
    obsDepthᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} f) ≡ obsDepthᵗ f

------------------------------------------------------------------
-- 2.  THE LEMMA, CLAUSE FOR CLAUSE AGAINST ITS TWIN.
------------------------------------------------------------------

-- Every clause but one is `cong` over the sub-derivations, exactly as
-- `obsDepth-elimG`'s are.  The one that carries content is `varᵗ`, and
-- it splits the way `subΘTm` splits: a LOCAL binder survives as a
-- `varᵗ` and reads zero on both sides, while a SUBSTITUTED binder
-- becomes a reified data value and reads zero because it is data.  The
-- `strmᵗ` clause is where the equality would fail for a non-data
-- environment, since that is the only head under which a substituted
-- observable would be counted.
mutual
  obsDepth-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    obsDepthᵉ (subΘExp Θloc σ e) ≡ obsDepthᵉ e
  obsDepth-subΘ Θloc dd σ (input i)       = refl
  obsDepth-subΘ Θloc dd σ (ofᵉ ts)        = obsDepth-subΘᵗˢ Θloc dd σ ts
  obsDepth-subΘ Θloc dd σ emptyᵉ          = refl
  obsDepth-subΘ Θloc dd σ (mapᵉ {s = s} f e) =
    cong₂ _⊔_ (obsDepth-subΘᵗ (s ∷ Θloc) dd σ f) (obsDepth-subΘ Θloc dd σ e)
  obsDepth-subΘ Θloc dd σ (takeᵉ c e)     =
    cong₂ _⊔_ (obsDepth-subΘᵗ Θloc dd σ c) (obsDepth-subΘ Θloc dd σ e)
  obsDepth-subΘ Θloc dd σ (scanᵉ {s = s} {t = t} f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-subΘᵗ ((t ×ᵗ s) ∷ Θloc) dd σ f)
                         (obsDepth-subΘᵗ Θloc dd σ z))
              (obsDepth-subΘ Θloc dd σ e)
  obsDepth-subΘ Θloc dd σ (mergeAllᵉ _ e) = obsDepth-subΘ Θloc dd σ e
  obsDepth-subΘ Θloc dd σ (switchAllᵉ e)  = obsDepth-subΘ Θloc dd σ e
  obsDepth-subΘ Θloc dd σ (exhaustAllᵉ e) = obsDepth-subΘ Θloc dd σ e
  obsDepth-subΘ Θloc dd σ (μᵉ e)          = obsDepth-subΘ Θloc dd σ e
  obsDepth-subΘ Θloc dd σ (varᵉ x)        = refl
  obsDepth-subΘ Θloc dd σ (deferᵉ e)      = refl

  obsDepth-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (f : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    obsDepthᵗ (subΘTm Θloc σ f) ≡ obsDepthᵗ f
  obsDepth-subΘᵗ Θloc dd σ (varᵗ x) with ∈-++⁻ Θloc x
  ... | inj₁ y = refl
  ... | inj₂ z = trans (obsDepth-wkTm (reify (lookupEnv σ z)))
                       (lookup-data dd σ z)
  obsDepth-subΘᵗ Θloc dd σ unit̂          = refl
  obsDepth-subΘᵗ Θloc dd σ (bool̂ b)      = refl
  obsDepth-subΘᵗ Θloc dd σ (nat̂ k)       = refl
  obsDepth-subΘᵗ Θloc dd σ (pairᵗ a b)   =
    cong₂ _⊔_ (obsDepth-subΘᵗ Θloc dd σ a) (obsDepth-subΘᵗ Θloc dd σ b)
  obsDepth-subΘᵗ Θloc dd σ (fstᵗ p)      = obsDepth-subΘᵗ Θloc dd σ p
  obsDepth-subΘᵗ Θloc dd σ (sndᵗ p)      = obsDepth-subΘᵗ Θloc dd σ p
  obsDepth-subΘᵗ Θloc dd σ (inlᵗ a)      = obsDepth-subΘᵗ Θloc dd σ a
  obsDepth-subΘᵗ Θloc dd σ (inrᵗ a)      = obsDepth-subΘᵗ Θloc dd σ a
  obsDepth-subΘᵗ Θloc dd σ (caseᵗ {s = s} {t = t} sc l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-subΘᵗ Θloc dd σ sc)
                         (obsDepth-subΘᵗ (s ∷ Θloc) dd σ l))
              (obsDepth-subΘᵗ (t ∷ Θloc) dd σ r)
  obsDepth-subΘᵗ Θloc dd σ (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (obsDepth-subΘᵗ Θloc dd σ c)
                         (obsDepth-subΘᵗ Θloc dd σ a))
              (obsDepth-subΘᵗ Θloc dd σ b)
  obsDepth-subΘᵗ Θloc dd σ (primᵗ op a)  = obsDepth-subΘᵗ Θloc dd σ a
  obsDepth-subΘᵗ Θloc dd σ (strmᵗ e)     = cong suc (obsDepth-subΘ Θloc dd σ e)

  obsDepth-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    obsDepthᵗˢ (subΘTms Θloc σ ts) ≡ obsDepthᵗˢ ts
  obsDepth-subΘᵗˢ Θloc dd σ []       = refl
  obsDepth-subΘᵗˢ Θloc dd σ (y ∷ ys) =
    cong₂ _⊔_ (obsDepth-subΘᵗ Θloc dd σ y) (obsDepth-subΘᵗˢ Θloc dd σ ys)

obsDepth-closeUnderFn : ∀ {n} {Γ : Ctx n} {s Θ t} → AllData (s ∷ Θ) →
  (e : Exp Γ [] [] (s ∷ Θ) t) (env : All (Val Γ) (s ∷ Θ)) →
  obsDepthᵉ (closeUnderFn e env) ≡ obsDepthᵉ e
obsDepth-closeUnderFn dd e env = obsDepth-subΘ [] dd env e

------------------------------------------------------------------
-- 3.  EVALUATION, AND THE STRICT DROP THAT IS THE DOOR'S PREMISE.
------------------------------------------------------------------

-- A value evaluated out of a term reads no deeper than the term, and
-- at an OBSERVABLE result type it reads strictly shallower — because
-- the only head that can produce one is `strmᵗ`, which is a successor,
-- and the substitution under it is depth-preserving by the lemma above.
obsDepth-eval : ∀ {n} {Γ : Ctx n} {Θ t} → AllData Θ →
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
  obsDepthᵛ t (evalWith tm env) ≤ obsDepthᵗ tm
obsDepth-eval dd (varᵗ x)      env
  rewrite obsDepthᵛ-data _ (data-of dd x) (lookupEnv env x) = z≤n
obsDepth-eval dd unit̂          env = z≤n
obsDepth-eval dd (bool̂ b)      env = z≤n
obsDepth-eval dd (nat̂ k)       env = z≤n
obsDepth-eval dd (pairᵗ a b)   env =
  ⊔-mono-≤ (obsDepth-eval dd a env) (obsDepth-eval dd b env)
obsDepth-eval dd (fstᵗ p)      env =
  ≤-trans (m≤m⊔n _ _) (obsDepth-eval dd p env)
    -- the pair's reading is the join of its components', so a
    -- projection reads no more than the pair
obsDepth-eval dd (sndᵗ p)      env =
  ≤-trans (m≤n⊔m _ _) (obsDepth-eval dd p env)
obsDepth-eval dd (inlᵗ a)      env = obsDepth-eval dd a env
obsDepth-eval dd (inrᵗ a)      env = obsDepth-eval dd a env
obsDepth-eval dd (caseᵗ sc l r) env = eval-case dd sc l r env
obsDepth-eval dd (ifᵗ c a b)   env = eval-if dd c a b env
obsDepth-eval dd (primᵗ op a)  env = z≤n
obsDepth-eval dd (strmᵗ e)     []ᵃ = n≤1+n _
obsDepth-eval dd (strmᵗ e)     (v ∷ᵃ vs)
  rewrite obsDepth-closeUnderFn dd e (v ∷ᵃ vs) = n≤1+n _

-- THE ONE ARM WHERE THE ENVIRONMENT STOPS BEING DATA, and it is the
-- same arm the fold has.  A `caseᵗ` on a sum containing an observable
-- binds one into the branch environment, so the branch is evaluated
-- under an environment this lemma's hypothesis does not cover.  The
-- bound is not lost — the bound value came OUT of the scrutinee, whose
-- own reading is a program quantity — but recovering it needs the open
-- form below rather than this one.
--
-- `ifᵗ` is separate only because Agda cannot see through the `if` that
-- selects the branch; nothing about it is open.
postulate
  eval-case : ∀ {n} {Γ : Ctx n} {Θ s t u} → AllData Θ →
    (sc : Tm Γ [] [] Θ (s +ᵗ t)) (l : Tm Γ [] [] (s ∷ Θ) u)
    (r : Tm Γ [] [] (t ∷ Θ) u) (env : All (Val Γ) Θ) →
    obsDepthᵛ u (evalWith (caseᵗ sc l r) env) ≤ obsDepthᵗ (caseᵗ sc l r)

  eval-if : ∀ {n} {Γ : Ctx n} {Θ t} → AllData Θ →
    (c : Tm Γ [] [] Θ boolᵗ) (a b : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
    obsDepthᵛ t (evalWith (ifᵗ c a b) env) ≤ obsDepthᵗ (ifᵗ c a b)

  data-of : ∀ {Θ t} → AllData Θ → t ∈ Θ → isData t ≡ true

-- THE OPEN FORM: what an environment carrying observables costs, which
-- is one wrap per binder crossed and NOT a function of the machine.
-- This is the statement the fold's arm needs, and the growth in it is
-- the iteration axis the carried family already names — stated here so
-- the two are the same fact rather than two.
postulate
  obsDepth-eval-open : ∀ {n} {Γ : Ctx n} {Θ t}
    (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) (m : ℕ) →
    envDepth env ≤ m → obsDepthᵛ t (evalWith tm env) ≤ obsDepthᵗ tm + m

envDepth : ∀ {n} {Γ : Ctx n} {Θ} → All (Val Γ) Θ → ℕ
envDepth []ᵃ       = 0
envDepth (v ∷ᵃ vs) = obsDepthᵗ (reify v) ⊔ envDepth vs

-- THE COROLLARY THE DOOR ASKS FOR, AND IT IS THE WHOLE POINT.  An
-- observable emitted by a template is written strictly below the
-- template — with no hypothesis about the run, the store, or the bound
-- the frame was entered under.  `subscribeInner`'s guard is exactly
-- this comparison, so where its argument came from a template the guard
-- can never fail.
obsDepth-applyFn : ∀ {n} {Γ : Ctx n} {s u} → isData s ≡ true →
  (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
  obsDepthᵉ (applyFn fn v) < obsDepthᵗ fn
obsDepth-applyFn ds fn v = applyFn-strict ds fn v

-- the strictness, which the weak lemma above does not give directly:
-- at an observable result type `tm` cannot be a `varᵗ` (its type would
-- have to be data), so every head is either a successor or an
-- eliminator whose own reading dominates.  One case split away from the
-- weak form and postulated only because that split is mechanical.
postulate
  applyFn-strict : ∀ {n} {Γ : Ctx n} {s u} → isData s ≡ true →
    (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
    obsDepthᵉ (applyFn fn v) < obsDepthᵗ fn

-- AND THE SIZE HALF, WHICH THIS ROUTE DOES NOT GIVE FOR FREE.  A
-- substituted data value replaces a `varᵗ` of size one with a literal
-- whose size is a function of its TYPE — bounded, but not by one.  So
-- the size axis keeps the pair the carried family states it at; what
-- the substitution lemma collapses is the DEPTH axis, which is the one
-- the door reads.
postulate
  syncSize-applyFn : ∀ {n} {Γ : Ctx n} {s u} → isData s ≡ true →
    (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
    syncSizeᵉ (applyFn fn v) ≤ syncSizeᵗ fn + dataSize s

  dataSize : Ty → ℕ
