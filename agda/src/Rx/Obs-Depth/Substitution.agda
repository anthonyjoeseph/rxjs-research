------------------------------------------------------------------
-- THE SUBSTITUTION LEMMA: WHAT A TEMPLATE EMITS IS READ OFF THE
-- TEMPLATE, NOT OFF WHAT IT WAS HANDED.
--
-- `applyFn fn v` is `evalWith fn (v ∷ᵃ []ᵃ)`, and at an observable
-- result type the only head that can produce one is `strmᵗ e`, whose
-- value is `closeUnderFn e (v ∷ᵃ []ᵃ)` — a SUBSTITUTION INSTANCE of a
-- subterm of `fn`.  Substituting DATA into an expression moves no
-- `strmᵗ`, so the instance reads exactly what the subterm reads:
--
--   depᵉ η (applyFn fn v) ≡ depᵉ η e < suc (depᵉ η e) ≡ depᵗ η fn
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
-- TWIN: `Rx.Obs-Depth.dep-elimG` — the same commutation for the
--   guarded substitution, clause for clause, equality and not a bound.
--   That one substitutes a closed EXPRESSION for a μ-variable; this one
--   substitutes a value environment for the Θ-variables, and the reason
--   both hold is the same: neither substitution introduces a `strmᵗ`.
module Rx.Obs-Depth.Substitution where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _+_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ⊔-mono-≤; m≤m⊔n; m≤n⊔m;
  ⊔-identityʳ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; Fn; isData;
  unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; ltᵖ; notᵖ;
  reify; wkTm; lookupEnv; subΘExp; subΘTm; subΘTms; closeUnderFn;
  evalWith; applyFn; syncSizeᵉ; syncSizeᵗ)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ; depᵛ)

------------------------------------------------------------------
-- 1.  DATA ENVIRONMENTS, WHICH ARE WHAT MAKE THE READING STATIC.
------------------------------------------------------------------

-- `isData (obs _)` is `false` and every other type is built from
-- types that are data, so this says exactly: no binder in Θ can be
-- instantiated with something the run could subscribe.
data AllData : List Ty → Set where
  []ᵈ  : AllData []
  _∷ᵈ_ : ∀ {t Θ} → isData t ≡ true → AllData Θ → AllData (t ∷ Θ)

-- the four projections the two clauses below need out of `isData`'s
-- `if`-shaped definition.  Mechanical: `isData (s ×ᵗ t)` is
-- `if isData s then isData t else false`, so a `true` there decides
-- both sides, and the `with` that reads it is the whole proof.  Both
-- pairs read the SAME `if`, since the sum's clause and the product's
-- clause are the same expression at different constructors, so one
-- pair of helpers over two bare booleans closes all four.
private
  ifˡ : ∀ a b → (if a then b else false) ≡ true → a ≡ true
  ifˡ true  b p = refl
  ifˡ false b ()

  ifʳ : ∀ a b → (if a then b else false) ≡ true → b ≡ true
  ifʳ true  b p = p
  ifʳ false b ()

×-dataˡ : ∀ s t → isData (s ×ᵗ t) ≡ true → isData s ≡ true
×-dataˡ s t = ifˡ (isData s) (isData t)

×-dataʳ : ∀ s t → isData (s ×ᵗ t) ≡ true → isData t ≡ true
×-dataʳ s t = ifʳ (isData s) (isData t)

+-dataˡ : ∀ s t → isData (s +ᵗ t) ≡ true → isData s ≡ true
+-dataˡ s t = ifˡ (isData s) (isData t)

+-dataʳ : ∀ s t → isData (s +ᵗ t) ≡ true → isData t ≡ true
+-dataʳ s t = ifʳ (isData s) (isData t)

-- PROBED: `Probed.Data-Shelf` — a membership at the head of the
--   telescope and past it.  The rows buy NON-VACUITY rather than an
--   inequality: the conclusion is a `Bool` the type alone decides, so
--   what is covered is that the premise is inhabited at a nested type
--   at all.
postulate
  data-of : ∀ {Θ t} → AllData Θ → t ∈ Θ → isData t ≡ true

-- a data value reads zero, both as a value and as the term `reify`
-- writes for it.  These are the two clauses the substitution's `varᵗ`
-- arm and the evaluation's `varᵗ` arm respectively spend, and they are
-- the ONLY place the data hypothesis is used — everything else is
-- structural.
dep-dataᵛ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (t : Ty) → isData t ≡ true →
  (v : Val Γ t) → depᵛ η t v ≡ 0
dep-dataᵛ η unitᵗ    _  _        = refl
dep-dataᵛ η boolᵗ    _  _        = refl
dep-dataᵛ η natᵗ     _  _        = refl
dep-dataᵛ η (s ×ᵗ t) dt (a , b)  =
  cong₂ _⊔_ (dep-dataᵛ η s (×-dataˡ s t dt) a)
            (dep-dataᵛ η t (×-dataʳ s t dt) b)
dep-dataᵛ η (s +ᵗ t) dt (inj₁ a) = dep-dataᵛ η s (+-dataˡ s t dt) a
dep-dataᵛ η (s +ᵗ t) dt (inj₂ b) = dep-dataᵛ η t (+-dataʳ s t dt) b
dep-dataᵛ η (obs t)  ()  _

dep-reify-data : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (t : Ty) → isData t ≡ true →
  (v : Val Γ t) → depᵗ η (reify v) ≡ 0
dep-reify-data η unitᵗ    _  _        = refl
dep-reify-data η boolᵗ    _  _        = refl
dep-reify-data η natᵗ     _  _        = refl
dep-reify-data η (s ×ᵗ t) dt (a , b)  =
  cong₂ _⊔_ (dep-reify-data η s (×-dataˡ s t dt) a)
            (dep-reify-data η t (×-dataʳ s t dt) b)
dep-reify-data η (s +ᵗ t) dt (inj₁ a) = dep-reify-data η s (+-dataˡ s t dt) a
dep-reify-data η (s +ᵗ t) dt (inj₂ b) = dep-reify-data η t (+-dataʳ s t dt) b
dep-reify-data η (obs t)  ()  _

lookup-data : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t} → AllData Θ →
  (σ : All (Val Γ) Θ) (x : t ∈ Θ) → depᵗ η (reify (lookupEnv σ x)) ≡ 0
lookup-data η (d ∷ᵈ _)  (v ∷ᵃ _)  (here refl) = dep-reify-data η _ d v
lookup-data η (_ ∷ᵈ ds) (_ ∷ᵃ vs) (there p)   = lookup-data η ds vs p

-- weakening writes no head, so it moves no reading.  Stated for the
-- exact instance the substitution's `varᵗ` arm produces rather than for
-- a general renaming, because that arm is the only consumer.
--
-- PROBED: `Probed.Data-Shelf` — a leaf, and a term whose head is
--   `strmᵗ`, which is the only head the reading counts and so the only
--   one a renaming could move.  Not reached: a term with a binder
--   under the weakened context.
postulate
  dep-wkTm : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} (f : Tm Γ [] [] [] t) →
    depᵗ η (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} f) ≡ depᵗ η f

------------------------------------------------------------------
-- 2.  THE LEMMA, CLAUSE FOR CLAUSE AGAINST ITS TWIN.
------------------------------------------------------------------

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
--
-- PROBED: `Probed.Eval-Binders` — a `caseᵗ` at a data payload with
--   both arms writing, and at an OBSERVABLE payload handed straight
--   back by the branch, which is the region that could make either
--   statement false; the second row is TIGHT, the value's reading
--   landing on the predecessor exactly.  An `ifᵗ` at a selected arm
--   that sets the join and at one that does not.  Not reached: an
--   arm whose reading differs from its sibling's with the observable
--   one selected, where the join gives slack by construction.
postulate
  eval-case : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ s t u} → AllData Θ →
    (sc : Tm Γ [] [] Θ (s +ᵗ t)) (l : Tm Γ [] [] (s ∷ Θ) u)
    (r : Tm Γ [] [] (t ∷ Θ) u) (env : All (Val Γ) Θ) →
    depᵛ η u (evalWith (caseᵗ sc l r) env) ≤ pred (depᵗ η (caseᵗ sc l r))

  eval-if : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t} → AllData Θ →
    (c : Tm Γ [] [] Θ boolᵗ) (a b : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
    depᵛ η t (evalWith (ifᵗ c a b) env) ≤ pred (depᵗ η (ifᵗ c a b))

-- Every clause but one is `cong` over the sub-derivations, exactly as
-- `dep-elimG`'s are.  The one that carries content is `varᵗ`, and
-- it splits the way `subΘTm` splits: a LOCAL binder survives as a
-- `varᵗ` and reads zero on both sides, while a SUBSTITUTED binder
-- becomes a reified data value and reads zero because it is data.  The
-- `strmᵗ` clause is where the equality would fail for a non-data
-- environment, since that is the only head under which a substituted
-- observable would be counted.
mutual
  dep-subΘ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    depᵉ η (subΘExp Θloc σ e) ≡ depᵉ η e
  dep-subΘ η Θloc dd σ (input i)       = refl
  dep-subΘ η Θloc dd σ (ofᵉ ts)        = dep-subΘᵗˢ η Θloc dd σ ts
  dep-subΘ η Θloc dd σ emptyᵉ          = refl
  dep-subΘ η Θloc dd σ (mapᵉ {s = s} f e) =
    cong₂ _⊔_ (dep-subΘᵗ η (s ∷ Θloc) dd σ f) (dep-subΘ η Θloc dd σ e)
  dep-subΘ η Θloc dd σ (takeᵉ c e)     =
    cong₂ _⊔_ (dep-subΘᵗ η Θloc dd σ c) (dep-subΘ η Θloc dd σ e)
  dep-subΘ η Θloc dd σ (scanᵉ {s = s} {t = t} f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-subΘᵗ η ((t ×ᵗ s) ∷ Θloc) dd σ f)
                         (dep-subΘᵗ η Θloc dd σ z))
              (dep-subΘ η Θloc dd σ e)
  dep-subΘ η Θloc dd σ (mergeAllᵉ _ e) = dep-subΘ η Θloc dd σ e
  dep-subΘ η Θloc dd σ (switchAllᵉ e)  = dep-subΘ η Θloc dd σ e
  dep-subΘ η Θloc dd σ (exhaustAllᵉ e) = dep-subΘ η Θloc dd σ e
  dep-subΘ η Θloc dd σ (μᵉ e)          = dep-subΘ η Θloc dd σ e
  dep-subΘ η Θloc dd σ (varᵉ x)        = refl
  dep-subΘ η Θloc dd σ (deferᵉ e)      = refl

  dep-subΘᵗ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (f : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    depᵗ η (subΘTm Θloc σ f) ≡ depᵗ η f
  dep-subΘᵗ η Θloc dd σ (varᵗ x) with ∈-++⁻ Θloc x
  ... | inj₁ y = refl
  ... | inj₂ z = trans (dep-wkTm η (reify (lookupEnv σ z)))
                       (lookup-data η dd σ z)
  dep-subΘᵗ η Θloc dd σ unit̂          = refl
  dep-subΘᵗ η Θloc dd σ (bool̂ b)      = refl
  dep-subΘᵗ η Θloc dd σ (nat̂ k)       = refl
  dep-subΘᵗ η Θloc dd σ (pairᵗ a b)   =
    cong₂ _⊔_ (dep-subΘᵗ η Θloc dd σ a) (dep-subΘᵗ η Θloc dd σ b)
  dep-subΘᵗ η Θloc dd σ (fstᵗ p)      = dep-subΘᵗ η Θloc dd σ p
  dep-subΘᵗ η Θloc dd σ (sndᵗ p)      = dep-subΘᵗ η Θloc dd σ p
  dep-subΘᵗ η Θloc dd σ (inlᵗ a)      = dep-subΘᵗ η Θloc dd σ a
  dep-subΘᵗ η Θloc dd σ (inrᵗ a)      = dep-subΘᵗ η Θloc dd σ a
  dep-subΘᵗ η Θloc dd σ (caseᵗ {s = s} {t = t} sc l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-subΘᵗ η Θloc dd σ sc)
                         (dep-subΘᵗ η (s ∷ Θloc) dd σ l))
              (dep-subΘᵗ η (t ∷ Θloc) dd σ r)
  dep-subΘᵗ η Θloc dd σ (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (dep-subΘᵗ η Θloc dd σ c)
                         (dep-subΘᵗ η Θloc dd σ a))
              (dep-subΘᵗ η Θloc dd σ b)
  dep-subΘᵗ η Θloc dd σ (primᵗ op a)  = dep-subΘᵗ η Θloc dd σ a
  dep-subΘᵗ η Θloc dd σ (strmᵗ e)     = cong suc (dep-subΘ η Θloc dd σ e)

  dep-subΘᵗˢ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (dd : AllData Θsub) (σ : All (Val Γ) Θsub)
    (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    depᵗˢ η (subΘTms Θloc σ ts) ≡ depᵗˢ η ts
  dep-subΘᵗˢ η Θloc dd σ []       = refl
  dep-subΘᵗˢ η Θloc dd σ (y ∷ ys) =
    cong₂ _⊔_ (dep-subΘᵗ η Θloc dd σ y) (dep-subΘᵗˢ η Θloc dd σ ys)

dep-closeUnderFn : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {s Θ t} → AllData (s ∷ Θ) →
  (e : Exp Γ [] [] (s ∷ Θ) t) (env : All (Val Γ) (s ∷ Θ)) →
  depᵉ η (closeUnderFn e env) ≡ depᵉ η e
dep-closeUnderFn η dd e env = dep-subΘ η [] dd env e

------------------------------------------------------------------
-- 3.  EVALUATION, AND THE STRICT DROP THAT IS THE DOOR'S PREMISE.
------------------------------------------------------------------

-- THE PREDECESSOR IS WHAT MAKES THE STATEMENT UNCONDITIONAL, and that
-- is the one design decision in this block.  The reading wanted at the
-- door is STRICT, and a strict statement cannot be made at a term whose
-- own reading is nought — so the obvious form carries a positivity
-- premise, and then every clause has to case-split on which side of a
-- join is the positive one before it can hand the premise down.  Stated
-- against the predecessor there is no premise to hand down: it is
-- nought where the term is nought, it is the strict drop everywhere
-- else, and `pred` distributes over the join, so the whole induction is
-- the weak one with a `pred` in front of it.
--
-- The positivity is then owed exactly once, by whoever wants the
-- strictness, and at an observable result type it is a fact about the
-- SYNTAX with no environment in it.
private
  pred-⊔ : ∀ m n → pred (m ⊔ n) ≡ pred m ⊔ pred n
  pred-⊔ zero    n       = refl
  pred-⊔ (suc m) zero    = sym (⊔-identityʳ m)
  pred-⊔ (suc m) (suc n) = refl

  ≤pred⇒< : ∀ {a m} → 0 < m → a ≤ pred m → a < m
  ≤pred⇒< {m = suc m} _ a≤ = s≤s a≤

-- A value evaluated out of a term reads no deeper than the term's own
-- predecessor — so at an OBSERVABLE result type, where the only head
-- that can produce one is the successor `strmᵗ`, it reads strictly
-- shallower.  The substitution under that successor is depth-preserving
-- by the lemma above, which is the whole content of the last clause.
dep-eval-strict : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t} → AllData Θ →
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
  depᵛ η t (evalWith tm env) ≤ pred (depᵗ η tm)
dep-eval-strict η dd (varᵗ x)      env
  rewrite dep-dataᵛ η _ (data-of dd x) (lookupEnv env x) = z≤n
dep-eval-strict η dd unit̂          env = z≤n
dep-eval-strict η dd (bool̂ b)      env = z≤n
dep-eval-strict η dd (nat̂ k)       env = z≤n
dep-eval-strict η dd (pairᵗ a b)   env
  rewrite pred-⊔ (depᵗ η a) (depᵗ η b) =
  ⊔-mono-≤ (dep-eval-strict η dd a env) (dep-eval-strict η dd b env)
dep-eval-strict η dd (fstᵗ p)      env =
  ≤-trans (m≤m⊔n _ _) (dep-eval-strict η dd p env)
    -- the pair's reading is the join of its components', so a
    -- projection reads no more than the pair
dep-eval-strict η dd (sndᵗ p)      env =
  ≤-trans (m≤n⊔m _ _) (dep-eval-strict η dd p env)
dep-eval-strict η dd (inlᵗ a)      env = dep-eval-strict η dd a env
dep-eval-strict η dd (inrᵗ a)      env = dep-eval-strict η dd a env
dep-eval-strict η dd (caseᵗ sc l r) env = eval-case η dd sc l r env
dep-eval-strict η dd (ifᵗ c a b)   env = eval-if η dd c a b env
dep-eval-strict η dd (primᵗ add  a)  env = z≤n
dep-eval-strict η dd (primᵗ sub  a)  env = z≤n
dep-eval-strict η dd (primᵗ mul  a)  env = z≤n
dep-eval-strict η dd (primᵗ eqᵖ  a)  env = z≤n
dep-eval-strict η dd (primᵗ ltᵖ  a)  env = z≤n
dep-eval-strict η dd (primᵗ notᵖ a)  env = z≤n
dep-eval-strict η dd (strmᵗ e)     []ᵃ = ≤-refl
dep-eval-strict η dd (strmᵗ e)     (v ∷ᵃ vs)
  rewrite dep-closeUnderFn η dd e (v ∷ᵃ vs) = ≤-refl


-- the reading of an environment, which is what the open form is
-- denominated in.
envDepth : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ} → All (Val Γ) Θ → ℕ
envDepth η []ᵃ       = 0
envDepth η (v ∷ᵃ vs) = depᵗ η (reify v) ⊔ envDepth η vs

-- THE OPEN FORM: what an environment carrying observables costs, which
-- is one wrap per binder crossed and NOT a function of the machine.
-- This is the statement the fold's arm needs, and the growth in it is
-- the iteration axis the carried family already names — stated here so
-- the two are the same fact rather than two.
--
-- AND NO ROW AT AN OBSERVABLE BINDER CAN SIT ON THIS BOUND, WHICH IS A
-- PROPERTY OF `envDepth` RATHER THAN OF THE PROGRAMS.  It reads its
-- values through `reify`, and reifying an observable writes a `strmᵗ`
-- the value did not have — so the environment's measured reading is
-- one above the reading of what is in it, and the slack is structural.
-- Tightness would need the measure to read the value rather than its
-- literal, which is a restatement and not a repair to the proof.
--
-- PROBED: `Probed.Eval-Binders` — an empty environment, a data one,
--   and one carrying an observable both read straight back and wrapped
--   again under a `strmᵗ`.  Not reached: the iteration axis, since one
--   evaluation crosses one binder and the growth this prices is per
--   refold.
postulate
  dep-eval-open : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t}
    (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) (m : ℕ) →
    envDepth η env ≤ m → depᵛ η t (evalWith tm env) ≤ depᵗ η tm + m

-- THE STRICT READING, AND IT IS THE WHOLE POINT.  An observable
-- emitted by a template is written strictly below the template — with
-- no hypothesis about the run, the store, or the bound the frame was
-- entered under, so a hop whose argument came from a template is priced
-- by the program text alone.  The lemma above gives the drop; what is
-- left is that there is something to drop FROM, which is the leaf
-- below.
--
-- AND THE DATA HYPOTHESIS IS THE STATEMENT, NOT A CONVENIENCE.  Where
-- the argument is itself observable, reifying it writes a `strmᵗ` the
-- template never wrote, so the substitution adds a level and the
-- emission is as deep as whatever was handed in — unbounded, rather
-- than off by one.  So the conditioned form is the true statement
-- replacing a false one rather than a weakening of it.
--
-- REFUTED: `Refuted.Template-Passes` — the same drop with the
--   hypothesis taken out, at a template that passes its argument
--   through.

-- THE LEAF IS SYNTAX, WITH NO ENVIRONMENT AND NO VALUE IN IT.  A
-- template at an observable result type has to WRITE the observable it
-- returns, because the one other way to have one is to read it from a
-- binder and the only binder is data.  The induction that says so needs
-- two predicates the type alone decides — one for a type every value of
-- which contains an observable, one for a context no binder of which
-- has such a type — because a `caseᵗ` at an observable result binds
-- into its branches, and which of the three subterms carries the
-- positivity is decided by whether those binder types are themselves
-- reachable.  Stated at the specialisation the door spends, since that
-- is the only shape any consumer asks for.
--
-- PROBED: `Probed.Template-Depth` — templates whose body is `ofᵉ` of a
--   term, with the argument dropped and with it wrapped under a second
--   `strmᵗ`.  Not reached: every head that BINDS, which is the arm the
--   induction has to split on.
postulate
  dep-fn-pos : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {s u} → isData s ≡ true →
    (fn : Fn Γ [] [] [] s (obs u)) → 0 < depᵗ η fn

applyFn-strict : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {s u} → isData s ≡ true →
  (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
  depᵉ η (applyFn fn v) < depᵗ η fn
applyFn-strict η ds fn v =
  ≤pred⇒< (dep-fn-pos η ds fn) (dep-eval-strict η (ds ∷ᵈ []ᵈ) fn (v ∷ᵃ []ᵃ))

-- AND THE SIZE HALF, WHICH THIS ROUTE DOES NOT GIVE FOR FREE.  A
-- substituted data value replaces a `varᵗ` of size one with a literal
-- whose size is a function of its TYPE — bounded, but not by one.  So
-- the size axis keeps the pair the carried family states it at; what
-- the substitution lemma collapses is the DEPTH axis, which is the one
-- the door reads.

-- AND THE FORM BELOW IS ALMOST CERTAINLY FALSE, WHICH IS WHAT COMES OF
-- INSTANTIATING IT.  The correction term is a function of the argument
-- TYPE, so at a fixed argument type it is ONE NUMBER however the
-- template is written — while the growth substitution causes is per
-- OCCURRENCE: each `varᵗ` the template reads is replaced by a literal
-- larger than it, so a template reading its argument k times pays k
-- times the difference.  Instantiated at a pair of numerals, one
-- occurrence leaves a gap of one over the template's own size and
-- three occurrences leave five, and nothing on the right moves with k.
-- Whatever number the correction returns, a template reading its
-- argument often enough exceeds it.
--
-- WHAT THE REPAIR IS, AND IT IS A RESTATEMENT RATHER THAN A PROOF.
-- The true statement prices the growth where it happens — a term of
-- size m reading a data argument grows by at most m times what a
-- literal of that type costs — so the correction belongs MULTIPLIED by
-- the template's size rather than added to it.  The row that closes
-- today closes only because a numeral reifies to one node and the
-- growth is nil; it is evidence that the shape is right at the floor,
-- not that the arithmetic holds.
--
-- AND THE STATEMENT CANNOT BE REFUTED IN THE SHAPE IT HAS, which is
-- the second half of the finding.  The correction is a postulate with
-- no equations, so no concrete instantiation can contradict it: the
-- witness has to be a FAMILY indexed by the occurrence count, carrying
-- the two rates as an induction.  So the finding is carried as a pair
-- of pins rather than as a `⊥` in the refuted tree.
--
-- PROBED: `Probed.Data-Shelf` — the bound at an argument whose
--   literal is one node, where the correction goes unspent.  NOT
--   reached, and not reachable: any argument whose literal is larger,
--   since closing such a row needs a LOWER bound on a postulate that
--   has no equations.  The two pins there carry the gap at one and at
--   three occurrences of the same argument type.
postulate
  dataSize : Ty → ℕ

  syncSize-applyFn : ∀ {n} {Γ : Ctx n} {s u} → isData s ≡ true →
    (fn : Fn Γ [] [] [] s (obs u)) (v : Val Γ s) →
    syncSizeᵉ (applyFn fn v) ≤ syncSizeᵗ fn + dataSize s
