------------------------------------------------------------------
-- WHAT A TEMPLATE EMITS IS READ OFF THE TEMPLATE AT THE BOUND ITS
-- ENVIRONMENT WAS HANDED IN AT.
--
-- `evalWith tm env` produces a value, and the reading of that value is
-- bounded by the reading of `tm` — provided the reading of `tm` is
-- taken at a bound the environment satisfies.  That proviso is the
-- whole of what this module adds over a closed reading, and it is what
-- makes the statement unconditional in the environment: there is no
-- premise that the binders carry data, because a binder carrying an
-- observable is priced rather than excluded.
--
-- THE DROP IS STRICT AT AN OBSERVABLE AND WEAK EVERYWHERE ELSE, AND
-- MEASURING THE RESULT THROUGH `reify` MAKES THOSE ONE INEQUALITY.
-- The reading wanted at the door is strict, and a statement about the
-- VALUE cannot say so without a `pred` and a positivity premise every
-- caller then has to spend.  `reify` writes a `strmᵗ` at an observable
-- and nothing anywhere else, so the wrap sits on the left exactly
-- where the head that produced it sits on the right: the two cases
-- become one statement, the strictness falls out by reduction at the
-- only type that wants it, and no clause carries a premise at all.
-- It also composes, which is the other half of why it is the right
-- form: `envDepth` is denominated through `reify` too, so the
-- rebinding arm's grown environment is this statement joined with the
-- caller's premise.
--
-- THE TWO ARMS THAT MAKE THEIR OWN ENVIRONMENT PAY FOR IT IN THE BOUND
-- AND NOT IN A PREMISE.  A `caseᵗ` binds what its scrutinee evaluated
-- to, so its branches run under an environment the caller never held;
-- a `strmᵗ` under a non-empty environment substitutes rather than
-- evaluates, so its body is read after the environment has been pushed
-- through it.  Neither is an exception here.  The first is the
-- reading's own composing clause, which hands the branches the larger
-- bound; the second is the substitution lemma below, whose whole
-- content is that pushing an environment bounded by `m` into a term
-- read at `m` cannot make it deeper.
--
-- TWIN: `Rx.Obs-Depth.dep-elimG` — the same commutation for the
--   guarded substitution, clause for clause, equality and not a bound.
--   That one substitutes a closed EXPRESSION for a μ-variable; this one
--   substitutes a value environment for the Θ-variables, and it is an
--   INEQUALITY because the environment's own reading is what it spends.
module Rx.Obs-Depth.Substitution where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ⊔-mono-≤; m≤m⊔n; m≤n⊔m; m≤n+m; n≤1+n; +-suc; +-distribˡ-⊔)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val; _×ᵗ_; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ;
  caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ; reify; wkTm; lookupEnv; subΘExp;
  subΘTm; subΘTms; evalWith)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ; bindᵃᵗ; bindᵃᵉ; bindˢᵗ)

------------------------------------------------------------------
-- 1.  THE READING IS MONOTONE IN ITS BOUND.
------------------------------------------------------------------

-- Every clause is either constant in the bound or hands it down, and
-- the one clause that CHANGES it — the rebinding arm — builds the new
-- bound monotonically out of the old.  So the whole induction is
-- `⊔-mono-≤` over the clause shapes, and it is needed because a term
-- read at nought and the same term read at a caller's bound are two
-- different numbers wherever the term is closed.
private
  -- a join under a common shift, which is how every non-leaf clause of
  -- the shift below lands
  ⊔-shift : ∀ d {p x y} → p ≤ (d + x) ⊔ (d + y) → p ≤ d + (x ⊔ y)
  ⊔-shift d {x = x} {y = y} le =
    ≤-trans le (≤-reflexive (sym (+-distribˡ-⊔ d x y)))

mutual
  dep-monoᵉ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} {k m : ℕ} → k ≤ m →
    (e : Exp Γ Δᵍ Δ Θ t) → depᵉ η k e ≤ depᵉ η m e
  dep-monoᵉ η km (input i)       = ≤-refl
  dep-monoᵉ η km (ofᵉ ts)        = dep-monoᵗˢ η km ts
  dep-monoᵉ η km emptyᵉ          = ≤-refl
  dep-monoᵉ η km (mapᵉ f e)      =
    ⊔-mono-≤ (dep-monoᵗ η (⊔-mono-≤ (dep-monoᵉ η km e) km) f) (dep-monoᵉ η km e)
  dep-monoᵉ η km (takeᵉ c e)     =
    ⊔-mono-≤ (dep-monoᵗ η (⊔-mono-≤ (dep-monoᵉ η km e) km) c) (dep-monoᵉ η km e)
  dep-monoᵉ η km (scanᵉ f z e)   =
    ⊔-mono-≤ (⊔-mono-≤ (dep-monoᵗ η (⊔-mono-≤ (⊔-mono-≤ (dep-monoᵉ η km e) km)
                                              (dep-monoᵗ η km z)) f)
                       (dep-monoᵗ η km z))
             (dep-monoᵉ η km e)
  dep-monoᵉ η km (mergeAllᵉ _ e) = dep-monoᵉ η km e
  dep-monoᵉ η km (switchAllᵉ e)  = dep-monoᵉ η km e
  dep-monoᵉ η km (exhaustAllᵉ e) = dep-monoᵉ η km e
  dep-monoᵉ η km (μᵉ e)          = dep-monoᵉ η km e
  dep-monoᵉ η km (varᵉ x)        = ≤-refl
  dep-monoᵉ η km (deferᵉ e)      = ≤-refl

  dep-monoᵗ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} {k m : ℕ} → k ≤ m →
    (f : Tm Γ Δᵍ Δ Θ t) → depᵗ η k f ≤ depᵗ η m f
  dep-monoᵗ η km (varᵗ x)      = km
  dep-monoᵗ η km unit̂          = ≤-refl
  dep-monoᵗ η km (bool̂ b)      = ≤-refl
  dep-monoᵗ η km (nat̂ j)       = ≤-refl
  dep-monoᵗ η km (pairᵗ a b)   = ⊔-mono-≤ (dep-monoᵗ η km a) (dep-monoᵗ η km b)
  dep-monoᵗ η km (fstᵗ p)      = dep-monoᵗ η km p
  dep-monoᵗ η km (sndᵗ p)      = dep-monoᵗ η km p
  dep-monoᵗ η km (inlᵗ a)      = dep-monoᵗ η km a
  dep-monoᵗ η km (inrᵗ a)      = dep-monoᵗ η km a
  dep-monoᵗ η km (caseᵗ sc l r) =
    ⊔-mono-≤ (dep-monoᵗ η b l) (dep-monoᵗ η b r)
    where b = ⊔-mono-≤ (s≤s (dep-monoᵗ η km sc)) km
  dep-monoᵗ η km (ifᵗ c a b)   =
    ⊔-mono-≤ (⊔-mono-≤ (dep-monoᵗ η km c) (dep-monoᵗ η km a)) (dep-monoᵗ η km b)
  dep-monoᵗ η km (primᵗ op a)  = dep-monoᵗ η km a
  dep-monoᵗ η km (strmᵗ e)     = s≤s (dep-monoᵉ η km e)

  dep-monoᵗˢ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} {k m : ℕ} → k ≤ m →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → depᵗˢ η k ts ≤ depᵗˢ η m ts
  dep-monoᵗˢ η km []       = ≤-refl
  dep-monoᵗˢ η km (y ∷ ys) = ⊔-mono-≤ (dep-monoᵗ η km y) (dep-monoᵗˢ η km ys)


-- AND IT IS LIPSCHITZ IN THE BOUND, WHICH IS WHAT LINEARISES A FOLD.
-- Monotonicity says a larger bound reads no smaller; this says by how
-- much, and the answer is "by at most the increase".  Every clause
-- either ignores the bound, returns it, or joins — and a join commutes
-- with the shift — while the rebinding arm's own bound is built out of
-- the old one by a successor and a join, both of which shift the same
-- way.  A fold re-enters its template with what it last wrote, so
-- without this the climb over a burst is a bound nested once per
-- delivery rather than a rate times a length.
mutual
  dep-shiftᵉ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} (d k : ℕ)
    (e : Exp Γ Δᵍ Δ Θ t) → depᵉ η (d + k) e ≤ d + depᵉ η k e
  dep-shiftᵉ η d k (input i)       = m≤n+m (η i) d
  dep-shiftᵉ η d k (ofᵉ ts)        = dep-shiftᵗˢ η d k ts
  dep-shiftᵉ η d k emptyᵉ          = z≤n
  dep-shiftᵉ η d k (mapᵉ f e)      =
    ⊔-shift d (⊔-mono-≤ (≤-trans (dep-monoᵗ η (bindᵉ-shift η d k e) f)
                                 (dep-shiftᵗ η d (bindᵃᵉ η k e) f))
                        (dep-shiftᵉ η d k e))
  dep-shiftᵉ η d k (takeᵉ c e)     =
    ⊔-shift d (⊔-mono-≤ (≤-trans (dep-monoᵗ η (bindᵉ-shift η d k e) c)
                                 (dep-shiftᵗ η d (bindᵃᵉ η k e) c))
                        (dep-shiftᵉ η d k e))
  dep-shiftᵉ η d k (scanᵉ f z e)   =
    ⊔-shift d (⊔-mono-≤ (⊔-shift d (⊔-mono-≤ (≤-trans (dep-monoᵗ η bnd f)
                                                (dep-shiftᵗ η d (bindˢᵗ η k z e) f))
                                             (dep-shiftᵗ η d k z)))
                        (dep-shiftᵉ η d k e))
    where
    bnd : bindˢᵗ η (d + k) z e ≤ d + bindˢᵗ η k z e
    bnd = ≤-trans (⊔-mono-≤ (bindᵉ-shift η d k e) (dep-shiftᵗ η d k z))
                  (≤-reflexive (sym (+-distribˡ-⊔ d (bindᵃᵉ η k e) (depᵗ η k z))))
  dep-shiftᵉ η d k (mergeAllᵉ _ e) = dep-shiftᵉ η d k e
  dep-shiftᵉ η d k (switchAllᵉ e)  = dep-shiftᵉ η d k e
  dep-shiftᵉ η d k (exhaustAllᵉ e) = dep-shiftᵉ η d k e
  dep-shiftᵉ η d k (μᵉ e)          = dep-shiftᵉ η d k e
  dep-shiftᵉ η d k (varᵉ x)        = z≤n
  dep-shiftᵉ η d k (deferᵉ e)      = z≤n

  dep-shiftᵗ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} (d k : ℕ)
    (f : Tm Γ Δᵍ Δ Θ t) → depᵗ η (d + k) f ≤ d + depᵗ η k f
  dep-shiftᵗ η d k (varᵗ x)      = ≤-refl
  dep-shiftᵗ η d k unit̂          = z≤n
  dep-shiftᵗ η d k (bool̂ b)      = z≤n
  dep-shiftᵗ η d k (nat̂ j)       = z≤n
  dep-shiftᵗ η d k (pairᵗ a b)   =
    ⊔-shift d (⊔-mono-≤ (dep-shiftᵗ η d k a) (dep-shiftᵗ η d k b))
  dep-shiftᵗ η d k (fstᵗ p)      = dep-shiftᵗ η d k p
  dep-shiftᵗ η d k (sndᵗ p)      = dep-shiftᵗ η d k p
  dep-shiftᵗ η d k (inlᵗ a)      = dep-shiftᵗ η d k a
  dep-shiftᵗ η d k (inrᵗ a)      = dep-shiftᵗ η d k a
  dep-shiftᵗ η d k (caseᵗ sc l r) =
    ⊔-shift d
      (⊔-mono-≤ (≤-trans (dep-monoᵗ η bnd l) (dep-shiftᵗ η d b l))
                (≤-trans (dep-monoᵗ η bnd r) (dep-shiftᵗ η d b r)))
    where
    b = bindᵃᵗ η k sc
    bnd : bindᵃᵗ η (d + k) sc ≤ d + b
    bnd = ≤-trans (⊔-mono-≤ (s≤s (dep-shiftᵗ η d k sc)) (≤-refl {d + k}))
                  (≤-reflexive (trans (cong (_⊔ (d + k))
                                        (sym (+-suc d (depᵗ η k sc))))
                                      (sym (+-distribˡ-⊔ d (suc (depᵗ η k sc)) k))))
  dep-shiftᵗ η d k (ifᵗ c a b)   =
    ⊔-shift d (⊔-mono-≤ (⊔-shift d (⊔-mono-≤ (dep-shiftᵗ η d k c)
                                             (dep-shiftᵗ η d k a)))
                        (dep-shiftᵗ η d k b))
  dep-shiftᵗ η d k (primᵗ op a)  = dep-shiftᵗ η d k a
  dep-shiftᵗ η d k (strmᵗ e)     =
    ≤-trans (s≤s (dep-shiftᵉ η d k e)) (≤-reflexive (sym (+-suc d (depᵉ η k e))))

  -- the template's bound shifts the way its two halves do
  bindᵉ-shift : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} (d k : ℕ)
    (e : Exp Γ Δᵍ Δ Θ t) → bindᵃᵉ η (d + k) e ≤ d + bindᵃᵉ η k e
  bindᵉ-shift η d k e =
    ≤-trans (⊔-mono-≤ (dep-shiftᵉ η d k e) (≤-refl {d + k}))
            (≤-reflexive (sym (+-distribˡ-⊔ d (depᵉ η k e) k)))

  dep-shiftᵗˢ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θ t} (d k : ℕ)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → depᵗˢ η (d + k) ts ≤ d + depᵗˢ η k ts
  dep-shiftᵗˢ η d k []       = z≤n
  dep-shiftᵗˢ η d k (y ∷ ys) =
    ⊔-shift d (⊔-mono-≤ (dep-shiftᵗ η d k y) (dep-shiftᵗˢ η d k ys))

------------------------------------------------------------------
-- 2.  WHAT AN ENVIRONMENT IS WORTH.
------------------------------------------------------------------

-- the reading of an environment, which is what every bound below is
-- denominated in.  It measures each value through `reify`, so it sits
-- one wrap above the reading of what is in it; the slack runs the safe
-- way, since a larger `envDepth` is a HARDER premise everywhere it is
-- one.
envDepth : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ} → All (Val Γ) Θ → ℕ
envDepth η []ᵃ       = 0
envDepth η (v ∷ᵃ vs) = depᵗ η 0 (reify v) ⊔ envDepth η vs

lookup-below : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t}
  (σ : All (Val Γ) Θ) (x : t ∈ Θ) →
  depᵗ η 0 (reify (lookupEnv σ x)) ≤ envDepth η σ
lookup-below η (v ∷ᵃ vs) (here refl) = m≤m⊔n _ _
lookup-below η (v ∷ᵃ vs) (there p)   = ≤-trans (lookup-below η vs p) (m≤n⊔m _ _)

------------------------------------------------------------------
-- 3.  THE TWO SIDES OF `reify`, WHICH IS WHAT THE ENVIRONMENT
--     READING AND THE VALUE READING DIFFER BY.
------------------------------------------------------------------

-- `envDepth` prices a value through `reify` and `ValOK` reads the value
-- itself, so a statement whose premise is an environment and whose
-- conclusion is a payload crosses between them twice -- once on the way
-- in and once on the way out.  The gap is exactly one wrap and it is
-- structural: `reify` at an observable writes a `strmᵗ` the value does
-- not have, and writes nothing at any other type.  So these are not
-- separate lemmas about `reify` but the directions of one, and a fold
-- needs both, because the value it hands back becomes the environment
-- of the next delivery.
------------------------------------------------------------------
-- 4.  PUSHING AN ENVIRONMENT IN CANNOT MAKE A TERM DEEPER.
------------------------------------------------------------------

-- weakening writes no head, so it moves no reading — and a Θ-closed
-- term reaches no variable clause, so the bound it is read at is
-- irrelevant.  Stated for the exact instance the substitution's `varᵗ`
-- arm produces rather than for a general renaming, because that arm is
-- the only consumer.
--
-- PROBED: `Probed.Data-Shelf` — a leaf, and a term whose head is
--   `strmᵗ`, which is the only head the reading counts and so the only
--   one a renaming could move.  Not reached: a term with a binder
--   under the weakened context.
postulate
  dep-wkTm : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (k : ℕ) {Δᵍ Δ Θ t}
    (f : Tm Γ [] [] [] t) →
    depᵗ η k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} f) ≡ depᵗ η 0 f

-- Every clause but two is `⊔-mono-≤` over the sub-derivations, exactly
-- as `dep-elimG`'s are `cong`.  The `varᵗ` clause splits the way
-- `subΘTm` splits: a LOCAL binder survives as a `varᵗ` and is read at
-- `k` on the left against `m` on the right, while a SUBSTITUTED binder
-- becomes a reified literal whose reading the environment's own bound
-- already covers.  The `caseᵗ` clause is where the two bounds move
-- together: substitution pushes the same environment into the
-- scrutinee and both branches, so the branches' bound on the left is
-- built from the SUBSTITUTED scrutinee and on the right from the
-- original, and the scrutinee's own induction is what relates them.
mutual
  dep-subΘ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (m k : ℕ) → envDepth η σ ≤ m → k ≤ m →
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    depᵉ η k (subΘExp Θloc σ e) ≤ depᵉ η m e
  dep-subΘ η Θloc σ m k h km (input i)       = ≤-refl
  dep-subΘ η Θloc σ m k h km (ofᵉ ts)        = dep-subΘᵗˢ η Θloc σ m k h km ts
  dep-subΘ η Θloc σ m k h km emptyᵉ          = ≤-refl
  dep-subΘ η Θloc σ m k h km (mapᵉ {s = s} f e) =
    ⊔-mono-≤ (dep-subΘᵗ η (s ∷ Θloc) σ (bindᵃᵉ η m e)
                (bindᵃᵉ η k (subΘExp Θloc σ e))
                (≤-trans h (m≤n⊔m (depᵉ η m e) m))
                (⊔-mono-≤ (dep-subΘ η Θloc σ m k h km e) km) f)
             (dep-subΘ η Θloc σ m k h km e)
  dep-subΘ η Θloc σ m k h km (takeᵉ c e)     =
    ⊔-mono-≤ (dep-subΘᵗ η Θloc σ (bindᵃᵉ η m e)
                (bindᵃᵉ η k (subΘExp Θloc σ e))
                (≤-trans h (m≤n⊔m (depᵉ η m e) m))
                (⊔-mono-≤ (dep-subΘ η Θloc σ m k h km e) km) c)
             (dep-subΘ η Θloc σ m k h km e)
  dep-subΘ η Θloc σ m k h km (scanᵉ {s = s} {t = t} f z e) =
    ⊔-mono-≤ (⊔-mono-≤ (dep-subΘᵗ η ((t ×ᵗ s) ∷ Θloc) σ (bindˢᵗ η m z e)
                          (bindˢᵗ η k (subΘTm Θloc σ z) (subΘExp Θloc σ e))
                          (≤-trans h (≤-trans (m≤n⊔m (depᵉ η m e) m)
                                              (m≤m⊔n (bindᵃᵉ η m e) (depᵗ η m z))))
                          (⊔-mono-≤ (⊔-mono-≤ (dep-subΘ η Θloc σ m k h km e) km)
                                    (dep-subΘᵗ η Θloc σ m k h km z)) f)
                       (dep-subΘᵗ η Θloc σ m k h km z))
             (dep-subΘ η Θloc σ m k h km e)
  dep-subΘ η Θloc σ m k h km (mergeAllᵉ _ e) = dep-subΘ η Θloc σ m k h km e
  dep-subΘ η Θloc σ m k h km (switchAllᵉ e)  = dep-subΘ η Θloc σ m k h km e
  dep-subΘ η Θloc σ m k h km (exhaustAllᵉ e) = dep-subΘ η Θloc σ m k h km e
  dep-subΘ η Θloc σ m k h km (μᵉ e)          = dep-subΘ η Θloc σ m k h km e
  dep-subΘ η Θloc σ m k h km (varᵉ x)        = ≤-refl
  dep-subΘ η Θloc σ m k h km (deferᵉ e)      = ≤-refl

  dep-subΘᵗ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (m k : ℕ) → envDepth η σ ≤ m → k ≤ m →
    (f : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    depᵗ η k (subΘTm Θloc σ f) ≤ depᵗ η m f
  dep-subΘᵗ η Θloc σ m k h km (varᵗ x) with ∈-++⁻ Θloc x
  ... | inj₁ y = km
  ... | inj₂ z = ≤-trans (≤-reflexive (dep-wkTm η k (reify (lookupEnv σ z))))
                         (≤-trans (lookup-below η σ z) h)
  dep-subΘᵗ η Θloc σ m k h km unit̂          = ≤-refl
  dep-subΘᵗ η Θloc σ m k h km (bool̂ b)      = ≤-refl
  dep-subΘᵗ η Θloc σ m k h km (nat̂ j)       = ≤-refl
  dep-subΘᵗ η Θloc σ m k h km (pairᵗ a b)   =
    ⊔-mono-≤ (dep-subΘᵗ η Θloc σ m k h km a) (dep-subΘᵗ η Θloc σ m k h km b)
  dep-subΘᵗ η Θloc σ m k h km (fstᵗ p)      = dep-subΘᵗ η Θloc σ m k h km p
  dep-subΘᵗ η Θloc σ m k h km (sndᵗ p)      = dep-subΘᵗ η Θloc σ m k h km p
  dep-subΘᵗ η Θloc σ m k h km (inlᵗ a)      = dep-subΘᵗ η Θloc σ m k h km a
  dep-subΘᵗ η Θloc σ m k h km (inrᵗ a)      = dep-subΘᵗ η Θloc σ m k h km a
  dep-subΘᵗ η Θloc σ m k h km (caseᵗ {s = s} {t = t} sc l r) =
    ⊔-mono-≤ (dep-subΘᵗ η (s ∷ Θloc) σ (bindᵃᵗ η m sc)
                (bindᵃᵗ η k (subΘTm Θloc σ sc)) h' b l)
             (dep-subΘᵗ η (t ∷ Θloc) σ (bindᵃᵗ η m sc)
                (bindᵃᵗ η k (subΘTm Θloc σ sc)) h' b r)
    where
    b : bindᵃᵗ η k (subΘTm Θloc σ sc) ≤ bindᵃᵗ η m sc
    b = ⊔-mono-≤ (s≤s (dep-subΘᵗ η Θloc σ m k h km sc)) km
    h' : envDepth η σ ≤ bindᵃᵗ η m sc
    h' = ≤-trans h (m≤n⊔m _ _)
  dep-subΘᵗ η Θloc σ m k h km (ifᵗ c a b)   =
    ⊔-mono-≤ (⊔-mono-≤ (dep-subΘᵗ η Θloc σ m k h km c)
                       (dep-subΘᵗ η Θloc σ m k h km a))
             (dep-subΘᵗ η Θloc σ m k h km b)
  dep-subΘᵗ η Θloc σ m k h km (primᵗ op a)  = dep-subΘᵗ η Θloc σ m k h km a
  dep-subΘᵗ η Θloc σ m k h km (strmᵗ e)     =
    s≤s (dep-subΘ η Θloc σ m k h km e)

  dep-subΘᵗˢ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (m k : ℕ) → envDepth η σ ≤ m → k ≤ m →
    (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    depᵗˢ η k (subΘTms Θloc σ ts) ≤ depᵗˢ η m ts
  dep-subΘᵗˢ η Θloc σ m k h km []       = ≤-refl
  dep-subΘᵗˢ η Θloc σ m k h km (y ∷ ys) =
    ⊔-mono-≤ (dep-subΘᵗ η Θloc σ m k h km y) (dep-subΘᵗˢ η Θloc σ m k h km ys)

------------------------------------------------------------------
-- 5.  EVALUATION, READ THROUGH `reify` SO THAT THE STRICT DROP AT AN
--     OBSERVABLE IS THE SAME STATEMENT AS THE WEAK ONE ELSEWHERE.
------------------------------------------------------------------

-- WHY THE CONCLUSION IS ABOUT `reify (evalWith …)` AND NOT ABOUT THE
-- VALUE.  A value read directly loses the one piece of information the
-- door needs: at an observable the literal carries a `strmᵗ` the value
-- does not, so the drop there is STRICT while it is weak everywhere
-- else, and a statement about the value has to say that with a `pred`
-- and then hand every caller a positivity premise to spend.  Measured
-- through `reify` the two cases are one inequality — the wrap is on
-- the left exactly where the head that produced it is on the right —
-- and the strictness falls out by reduction at the only type that
-- wants it.  It also composes: `envDepth` is itself denominated
-- through `reify`, so the rebinding arm's grown environment is this
-- statement joined with the caller's premise and nothing else.
--
-- Two clauses carry the content and the rest is `⊔` plumbing: the
-- rebinding arm, where the branch's environment gains the scrutinee's
-- value and the branch is read at the bound the measure's own clause
-- hands it; and the `strmᵗ` arm under a non-empty environment, where
-- the run SUBSTITUTES rather than evaluates and the lemma above pays.
dep-eval : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {Θ t}
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) (m : ℕ) →
  envDepth η env ≤ m → depᵗ η 0 (reify (evalWith tm env)) ≤ depᵗ η m tm
dep-eval η (varᵗ x)      env m h = ≤-trans (lookup-below η env x) h
dep-eval η unit̂          env m h = z≤n
dep-eval η (bool̂ b)      env m h = z≤n
dep-eval η (nat̂ j)       env m h = z≤n
dep-eval η (pairᵗ a b)   env m h =
  ⊔-mono-≤ (dep-eval η a env m h) (dep-eval η b env m h)
-- the pair's reading is the join of its components', so a projection
-- reads no more than the pair
dep-eval η (fstᵗ p)      env m h with evalWith p env | dep-eval η p env m h
... | (a , b) | ih = ≤-trans (m≤m⊔n _ _) ih
dep-eval η (sndᵗ p)      env m h with evalWith p env | dep-eval η p env m h
... | (a , b) | ih = ≤-trans (m≤n⊔m _ _) ih
dep-eval η (inlᵗ a)      env m h = dep-eval η a env m h
dep-eval η (inrᵗ a)      env m h = dep-eval η a env m h
dep-eval η (caseᵗ {s = s} {t = t} sc l r) env m h
  with evalWith sc env | dep-eval η sc env m h
... | inj₁ x | ih =
  ≤-trans (dep-eval η l (x ∷ᵃ env) (bindᵃᵗ η m sc)
             (⊔-mono-≤ (≤-trans ih (n≤1+n (depᵗ η m sc))) h))
          (m≤m⊔n (depᵗ η (bindᵃᵗ η m sc) l) (depᵗ η (bindᵃᵗ η m sc) r))
... | inj₂ y | ih =
  ≤-trans (dep-eval η r (y ∷ᵃ env) (bindᵃᵗ η m sc)
             (⊔-mono-≤ (≤-trans ih (n≤1+n (depᵗ η m sc))) h))
          (m≤n⊔m (depᵗ η (bindᵃᵗ η m sc) l) (depᵗ η (bindᵃᵗ η m sc) r))
dep-eval η (ifᵗ c a b)   env m h with evalWith c env
... | true  =
  ≤-trans (dep-eval η a env m h)
          (≤-trans (m≤n⊔m (depᵗ η m c) (depᵗ η m a))
                   (m≤m⊔n (depᵗ η m c ⊔ depᵗ η m a) (depᵗ η m b)))
... | false =
  ≤-trans (dep-eval η b env m h)
          (m≤n⊔m (depᵗ η m c ⊔ depᵗ η m a) (depᵗ η m b))
dep-eval η (primᵗ add  a)  env m h = z≤n
dep-eval η (primᵗ sub  a)  env m h = z≤n
dep-eval η (primᵗ mul  a)  env m h = z≤n
dep-eval η (primᵗ eqᵖ  a)  env m h = z≤n
dep-eval η (primᵗ ltᵖ  a)  env m h = z≤n
dep-eval η (primᵗ notᵖ a)  env m h = z≤n
dep-eval η (strmᵗ e)     []ᵃ       m h = s≤s (dep-monoᵉ η z≤n e)
dep-eval η (strmᵗ e)     (v ∷ᵃ vs) m h =
  s≤s (dep-subΘ η [] (v ∷ᵃ vs) m 0 h z≤n e)
