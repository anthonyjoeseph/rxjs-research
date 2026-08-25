------------------------------------------------------------------
-- WHAT SUBSTITUTION DOES TO THE NESTING MEASURE, AND WHAT EVALUATION
-- DOES ON TOP OF IT.  Two different arithmetics, and the difference is
-- the whole reason this module exists.
--
-- SUBSTITUTION IS LINEAR.  `subΘTm` replaces a `varᵗ` -- which the
-- measure charges zero -- by a reified environment value, and every
-- other constructor maps one-to-one.  So the measure grows by at most
-- one environment value's worth per occurrence, occurrences are
-- bounded by the term's own size, and the bound is `nestD e + size e *
-- N`.  Nothing here is exponential.
--
-- EVALUATION IS NOT, AND `caseᵗ` IS WHY.  Evaluating a case runs the
-- branch in an environment EXTENDED by the scrutinee's own value, so
-- the branch's linear factor multiplies the scrutinee's -- one product
-- per binder crossed, and binders nest.  A linear bound on `evalWith`
-- is therefore false at depth two; two to the size dominates it,
-- because the size counts the binders that could nest.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Subst where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; ≤-refl; <⇒≤; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm;
   *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; *-identityˡ; *-distribˡ-+; *-distribʳ-+;
   *-assoc; *-comm; ^-distribˡ-+-*;
   ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; n≤1+n; ^-monoʳ-≤; m^n>0)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Exp using
  (Ctx; Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Exp; Tm; Val; Fn; input; ofᵉ; emptyᵉ; mapᵉ;
  takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂;
  pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ; Ren∈;
  ext∈; renExp; renTm; renTms; reify; lookupEnv; subΘExp; subΘTm; subΘTms; evalWith; applyFn;
  sizeᵉ; sizeᵗ; sizeᵗˢ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵗˢ; nestDᵛ)
open import Verify-Budget-Sufficient.Measures using (n<2^n)
open import Verify-Budget-Sufficient.Nest-Store using (nest-inflate)

------------------------------------------------------------------
-- RENAMING IS INVISIBLE TO THE MEASURE, exactly as it is to the size:
-- every constructor maps one-to-one and no clause reads an index.
mutual
  nest-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → nestDᵉ (renExp ρg ρd ρt e) ≡ nestDᵉ e
  nest-renᵉ ρg ρd ρt (input i)       = refl
  nest-renᵉ ρg ρd ρt (ofᵉ ts)        = nest-renᵗˢ ρg ρd ρt ts
  nest-renᵉ ρg ρd ρt emptyᵉ          = refl
  nest-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _+_ (nest-renᵗ ρg ρd (ext∈ ρt) f) (nest-renᵉ ρg ρd ρt e)
  nest-renᵉ ρg ρd ρt (takeᵉ c e)     = nest-renᵉ ρg ρd ρt e
  nest-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _+_ (cong₂ _+_ (nest-renᵗ ρg ρd ρt z) (nest-renᵗ ρg ρd (ext∈ ρt) f))
              (nest-renᵉ ρg ρd ρt e)
  nest-renᵉ ρg ρd ρt (mergeAllᵉ _ e) = cong suc (nest-renᵉ ρg ρd ρt e)
  nest-renᵉ ρg ρd ρt (switchAllᵉ e)  = cong suc (nest-renᵉ ρg ρd ρt e)
  nest-renᵉ ρg ρd ρt (exhaustAllᵉ e) = cong suc (nest-renᵉ ρg ρd ρt e)
  nest-renᵉ ρg ρd ρt (μᵉ e)          = nest-renᵉ (ext∈ ρg) ρd ρt e
  nest-renᵉ ρg ρd ρt (varᵉ x)        = refl
  nest-renᵉ ρg ρd ρt (deferᵉ e)      = refl

  nest-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → nestDᵗ (renTm ρg ρd ρt tm) ≡ nestDᵗ tm
  nest-renᵗ ρg ρd ρt (varᵗ x)      = refl
  nest-renᵗ ρg ρd ρt unit̂          = refl
  nest-renᵗ ρg ρd ρt (bool̂ _)      = refl
  nest-renᵗ ρg ρd ρt (nat̂ _)       = refl
  nest-renᵗ ρg ρd ρt (pairᵗ a b)   =
    cong₂ _⊔_ (nest-renᵗ ρg ρd ρt a) (nest-renᵗ ρg ρd ρt b)
  nest-renᵗ ρg ρd ρt (fstᵗ p)      = nest-renᵗ ρg ρd ρt p
  nest-renᵗ ρg ρd ρt (sndᵗ p)      = nest-renᵗ ρg ρd ρt p
  nest-renᵗ ρg ρd ρt (inlᵗ a)      = nest-renᵗ ρg ρd ρt a
  nest-renᵗ ρg ρd ρt (inrᵗ a)      = nest-renᵗ ρg ρd ρt a
  nest-renᵗ ρg ρd ρt (caseᵗ s l r) =
    cong₂ _+_ (nest-renᵗ ρg ρd ρt s)
              (cong₂ _⊔_ (nest-renᵗ ρg ρd (ext∈ ρt) l) (nest-renᵗ ρg ρd (ext∈ ρt) r))
  nest-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _⊔_ (cong₂ _⊔_ (nest-renᵗ ρg ρd ρt c) (nest-renᵗ ρg ρd ρt a))
              (nest-renᵗ ρg ρd ρt b)
  nest-renᵗ ρg ρd ρt (primᵗ _ a)   = nest-renᵗ ρg ρd ρt a
  nest-renᵗ ρg ρd ρt (strmᵗ e)     = nest-renᵉ ρg ρd ρt e

  nest-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → nestDᵗˢ (renTms ρg ρd ρt ts) ≡ nestDᵗˢ ts
  nest-renᵗˢ ρg ρd ρt []       = refl
  nest-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _⊔_ (nest-renᵗ ρg ρd ρt y) (nest-renᵗˢ ρg ρd ρt ys)

-- REIFICATION IS EXACT, where the size face only gets a doubling: the
-- measure reads a pair by `⊔` and a value's pair the same way, and an
-- `obs` value IS the expression its reification carries.
nest-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  nestDᵗ (reify {t = t} v) ≡ nestDᵛ t v
nest-reify unitᵗ    _        = refl
nest-reify boolᵗ    _        = refl
nest-reify natᵗ     _        = refl
nest-reify (s ×ᵗ t) (a , b)  = cong₂ _⊔_ (nest-reify s a) (nest-reify t b)
nest-reify (s +ᵗ t) (inj₁ a) = nest-reify s a
nest-reify (s +ᵗ t) (inj₂ b) = nest-reify t b
nest-reify (obs t)  e        = refl

------------------------------------------------------------------
-- THE ENVIRONMENT CAP.  One number for the whole environment, in the
-- shape `EnvSize` already has on the size face.
EnvNest : ∀ {n} {Γ : Ctx n} {Θ} (N : ℕ) → All (Val Γ) Θ → Set
EnvNest N []ᵃ                = ⊤
EnvNest N (_∷ᵃ_ {x = t} v σ) = (nestDᵛ t v ≤ N) × EnvNest N σ

envNest-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (N : ℕ) (σ : All (Val Γ) Θ) →
  EnvNest N σ → (z : t ∈ Θ) → nestDᵛ t (lookupEnv σ z) ≤ N
envNest-lookup N (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envNest-lookup N (v ∷ᵃ σ) (hv , hσ) (there z)   = envNest-lookup N σ hσ z

------------------------------------------------------------------
-- SUBSTITUTION, LINEARLY.  Three shapes carry every clause: a
-- constructor whose measure ADDS its subterms distributes the size sum,
-- one whose measure takes their `⊔` takes the `⊔` of the two bounds and
-- then widens both sizes, and a `varᵗ` that has been hit pays one
-- environment value against its own size of one.
sum⊔ : ∀ {A B} (a b sa sb N : ℕ) → A ≤ a + sa * N → B ≤ b + sb * N →
  A ⊔ B ≤ (a ⊔ b) + (sa + sb) * N
sum⊔ {A} {B} a b sa sb N pa pb =
  ⊔-lub (≤-trans pa (+-mono-≤ (m≤m⊔n a b)
                              (*-monoˡ-≤ N (m≤m+n sa sb))))
        (≤-trans pb (+-mono-≤ (m≤n⊔m a b)
                              (*-monoˡ-≤ N (m≤n+m sb sa))))

sum+ : ∀ {A B} (a b sa sb N : ℕ) → A ≤ a + sa * N → B ≤ b + sb * N →
  A + B ≤ (a + b) + (sa + sb) * N
sum+ {A} {B} a b sa sb N pa pb =
  ≤-trans (+-mono-≤ pa pb)
    (≤-reflexive (trans (+-assoc a (sa * N) (b + sb * N))
      (trans (cong (a +_) (trans (sym (+-assoc (sa * N) b (sb * N)))
                            (trans (cong (_+ sb * N) (+-comm (sa * N) b))
                                   (+-assoc b (sa * N) (sb * N)))))
        (trans (sym (+-assoc a b (sa * N + sb * N)))
               (cong ((a + b) +_) (sym (*-distribʳ-+ N sa sb)))))))

mutual
  nest-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (N : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) → EnvNest N σ →
    nestDᵉ (subΘExp Θloc σ e) ≤ nestDᵉ e + sizeᵉ e * N
  nest-subΘᵉ N Θloc σ (input i)   hσ = z≤n
  nest-subΘᵉ N Θloc σ (ofᵉ ts)    hσ =
    ≤-trans (nest-subΘᵗˢ N Θloc σ ts hσ)
            (+-monoʳ-≤ (nestDᵗˢ ts) (*-monoˡ-≤ N (n≤1+n (sizeᵗˢ ts))))
  nest-subΘᵉ N Θloc σ emptyᵉ      hσ = z≤n
  nest-subΘᵉ N Θloc σ (mapᵉ {s = s} f e) hσ =
    ≤-trans (sum+ (nestDᵗ f) (nestDᵉ e) (sizeᵗ f) (sizeᵉ e) N
                  (nest-subΘᵗ N (s ∷ Θloc) σ f hσ) (nest-subΘᵉ N Θloc σ e hσ))
            (+-monoʳ-≤ (nestDᵗ f + nestDᵉ e)
                       (*-monoˡ-≤ N (m≤n+m (sizeᵗ f + sizeᵉ e) 1)))
  nest-subΘᵉ N Θloc σ (takeᵉ c e) hσ =
    ≤-trans (nest-subΘᵉ N Θloc σ e hσ)
            (+-monoʳ-≤ (nestDᵉ e)
                       (*-monoˡ-≤ N (≤-trans (m≤n+m (sizeᵉ e) (sizeᵗ c))
                                             (m≤n+m (sizeᵗ c + sizeᵉ e) 1))))
  nest-subΘᵉ N Θloc σ (scanᵉ {s = s} {t = t} f i e) hσ =
    ≤-trans (sum+ (nestDᵗ i + nestDᵗ f) (nestDᵉ e) (sizeᵗ f + sizeᵗ i) (sizeᵉ e) N
              (sum+′ (nestDᵗ i) (nestDᵗ f) (sizeᵗ i) (sizeᵗ f) N
                     (nest-subΘᵗ N Θloc σ i hσ)
                     (nest-subΘᵗ N ((t ×ᵗ s) ∷ Θloc) σ f hσ))
              (nest-subΘᵉ N Θloc σ e hσ))
            (+-monoʳ-≤ ((nestDᵗ i + nestDᵗ f) + nestDᵉ e)
                       (*-monoˡ-≤ N (m≤n+m ((sizeᵗ f + sizeᵗ i) + sizeᵉ e) 1)))
    where
    sum+′ : ∀ {A B} (a b sa sb N : ℕ) → A ≤ a + sa * N → B ≤ b + sb * N →
      A + B ≤ (a + b) + (sb + sa) * N
    sum+′ a b sa sb N pa pb =
      ≤-trans (sum+ a b sa sb N pa pb)
              (+-monoʳ-≤ (a + b) (*-monoˡ-≤ N (≤-reflexive (+-comm sa sb))))
  nest-subΘᵉ N Θloc σ (mergeAllᵉ lim e) hσ =
    s≤s (≤-trans (nest-subΘᵉ N Θloc σ e hσ)
                 (+-monoʳ-≤ (nestDᵉ e) (*-monoˡ-≤ N (n≤1+n (sizeᵉ e)))))
  nest-subΘᵉ N Θloc σ (switchAllᵉ e) hσ =
    s≤s (≤-trans (nest-subΘᵉ N Θloc σ e hσ)
                 (+-monoʳ-≤ (nestDᵉ e) (*-monoˡ-≤ N (n≤1+n (sizeᵉ e)))))
  nest-subΘᵉ N Θloc σ (exhaustAllᵉ e) hσ =
    s≤s (≤-trans (nest-subΘᵉ N Θloc σ e hσ)
                 (+-monoʳ-≤ (nestDᵉ e) (*-monoˡ-≤ N (n≤1+n (sizeᵉ e)))))
  nest-subΘᵉ N Θloc σ (μᵉ e)      hσ =
    ≤-trans (nest-subΘᵉ N Θloc σ e hσ)
            (+-monoʳ-≤ (nestDᵉ e) (*-monoˡ-≤ N (m≤n+m (sizeᵉ e) 1)))
  nest-subΘᵉ N Θloc σ (varᵉ x)    hσ = z≤n
  nest-subΘᵉ N Θloc σ (deferᵉ e)  hσ = z≤n

  nest-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (N : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) → EnvNest N σ →
    nestDᵗ (subΘTm Θloc σ tm) ≤ nestDᵗ tm + sizeᵗ tm * N
  nest-subΘᵗ N Θloc σ (varᵗ x) hσ with ∈-++⁻ Θloc x
  ... | inj₁ y = z≤n
  ... | inj₂ z =
    ≤-trans (≤-reflexive (trans (nest-renᵗ (λ ()) (λ ()) (λ ()) (reify (lookupEnv σ z)))
                                (nest-reify _ (lookupEnv σ z))))
            (≤-trans (envNest-lookup N σ hσ z)
                     (≤-reflexive (sym (*-identityˡ N))))
  nest-subΘᵗ N Θloc σ unit̂     hσ = z≤n
  nest-subΘᵗ N Θloc σ (bool̂ _) hσ = z≤n
  nest-subΘᵗ N Θloc σ (nat̂ _)  hσ = z≤n
  nest-subΘᵗ N Θloc σ (pairᵗ a b) hσ =
    ≤-trans (sum⊔ (nestDᵗ a) (nestDᵗ b) (sizeᵗ a) (sizeᵗ b) N
                  (nest-subΘᵗ N Θloc σ a hσ) (nest-subΘᵗ N Θloc σ b hσ))
            (+-monoʳ-≤ (nestDᵗ a ⊔ nestDᵗ b)
                       (*-monoˡ-≤ N (m≤n+m (sizeᵗ a + sizeᵗ b) 1)))
  nest-subΘᵗ N Θloc σ (fstᵗ p) hσ =
    ≤-trans (nest-subΘᵗ N Θloc σ p hσ)
            (+-monoʳ-≤ (nestDᵗ p) (*-monoˡ-≤ N (m≤n+m (sizeᵗ p) 1)))
  nest-subΘᵗ N Θloc σ (sndᵗ p) hσ =
    ≤-trans (nest-subΘᵗ N Θloc σ p hσ)
            (+-monoʳ-≤ (nestDᵗ p) (*-monoˡ-≤ N (m≤n+m (sizeᵗ p) 1)))
  nest-subΘᵗ N Θloc σ (inlᵗ a) hσ =
    ≤-trans (nest-subΘᵗ N Θloc σ a hσ)
            (+-monoʳ-≤ (nestDᵗ a) (*-monoˡ-≤ N (m≤n+m (sizeᵗ a) 1)))
  nest-subΘᵗ N Θloc σ (inrᵗ a) hσ =
    ≤-trans (nest-subΘᵗ N Θloc σ a hσ)
            (+-monoʳ-≤ (nestDᵗ a) (*-monoˡ-≤ N (m≤n+m (sizeᵗ a) 1)))
  nest-subΘᵗ N Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ =
    ≤-trans (sum+ (nestDᵗ sc) (nestDᵗ l ⊔ nestDᵗ r) (sizeᵗ sc) (sizeᵗ l + sizeᵗ r) N
                  (nest-subΘᵗ N Θloc σ sc hσ)
                  (sum⊔ (nestDᵗ l) (nestDᵗ r) (sizeᵗ l) (sizeᵗ r) N
                        (nest-subΘᵗ N (s ∷ Θloc) σ l hσ)
                        (nest-subΘᵗ N (t ∷ Θloc) σ r hσ)))
            (+-monoʳ-≤ (nestDᵗ sc + (nestDᵗ l ⊔ nestDᵗ r))
                       (*-monoˡ-≤ N (≤-trans (≤-reflexive (sym (+-assoc (sizeᵗ sc) (sizeᵗ l) (sizeᵗ r))))
                                             (m≤n+m ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r) 1))))
  nest-subΘᵗ N Θloc σ (ifᵗ c a b) hσ =
    ≤-trans (sum⊔ (nestDᵗ c ⊔ nestDᵗ a) (nestDᵗ b) (sizeᵗ c + sizeᵗ a) (sizeᵗ b) N
                  (sum⊔ (nestDᵗ c) (nestDᵗ a) (sizeᵗ c) (sizeᵗ a) N
                        (nest-subΘᵗ N Θloc σ c hσ) (nest-subΘᵗ N Θloc σ a hσ))
                  (nest-subΘᵗ N Θloc σ b hσ))
            (+-monoʳ-≤ ((nestDᵗ c ⊔ nestDᵗ a) ⊔ nestDᵗ b)
                       (*-monoˡ-≤ N (m≤n+m ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) 1)))
  nest-subΘᵗ N Θloc σ (primᵗ op a) hσ =
    ≤-trans (nest-subΘᵗ N Θloc σ a hσ)
            (+-monoʳ-≤ (nestDᵗ a) (*-monoˡ-≤ N (m≤n+m (sizeᵗ a) 1)))
  nest-subΘᵗ N Θloc σ (strmᵗ e) hσ =
    ≤-trans (nest-subΘᵉ N Θloc σ e hσ)
            (+-monoʳ-≤ (nestDᵉ e) (*-monoˡ-≤ N (m≤n+m (sizeᵉ e) 1)))

  nest-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (N : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) → EnvNest N σ →
    nestDᵗˢ (subΘTms Θloc σ ts) ≤ nestDᵗˢ ts + sizeᵗˢ ts * N
  nest-subΘᵗˢ N Θloc σ []       hσ = z≤n
  nest-subΘᵗˢ N Θloc σ (y ∷ ys) hσ =
    sum⊔ (nestDᵗ y) (nestDᵗˢ ys) (sizeᵗ y) (sizeᵗˢ ys) N
         (nest-subΘᵗ N Θloc σ y hσ) (nest-subΘᵗˢ N Θloc σ ys hσ)

------------------------------------------------------------------
-- AND EVALUATION, WHERE THE FACTOR COMES FROM.  Four arithmetic steps
-- carry every clause: widening a subterm's exponent and its base,
-- lifting a bound into a scaled one, the `caseᵗ` product, and the one
-- place a linear substitution bound is absorbed into an exponential.
scale : ∀ (k A : ℕ) → A ≤ 2 ^ k * A
scale k A = nest-inflate (2 ^ k) A (m^n>0 2 k)

pow-grow : ∀ (j k A B : ℕ) → j ≤ k → A ≤ B → 2 ^ j * A ≤ 2 ^ k * B
pow-grow j k A B hj hA = *-mono-≤ (^-monoʳ-≤ 2 hj) hA

-- the branch's factor multiplies the scrutinee's, which is the whole
-- reason this face is exponential and the substitution face is not
case-step : ∀ (ss sl nl ns N : ℕ) →
  2 ^ sl * (nl + 2 ^ ss * (ns + N)) ≤ 2 ^ (ss + sl) * ((ns + nl) + N)
case-step ss sl nl ns N =
  ≤-trans (*-monoʳ-≤ (2 ^ sl) inner) (≤-reflexive outer)
  where
  inner : nl + 2 ^ ss * (ns + N) ≤ 2 ^ ss * ((ns + nl) + N)
  inner =
    ≤-trans (+-monoˡ-≤ (2 ^ ss * (ns + N)) (scale ss nl))
      (≤-trans (≤-reflexive (sym (*-distribˡ-+ (2 ^ ss) nl (ns + N))))
        (*-monoʳ-≤ (2 ^ ss)
          (≤-reflexive (trans (sym (+-assoc nl ns N))
                              (cong (_+ N) (+-comm nl ns))))))
  outer : 2 ^ sl * (2 ^ ss * ((ns + nl) + N)) ≡ 2 ^ (ss + sl) * ((ns + nl) + N)
  outer =
    trans (sym (*-assoc (2 ^ sl) (2 ^ ss) ((ns + nl) + N)))
          (cong (_* ((ns + nl) + N))
                (trans (*-comm (2 ^ sl) (2 ^ ss))
                       (sym (^-distribˡ-+-* 2 ss sl))))

strm-step : ∀ (se ne N : ℕ) → ne + se * N ≤ 2 ^ suc se * (ne + N)
strm-step se ne N =
  ≤-trans (+-mono-≤ (scale (suc se) ne)
                    (*-monoˡ-≤ N (≤-trans (<⇒≤ (n<2^n se)) (^-monoʳ-≤ 2 (n≤1+n se)))))
          (≤-reflexive (sym (*-distribˡ-+ (2 ^ suc se) ne N)))

envNest-mono : ∀ {n} {Γ : Ctx n} {Θ} (N N′ : ℕ) (σ : All (Val Γ) Θ) →
  EnvNest N σ → N ≤ N′ → EnvNest N′ σ
envNest-mono N N′ []ᵃ      tt        h = tt
envNest-mono N N′ (v ∷ᵃ σ) (hv , hσ) h = ≤-trans hv h , envNest-mono N N′ σ hσ h

evalWith-nest : ∀ {n} {Γ : Ctx n} {Θ t} (N : ℕ)
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) → EnvNest N env →
  nestDᵛ t (evalWith tm env) ≤ 2 ^ sizeᵗ tm * (nestDᵗ tm + N)
evalWith-nest N (varᵗ x)  env hσ =
  ≤-trans (envNest-lookup N env hσ x) (scale 1 N)
evalWith-nest N unit̂      env hσ = z≤n
evalWith-nest N (bool̂ _)  env hσ = z≤n
evalWith-nest N (nat̂ _)   env hσ = z≤n
evalWith-nest N (pairᵗ {s = s} {t = t} a b) env hσ =
  ⊔-lub (≤-trans (evalWith-nest N a env hσ)
                 (pow-grow (sizeᵗ a) (suc (sizeᵗ a + sizeᵗ b)) _ _
                   (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b)) (n≤1+n _))
                   (+-monoˡ-≤ N (m≤m⊔n (nestDᵗ a) (nestDᵗ b)))))
        (≤-trans (evalWith-nest N b env hσ)
                 (pow-grow (sizeᵗ b) (suc (sizeᵗ a + sizeᵗ b)) _ _
                   (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a)) (n≤1+n _))
                   (+-monoˡ-≤ N (m≤n⊔m (nestDᵗ a) (nestDᵗ b)))))
evalWith-nest N (fstᵗ {s = s} {t = t} p) env hσ
  with evalWith p env | evalWith-nest N p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (m≤m⊔n (nestDᵛ s a) (nestDᵛ t b)) ih)
          (pow-grow (sizeᵗ p) (suc (sizeᵗ p)) _ _ (n≤1+n _) ≤-refl)
evalWith-nest N (sndᵗ {s = s} {t = t} p) env hσ
  with evalWith p env | evalWith-nest N p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (m≤n⊔m (nestDᵛ s a) (nestDᵛ t b)) ih)
          (pow-grow (sizeᵗ p) (suc (sizeᵗ p)) _ _ (n≤1+n _) ≤-refl)
evalWith-nest N (inlᵗ a) env hσ =
  ≤-trans (evalWith-nest N a env hσ)
          (pow-grow (sizeᵗ a) (suc (sizeᵗ a)) _ _ (n≤1+n _) ≤-refl)
evalWith-nest N (inrᵗ a) env hσ =
  ≤-trans (evalWith-nest N a env hσ)
          (pow-grow (sizeᵗ a) (suc (sizeᵗ a)) _ _ (n≤1+n _) ≤-refl)
evalWith-nest N (caseᵗ {s = s} {t = t} sc l r) env hσ
  with evalWith sc env | evalWith-nest N sc env hσ
... | inj₁ x | ih =
  ≤-trans (≤-trans (evalWith-nest N′ l (x ∷ᵃ env) (ih , envNest-mono N N′ env hσ N≤N′))
                   (case-step (sizeᵗ sc) (sizeᵗ l) (nestDᵗ l) (nestDᵗ sc) N))
          (pow-grow (sizeᵗ sc + sizeᵗ l) (suc ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r)) _ _
            (≤-trans (m≤m+n _ (sizeᵗ r)) (n≤1+n _))
            (+-monoˡ-≤ N (+-monoʳ-≤ (nestDᵗ sc) (m≤m⊔n (nestDᵗ l) (nestDᵗ r)))))
  where
  N′ = 2 ^ sizeᵗ sc * (nestDᵗ sc + N)
  N≤N′ : N ≤ N′
  N≤N′ = ≤-trans (m≤n+m N (nestDᵗ sc)) (scale (sizeᵗ sc) (nestDᵗ sc + N))
... | inj₂ y | ih =
  ≤-trans (≤-trans (evalWith-nest N′ r (y ∷ᵃ env) (ih , envNest-mono N N′ env hσ N≤N′))
                   (case-step (sizeᵗ sc) (sizeᵗ r) (nestDᵗ r) (nestDᵗ sc) N))
          (pow-grow (sizeᵗ sc + sizeᵗ r) (suc ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r)) _ _
            (≤-trans (+-monoʳ-≤ (sizeᵗ sc) (m≤n+m (sizeᵗ r) (sizeᵗ l)))
              (≤-trans (≤-reflexive (sym (+-assoc (sizeᵗ sc) (sizeᵗ l) (sizeᵗ r)))) (n≤1+n _)))
            (+-monoˡ-≤ N (+-monoʳ-≤ (nestDᵗ sc) (m≤n⊔m (nestDᵗ l) (nestDᵗ r)))))
  where
  N′ = 2 ^ sizeᵗ sc * (nestDᵗ sc + N)
  N≤N′ : N ≤ N′
  N≤N′ = ≤-trans (m≤n+m N (nestDᵗ sc)) (scale (sizeᵗ sc) (nestDᵗ sc + N))
evalWith-nest N (ifᵗ c a b) env hσ with evalWith c env
... | true =
  ≤-trans (evalWith-nest N a env hσ)
          (pow-grow (sizeᵗ a) (suc ((sizeᵗ c + sizeᵗ a) + sizeᵗ b)) _ _
            (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c)) (≤-trans (m≤m+n _ (sizeᵗ b)) (n≤1+n _)))
            (+-monoˡ-≤ N (≤-trans (m≤n⊔m (nestDᵗ c) (nestDᵗ a))
                                  (m≤m⊔n (nestDᵗ c ⊔ nestDᵗ a) (nestDᵗ b)))))
... | false =
  ≤-trans (evalWith-nest N b env hσ)
          (pow-grow (sizeᵗ b) (suc ((sizeᵗ c + sizeᵗ a) + sizeᵗ b)) _ _
            (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a)) (n≤1+n _))
            (+-monoˡ-≤ N (m≤n⊔m (nestDᵗ c ⊔ nestDᵗ a) (nestDᵗ b))))
evalWith-nest N (primᵗ add arg)  env hσ = z≤n
evalWith-nest N (primᵗ sub arg)  env hσ = z≤n
evalWith-nest N (primᵗ mul arg)  env hσ = z≤n
evalWith-nest N (primᵗ eqᵖ arg)  env hσ = z≤n
evalWith-nest N (primᵗ ltᵖ arg)  env hσ = z≤n
evalWith-nest N (primᵗ notᵖ arg) env hσ = z≤n
evalWith-nest N (strmᵗ e) []ᵃ       hσ =
  ≤-trans (m≤m+n (nestDᵉ e) N) (scale (suc (sizeᵉ e)) (nestDᵉ e + N))
evalWith-nest N (strmᵗ e) (v ∷ᵃ vs) hσ =
  ≤-trans (nest-subΘᵉ N [] (v ∷ᵃ vs) e hσ) (strm-step (sizeᵉ e) (nestDᵉ e) N)

-- WHAT THE WALK ACTUALLY SPENDS: one payload, one step function, and
-- the factor is why the map frame's charge is a power rather than a
-- summand -- a step function may name its payload once per occurrence,
-- and a variable weighs nothing before the substitution.
--
-- REFUTED: `Refuted.Apply-Fn-Nest` kills the additive form -- two
--   against one, at a step function naming its payload on both sides
--   of one `mapᵉ`.
applyFn-nest : ∀ {n} {Γ : Ctx n} {s u}
  (fn : Fn Γ [] [] [] s u) (v : Val Γ s) →
  nestDᵛ u (applyFn fn v) ≤ 2 ^ sizeᵗ fn * (nestDᵗ fn + nestDᵛ s v)
applyFn-nest {s = s} fn v =
  evalWith-nest (nestDᵛ s v) fn (v ∷ᵃ []ᵃ) (≤-refl , tt)
