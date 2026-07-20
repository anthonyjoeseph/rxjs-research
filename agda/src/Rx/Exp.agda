module Rx.Exp where

open import Data.Nat     using (ℕ; suc; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Bool    using (Bool; true; false; not; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Vec     using (Vec; lookup)
open import Data.Fin     using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)


------------------------------------------------------------------
-- Types (sums included, for Either/error and sentinel patterns)
------------------------------------------------------------------

data Ty : Set where
  unitᵗ boolᵗ natᵗ : Ty
  _×ᵗ_ _+ᵗ_ : Ty → Ty → Ty
  obs : Ty → Ty

Ctx : ℕ → Set
Ctx n = Vec Ty n

-- concrete now (the JSON bridge fixes exactly this set): the binary ops
-- take a pair; sub is ℕ monus; eq/lt compare nats
data PrimOp : Ty → Ty → Set where
  add sub mul : PrimOp (natᵗ ×ᵗ natᵗ) natᵗ
  eqᵖ ltᵖ     : PrimOp (natᵗ ×ᵗ natᵗ) boolᵗ
  notᵖ        : PrimOp boolᵗ boolᵗ


------------------------------------------------------------------
-- Syntax.  Contexts: Γ inputs, Δᵍ guarded μ-vars, Δ usable μ-vars,
-- Θ value vars.  μᵉ binds into Δᵍ; deferᵉ is the sole gate moving
-- Δᵍ into scope — synchronous self-reference is a type error.
------------------------------------------------------------------

mutual

  data Exp {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    input      : (i : Fin n) → Exp Γ Δᵍ Δ Θ (lookup Γ i)
    ofᵉ        : ∀ {t} → List (Tm Γ Δᵍ Δ Θ t) → Exp Γ Δᵍ Δ Θ t
    emptyᵉ     : ∀ {t} → Exp Γ Δᵍ Δ Θ t
    mapᵉ       : ∀ {s t} → Fn Γ Δᵍ Δ Θ s t → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
    takeᵉ      : ∀ {t} → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ t
                 -- count is a term: evaluated once, at subscription time
    scanᵉ      : ∀ {s t} → Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t → Tm Γ Δᵍ Δ Θ t
               → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
               -- NOTE: share is NOT an Exp primitive — share identity is a
               -- binding, not an expression.  Shared observables live in the
               -- slot telescope (Rx.Evaluator.Slot) and are referenced with
               -- `input`, exactly like scripted inputs
    mergeAllᵉ concatAllᵉ switchAllᵉ exhaustAllᵉ :
                 ∀ {t} → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
    μᵉ         : ∀ {t} → Exp Γ (t ∷ Δᵍ) Δ Θ t → Exp Γ Δᵍ Δ Θ t
    varᵉ       : ∀ {t} → t ∈ Δ → Exp Γ Δᵍ Δ Θ t
    deferᵉ     : ∀ {t} → Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t
                 -- subscribe at tick k ⇒ body subscribed at k+1, fresh ids

  data Tm {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    varᵗ  : ∀ {t} → t ∈ Θ → Tm Γ Δᵍ Δ Θ t
    unit̂  : Tm Γ Δᵍ Δ Θ unitᵗ
    bool̂  : Bool → Tm Γ Δᵍ Δ Θ boolᵗ
    nat̂   : ℕ → Tm Γ Δᵍ Δ Θ natᵗ
    pairᵗ : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s ×ᵗ t)
    fstᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ s
    sndᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ t
    inlᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    inrᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    caseᵗ : ∀ {s t u} → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
          → Tm Γ Δᵍ Δ (s ∷ Θ) u → Tm Γ Δᵍ Δ (t ∷ Θ) u → Tm Γ Δᵍ Δ Θ u
    ifᵗ   : ∀ {t} → Tm Γ Δᵍ Δ Θ boolᵗ → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ t
          → Tm Γ Δᵍ Δ Θ t
    primᵗ : ∀ {s t} → PrimOp s t → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t
    strmᵗ : ∀ {t} → Exp Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (obs t)

  Fn : ∀ {n} → Ctx n → List Ty → List Ty → List Ty → Ty → Ty → Set
  Fn Γ Δᵍ Δ Θ s t = Tm Γ Δᵍ Δ (s ∷ Θ) t

  Val : ∀ {n} → Ctx n → Ty → Set
  Val Γ unitᵗ    = ⊤
  Val Γ boolᵗ    = Bool
  Val Γ natᵗ     = ℕ
  Val Γ (s ×ᵗ t) = Val Γ s × Val Γ t
  Val Γ (s +ᵗ t) = Val Γ s ⊎ Val Γ t
  Val Γ (obs t)  = Exp Γ [] [] [] t     -- runtime observables are closed exprs

Closed : ∀ {n} → Ctx n → Ty → Set
Closed Γ t = Exp Γ [] [] [] t

-- decidable type equality (the evaluator admits a chain only past a Ty
-- match, so no payload is ever read at the wrong type)
_≟ᵗ_ : (s t : Ty) → Dec (s ≡ t)
unitᵗ ≟ᵗ unitᵗ = yes refl
boolᵗ ≟ᵗ boolᵗ = yes refl
natᵗ  ≟ᵗ natᵗ  = yes refl
(a ×ᵗ b) ≟ᵗ (c ×ᵗ d) with a ≟ᵗ c | b ≟ᵗ d
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬p    = no λ { refl → ¬p refl }
(a +ᵗ b) ≟ᵗ (c +ᵗ d) with a ≟ᵗ c | b ≟ᵗ d
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬p    = no λ { refl → ¬p refl }
obs a ≟ᵗ obs c with a ≟ᵗ c
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
unitᵗ    ≟ᵗ boolᵗ    = no λ ()
unitᵗ    ≟ᵗ natᵗ     = no λ ()
unitᵗ    ≟ᵗ (_ ×ᵗ _) = no λ ()
unitᵗ    ≟ᵗ (_ +ᵗ _) = no λ ()
unitᵗ    ≟ᵗ obs _    = no λ ()
boolᵗ    ≟ᵗ unitᵗ    = no λ ()
boolᵗ    ≟ᵗ natᵗ     = no λ ()
boolᵗ    ≟ᵗ (_ ×ᵗ _) = no λ ()
boolᵗ    ≟ᵗ (_ +ᵗ _) = no λ ()
boolᵗ    ≟ᵗ obs _    = no λ ()
natᵗ     ≟ᵗ unitᵗ    = no λ ()
natᵗ     ≟ᵗ boolᵗ    = no λ ()
natᵗ     ≟ᵗ (_ ×ᵗ _) = no λ ()
natᵗ     ≟ᵗ (_ +ᵗ _) = no λ ()
natᵗ     ≟ᵗ obs _    = no λ ()
(_ ×ᵗ _) ≟ᵗ unitᵗ    = no λ ()
(_ ×ᵗ _) ≟ᵗ boolᵗ    = no λ ()
(_ ×ᵗ _) ≟ᵗ natᵗ     = no λ ()
(_ ×ᵗ _) ≟ᵗ (_ +ᵗ _) = no λ ()
(_ ×ᵗ _) ≟ᵗ obs _    = no λ ()
(_ +ᵗ _) ≟ᵗ unitᵗ    = no λ ()
(_ +ᵗ _) ≟ᵗ boolᵗ    = no λ ()
(_ +ᵗ _) ≟ᵗ natᵗ     = no λ ()
(_ +ᵗ _) ≟ᵗ (_ ×ᵗ _) = no λ ()
(_ +ᵗ _) ≟ᵗ obs _    = no λ ()
obs _    ≟ᵗ unitᵗ    = no λ ()
obs _    ≟ᵗ boolᵗ    = no λ ()
obs _    ≟ᵗ natᵗ     = no λ ()
obs _    ≟ᵗ (_ ×ᵗ _) = no λ ()
obs _    ≟ᵗ (_ +ᵗ _) = no λ ()

-- one Θ value-environment lookup, indexed by the de Bruijn membership proof
lookupEnv : ∀ {n} {Γ : Ctx n} {Θ t} → All (Val Γ) Θ → t ∈ Θ → Val Γ t
lookupEnv (v ∷ᵃ _)  (here refl) = v
lookupEnv (_ ∷ᵃ vs) (there p)   = lookupEnv vs p

------------------------------------------------------------------
-- Renaming: re-index a term into wider μ-var (Δᵍ, Δ) and value-var (Θ)
-- contexts. A membership map per context; extended under binders; the
-- deferᵉ clause moves Δᵍ into Δ, so its Δ-renaming is the ++-congruence.
------------------------------------------------------------------

Ren∈ : List Ty → List Ty → Set
Ren∈ xs ys = ∀ {u} → u ∈ xs → u ∈ ys

ext∈ : ∀ {xs ys s} → Ren∈ xs ys → Ren∈ (s ∷ xs) (s ∷ ys)
ext∈ ρ (here refl) = here refl
ext∈ ρ (there x)   = there (ρ x)

++Ren : ∀ {A A′ B B′} → Ren∈ A A′ → Ren∈ B B′ → Ren∈ (A ++ B) (A′ ++ B′)
++Ren {A} {A′} ρa ρb x with ∈-++⁻ A x
... | inj₁ y = ∈-++⁺ˡ (ρa y)
... | inj₂ z = ∈-++⁺ʳ A′ (ρb z)

mutual
  renExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
         → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
         → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ′ Δ′ Θ′ t
  renExp ρg ρd ρt (input i)      = input i
  renExp ρg ρd ρt (ofᵉ ts)       = ofᵉ (renTms ρg ρd ρt ts)
  renExp ρg ρd ρt emptyᵉ         = emptyᵉ
  renExp ρg ρd ρt (mapᵉ f e)     = mapᵉ (renTm ρg ρd (ext∈ ρt) f) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (takeᵉ n e)    = takeᵉ (renTm ρg ρd ρt n) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (scanᵉ f i e)  = scanᵉ (renTm ρg ρd (ext∈ ρt) f) (renTm ρg ρd ρt i) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (mergeAllᵉ e)  = mergeAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (concatAllᵉ e) = concatAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (switchAllᵉ e) = switchAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (exhaustAllᵉ e) = exhaustAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (μᵉ e)         = μᵉ (renExp (ext∈ ρg) ρd ρt e)
  renExp ρg ρd ρt (varᵉ x)       = varᵉ (ρd x)
  renExp ρg ρd ρt (deferᵉ e)     = deferᵉ (renExp (λ ()) (++Ren ρg ρd) ρt e)

  renTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
        → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
        → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ′ Δ′ Θ′ t
  renTm ρg ρd ρt (varᵗ x)     = varᵗ (ρt x)
  renTm ρg ρd ρt unit̂         = unit̂
  renTm ρg ρd ρt (bool̂ b)     = bool̂ b
  renTm ρg ρd ρt (nat̂ n)      = nat̂ n
  renTm ρg ρd ρt (pairᵗ a b)  = pairᵗ (renTm ρg ρd ρt a) (renTm ρg ρd ρt b)
  renTm ρg ρd ρt (fstᵗ p)     = fstᵗ (renTm ρg ρd ρt p)
  renTm ρg ρd ρt (sndᵗ p)     = sndᵗ (renTm ρg ρd ρt p)
  renTm ρg ρd ρt (inlᵗ a)     = inlᵗ (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (inrᵗ a)     = inrᵗ (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (caseᵗ s l r) = caseᵗ (renTm ρg ρd ρt s) (renTm ρg ρd (ext∈ ρt) l) (renTm ρg ρd (ext∈ ρt) r)
  renTm ρg ρd ρt (ifᵗ c a b)  = ifᵗ (renTm ρg ρd ρt c) (renTm ρg ρd ρt a) (renTm ρg ρd ρt b)
  renTm ρg ρd ρt (primᵗ op a) = primᵗ op (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (strmᵗ e)    = strmᵗ (renExp ρg ρd ρt e)

  renTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
         → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
         → List (Tm Γ Δᵍ Δ Θ t) → List (Tm Γ Δᵍ′ Δ′ Θ′ t)
  renTms ρg ρd ρt []       = []
  renTms ρg ρd ρt (x ∷ xs) = renTm ρg ρd ρt x ∷ renTms ρg ρd ρt xs

-- weaken a closed term into any context (source contexts empty)
wkTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ [] [] [] t → Tm Γ Δᵍ Δ Θ t
wkTm = renTm (λ ()) (λ ()) (λ ())

-- the postulated Δᵍ-weakening, now a definition
wkᵍ : ∀ {n} {Γ : Ctx n} {g Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Exp Γ (g ∷ Δᵍ) Δ Θ t
wkᵍ = renExp there (λ x → x) (λ x → x)

------------------------------------------------------------------
-- reify: a value → the closed Tm literal denoting it (an obs value is
-- already a closed Exp, so no substitution)
------------------------------------------------------------------

reify : ∀ {n} {Γ : Ctx n} {t} → Val Γ t → Tm Γ [] [] [] t
reify {t = unitᵗ}   _        = unit̂
reify {t = boolᵗ}   b        = bool̂ b
reify {t = natᵗ}    n        = nat̂ n
reify {t = _ ×ᵗ _}  (a , b)  = pairᵗ (reify a) (reify b)
reify {t = _ +ᵗ _}  (inj₁ a) = inlᵗ (reify a)
reify {t = _ +ᵗ _}  (inj₂ b) = inrᵗ (reify b)
reify {t = obs _}   e        = strmᵗ e

------------------------------------------------------------------
-- closeUnderFn: substitute a Θ value-environment into a term, closing
-- the whole environment. A varᵗ in the local binders (Θloc) stays; one
-- naming an environment value is reified (closed) and weakened in.
------------------------------------------------------------------

mutual
  subΘExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
          → All (Val Γ) Θsub → Exp Γ Δᵍ Δ (Θloc ++ Θsub) t → Exp Γ Δᵍ Δ Θloc t
  subΘExp Θloc σ (input i)      = input i
  subΘExp Θloc σ (ofᵉ ts)       = ofᵉ (subΘTms Θloc σ ts)
  subΘExp Θloc σ emptyᵉ         = emptyᵉ
  subΘExp Θloc σ (mapᵉ {s = s} f e) = mapᵉ (subΘTm (s ∷ Θloc) σ f) (subΘExp Θloc σ e)
  subΘExp Θloc σ (takeᵉ n e)    = takeᵉ (subΘTm Θloc σ n) (subΘExp Θloc σ e)
  subΘExp Θloc σ (scanᵉ {s = s} {t = t} f i e) =
    scanᵉ (subΘTm ((t ×ᵗ s) ∷ Θloc) σ f) (subΘTm Θloc σ i) (subΘExp Θloc σ e)
  subΘExp Θloc σ (mergeAllᵉ e)  = mergeAllᵉ (subΘExp Θloc σ e)
  subΘExp Θloc σ (concatAllᵉ e) = concatAllᵉ (subΘExp Θloc σ e)
  subΘExp Θloc σ (switchAllᵉ e) = switchAllᵉ (subΘExp Θloc σ e)
  subΘExp Θloc σ (exhaustAllᵉ e) = exhaustAllᵉ (subΘExp Θloc σ e)
  subΘExp Θloc σ (μᵉ e)         = μᵉ (subΘExp Θloc σ e)
  subΘExp Θloc σ (varᵉ x)       = varᵉ x
  subΘExp Θloc σ (deferᵉ e)     = deferᵉ (subΘExp Θloc σ e)

  subΘTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
         → All (Val Γ) Θsub → Tm Γ Δᵍ Δ (Θloc ++ Θsub) t → Tm Γ Δᵍ Δ Θloc t
  subΘTm Θloc σ (varᵗ x) with ∈-++⁻ Θloc x
  ... | inj₁ y = varᵗ y
  ... | inj₂ z = wkTm (reify (lookupEnv σ z))
  subΘTm Θloc σ unit̂         = unit̂
  subΘTm Θloc σ (bool̂ b)     = bool̂ b
  subΘTm Θloc σ (nat̂ n)      = nat̂ n
  subΘTm Θloc σ (pairᵗ a b)  = pairᵗ (subΘTm Θloc σ a) (subΘTm Θloc σ b)
  subΘTm Θloc σ (fstᵗ p)     = fstᵗ (subΘTm Θloc σ p)
  subΘTm Θloc σ (sndᵗ p)     = sndᵗ (subΘTm Θloc σ p)
  subΘTm Θloc σ (inlᵗ a)     = inlᵗ (subΘTm Θloc σ a)
  subΘTm Θloc σ (inrᵗ a)     = inrᵗ (subΘTm Θloc σ a)
  subΘTm Θloc σ (caseᵗ {s = s} {t = t} sc l r) =
    caseᵗ (subΘTm Θloc σ sc) (subΘTm (s ∷ Θloc) σ l) (subΘTm (t ∷ Θloc) σ r)
  subΘTm Θloc σ (ifᵗ c a b)  = ifᵗ (subΘTm Θloc σ c) (subΘTm Θloc σ a) (subΘTm Θloc σ b)
  subΘTm Θloc σ (primᵗ op a) = primᵗ op (subΘTm Θloc σ a)
  subΘTm Θloc σ (strmᵗ e)    = strmᵗ (subΘExp Θloc σ e)

  subΘTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
          → All (Val Γ) Θsub → List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) → List (Tm Γ Δᵍ Δ Θloc t)
  subΘTms Θloc σ []       = []
  subΘTms Θloc σ (x ∷ xs) = subΘTm Θloc σ x ∷ subΘTms Θloc σ xs

closeUnderFn : ∀ {n} {Γ : Ctx n} {s Θ t}
             → Exp Γ [] [] (s ∷ Θ) t → All (Val Γ) (s ∷ Θ) → Exp Γ [] [] [] t
closeUnderFn e env = subΘExp [] env e

------------------------------------------------------------------
-- unfoldμ: substitute the (closed) `μᵉ body` for the μ-var this μ binds.
-- The var starts alone in Δᵍ and is READ only as a varᵉ (in Δ), reachable
-- only past a deferᵉ that moved Δᵍ into Δ. So we eliminate it, tracking
-- whether it currently sits in Δᵍ (elimG) or has migrated into Δ (elimD),
-- and drop it from that context. The deferᵉ shuffle needs two context
-- identities — proofs, left as postulates per the behavior/proof split.
------------------------------------------------------------------

-- remove the pointed element from a context
_⊟_ : ∀ {A : Set} (xs : List A) {x : A} → x ∈ xs → List A
(_ ∷ xs) ⊟ here _  = xs
(y ∷ xs) ⊟ there p = y ∷ (xs ⊟ p)

-- proven (not postulated): a postulate here would be an abstract proof,
-- and subst on it would BLOCK evaluation — these must reduce to refl on
-- concrete indices for a μ-program to compute
⊟-++ˡ : ∀ {Δᵍ Δ : List Ty} {t} (x : t ∈ Δᵍ)
      → (Δᵍ ++ Δ) ⊟ (∈-++⁺ˡ {ys = Δ} x) ≡ (Δᵍ ⊟ x) ++ Δ
⊟-++ˡ (here refl) = refl
⊟-++ˡ (there {x = g} x) = cong (g ∷_) (⊟-++ˡ x)

⊟-++ʳ : ∀ {Δᵍ Δ : List Ty} {t} (x : t ∈ Δ)
      → (Δᵍ ++ Δ) ⊟ (∈-++⁺ʳ Δᵍ x) ≡ Δᵍ ++ (Δ ⊟ x)
⊟-++ʳ {Δᵍ = []}     x = refl
⊟-++ʳ {Δᵍ = g ∷ _}  x = cong (g ∷_) (⊟-++ʳ x)

wkExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ [] [] [] t → Exp Γ Δᵍ Δ Θ t
wkExp = renExp (λ ()) (λ ()) (λ ())

-- compare two positions: inj₁ ⟺ the same position (types coincide);
-- inj₂ ⟺ y sits at this position once x is removed
compare∈ : ∀ {A : Set} {t u : A} {xs} (x : t ∈ xs) (y : u ∈ xs)
         → (t ≡ u) ⊎ (u ∈ (xs ⊟ x))
compare∈ (here refl) (here refl) = inj₁ refl
compare∈ (here refl) (there y)   = inj₂ y
compare∈ (there x)   (here refl) = inj₂ (here refl)
compare∈ (there x)   (there y)   with compare∈ x y
... | inj₁ eq = inj₁ eq
... | inj₂ y′ = inj₂ (there y′)

mutual
  elimGExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
           → Exp Γ [] [] [] t → Exp Γ Δᵍ Δ Θ u → Exp Γ (Δᵍ ⊟ x) Δ Θ u
  elimGExp x cl (input i)      = input i
  elimGExp x cl (ofᵉ ts)       = ofᵉ (elimGTms x cl ts)
  elimGExp x cl emptyᵉ         = emptyᵉ
  elimGExp x cl (mapᵉ f e)     = mapᵉ (elimGTm x cl f) (elimGExp x cl e)
  elimGExp x cl (takeᵉ n e)    = takeᵉ (elimGTm x cl n) (elimGExp x cl e)
  elimGExp x cl (scanᵉ f i e)  = scanᵉ (elimGTm x cl f) (elimGTm x cl i) (elimGExp x cl e)
  elimGExp x cl (mergeAllᵉ e)  = mergeAllᵉ (elimGExp x cl e)
  elimGExp x cl (concatAllᵉ e) = concatAllᵉ (elimGExp x cl e)
  elimGExp x cl (switchAllᵉ e) = switchAllᵉ (elimGExp x cl e)
  elimGExp x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimGExp x cl e)
  elimGExp x cl (μᵉ e)         = μᵉ (elimGExp (there x) cl e)
  elimGExp x cl (varᵉ y)       = varᵉ y
  elimGExp x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e))

  elimGTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
          → Exp Γ [] [] [] t → Tm Γ Δᵍ Δ Θ u → Tm Γ (Δᵍ ⊟ x) Δ Θ u
  elimGTm x cl (varᵗ y)     = varᵗ y
  elimGTm x cl unit̂         = unit̂
  elimGTm x cl (bool̂ b)     = bool̂ b
  elimGTm x cl (nat̂ n)      = nat̂ n
  elimGTm x cl (pairᵗ a b)  = pairᵗ (elimGTm x cl a) (elimGTm x cl b)
  elimGTm x cl (fstᵗ p)     = fstᵗ (elimGTm x cl p)
  elimGTm x cl (sndᵗ p)     = sndᵗ (elimGTm x cl p)
  elimGTm x cl (inlᵗ a)     = inlᵗ (elimGTm x cl a)
  elimGTm x cl (inrᵗ a)     = inrᵗ (elimGTm x cl a)
  elimGTm x cl (caseᵗ s l r) = caseᵗ (elimGTm x cl s) (elimGTm x cl l) (elimGTm x cl r)
  elimGTm x cl (ifᵗ c a b)  = ifᵗ (elimGTm x cl c) (elimGTm x cl a) (elimGTm x cl b)
  elimGTm x cl (primᵗ op a) = primᵗ op (elimGTm x cl a)
  elimGTm x cl (strmᵗ e)    = strmᵗ (elimGExp x cl e)

  elimGTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
           → Exp Γ [] [] [] t → List (Tm Γ Δᵍ Δ Θ u) → List (Tm Γ (Δᵍ ⊟ x) Δ Θ u)
  elimGTms x cl []       = []
  elimGTms x cl (y ∷ ys) = elimGTm x cl y ∷ elimGTms x cl ys

  elimDExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
           → Exp Γ [] [] [] t → Exp Γ Δᵍ Δ Θ u → Exp Γ Δᵍ (Δ ⊟ x) Θ u
  elimDExp x cl (input i)      = input i
  elimDExp x cl (ofᵉ ts)       = ofᵉ (elimDTms x cl ts)
  elimDExp x cl emptyᵉ         = emptyᵉ
  elimDExp x cl (mapᵉ f e)     = mapᵉ (elimDTm x cl f) (elimDExp x cl e)
  elimDExp x cl (takeᵉ n e)    = takeᵉ (elimDTm x cl n) (elimDExp x cl e)
  elimDExp x cl (scanᵉ f i e)  = scanᵉ (elimDTm x cl f) (elimDTm x cl i) (elimDExp x cl e)
  elimDExp x cl (mergeAllᵉ e)  = mergeAllᵉ (elimDExp x cl e)
  elimDExp x cl (concatAllᵉ e) = concatAllᵉ (elimDExp x cl e)
  elimDExp x cl (switchAllᵉ e) = switchAllᵉ (elimDExp x cl e)
  elimDExp x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimDExp x cl e)
  elimDExp x cl (μᵉ e)         = μᵉ (elimDExp x cl e)
  elimDExp x cl (varᵉ y)       with compare∈ x y
  ... | inj₁ refl = wkExp cl
  ... | inj₂ y′   = varᵉ y′
  elimDExp x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ʳ x) (elimDExp (∈-++⁺ʳ _ x) cl e))

  elimDTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
          → Exp Γ [] [] [] t → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ (Δ ⊟ x) Θ u
  elimDTm x cl (varᵗ y)     = varᵗ y
  elimDTm x cl unit̂         = unit̂
  elimDTm x cl (bool̂ b)     = bool̂ b
  elimDTm x cl (nat̂ n)      = nat̂ n
  elimDTm x cl (pairᵗ a b)  = pairᵗ (elimDTm x cl a) (elimDTm x cl b)
  elimDTm x cl (fstᵗ p)     = fstᵗ (elimDTm x cl p)
  elimDTm x cl (sndᵗ p)     = sndᵗ (elimDTm x cl p)
  elimDTm x cl (inlᵗ a)     = inlᵗ (elimDTm x cl a)
  elimDTm x cl (inrᵗ a)     = inrᵗ (elimDTm x cl a)
  elimDTm x cl (caseᵗ s l r) = caseᵗ (elimDTm x cl s) (elimDTm x cl l) (elimDTm x cl r)
  elimDTm x cl (ifᵗ c a b)  = ifᵗ (elimDTm x cl c) (elimDTm x cl a) (elimDTm x cl b)
  elimDTm x cl (primᵗ op a) = primᵗ op (elimDTm x cl a)
  elimDTm x cl (strmᵗ e)    = strmᵗ (elimDExp x cl e)

  elimDTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
           → Exp Γ [] [] [] t → List (Tm Γ Δᵍ Δ Θ u) → List (Tm Γ Δᵍ (Δ ⊟ x) Θ u)
  elimDTms x cl []       = []
  elimDTms x cl (y ∷ ys) = elimDTm x cl y ∷ elimDTms x cl ys

unfoldμ : ∀ {n} {Γ : Ctx n} {t} → Exp Γ (t ∷ []) [] [] t → Closed Γ t
unfoldμ body = elimGExp (here refl) (μᵉ body) body

-- the first-order evaluator, in a Θ value-environment; a closed strmᵗ IS
-- its (closed) observable, so obs values built outside a fn need no
-- substitution
evalWith : ∀ {n} {Γ : Ctx n} {Θ t} → Tm Γ [] [] Θ t → All (Val Γ) Θ → Val Γ t
evalWith (varᵗ x)      env = lookupEnv env x
evalWith unit̂          env = tt
evalWith (bool̂ b)      env = b
evalWith (nat̂ n)       env = n
evalWith (pairᵗ a b)   env = evalWith a env , evalWith b env
evalWith (fstᵗ p)      env = let (a , _) = evalWith p env in a
evalWith (sndᵗ p)      env = let (_ , b) = evalWith p env in b
evalWith (inlᵗ a)      env = inj₁ (evalWith a env)
evalWith (inrᵗ a)      env = inj₂ (evalWith a env)
evalWith (caseᵗ sc l r) env with evalWith sc env
... | inj₁ x = evalWith l (x ∷ᵃ env)
... | inj₂ y = evalWith r (y ∷ᵃ env)
evalWith (ifᵗ c t e)   env = if evalWith c env then evalWith t env else evalWith e env
evalWith (primᵗ add arg)  env = let (a , b) = evalWith arg env in a + b
evalWith (primᵗ sub arg)  env = let (a , b) = evalWith arg env in a ∸ b
evalWith (primᵗ mul arg)  env = let (a , b) = evalWith arg env in a * b
evalWith (primᵗ eqᵖ arg)  env = let (a , b) = evalWith arg env in a ≡ᵇ b
evalWith (primᵗ ltᵖ arg)  env = let (a , b) = evalWith arg env in a <ᵇ b
evalWith (primᵗ notᵖ arg) env = not (evalWith arg env)
evalWith (strmᵗ e)     []ᵃ        = e
evalWith (strmᵗ e)     (v ∷ᵃ vs)  = closeUnderFn e (v ∷ᵃ vs)

evalTm  : ∀ {n} {Γ : Ctx n} {t} → Tm Γ [] [] [] t → Val Γ t
evalTm t = evalWith t []ᵃ

applyFn : ∀ {n} {Γ : Ctx n} {s t} → Fn Γ [] [] [] s t → Val Γ s → Val Γ t
applyFn fn v = evalWith fn (v ∷ᵃ []ᵃ)

------------------------------------------------------------------
-- Syntax size, counting everything — including under deferᵉ and
-- inside strmᵗ templates.  Seeds the evaluator's sync-fuel budget
-- (Rx.Evaluator.syncBudget): the budget must dominate a cascade's
-- recursion depth, and every runtime value is assembled from these
-- counted templates
------------------------------------------------------------------

mutual
  sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  sizeᵉ (input i)        = 1
  sizeᵉ (ofᵉ ts)         = suc (sizeᵗˢ ts)
  sizeᵉ emptyᵉ           = 1
  sizeᵉ (mapᵉ f e)       = suc (sizeᵗ f + sizeᵉ e)
  sizeᵉ (takeᵉ c e)      = suc (sizeᵗ c + sizeᵉ e)
  sizeᵉ (scanᵉ f z e)    = suc (sizeᵗ f + sizeᵗ z + sizeᵉ e)
  sizeᵉ (mergeAllᵉ e)    = suc (sizeᵉ e)
  sizeᵉ (concatAllᵉ e)   = suc (sizeᵉ e)
  sizeᵉ (switchAllᵉ e)   = suc (sizeᵉ e)
  sizeᵉ (exhaustAllᵉ e)  = suc (sizeᵉ e)
  sizeᵉ (μᵉ e)           = suc (sizeᵉ e)
  sizeᵉ (varᵉ x)         = 1
  sizeᵉ (deferᵉ e)       = suc (sizeᵉ e)

  sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  sizeᵗ (varᵗ x)      = 1
  sizeᵗ unit̂          = 1
  sizeᵗ (bool̂ _)      = 1
  sizeᵗ (nat̂ _)       = 1
  sizeᵗ (pairᵗ a b)   = suc (sizeᵗ a + sizeᵗ b)
  sizeᵗ (fstᵗ p)      = suc (sizeᵗ p)
  sizeᵗ (sndᵗ p)      = suc (sizeᵗ p)
  sizeᵗ (inlᵗ a)      = suc (sizeᵗ a)
  sizeᵗ (inrᵗ a)      = suc (sizeᵗ a)
  sizeᵗ (caseᵗ s l r) = suc (sizeᵗ s + sizeᵗ l + sizeᵗ r)
  sizeᵗ (ifᵗ c a b)   = suc (sizeᵗ c + sizeᵗ a + sizeᵗ b)
  sizeᵗ (primᵗ _ a)   = suc (sizeᵗ a)
  sizeᵗ (strmᵗ e)     = suc (sizeᵉ e)

  sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  sizeᵗˢ []       = 1
  sizeᵗˢ (y ∷ ys) = sizeᵗ y + sizeᵗˢ ys

------------------------------------------------------------------
-- Sync-reachable size: like sizeᵉ, but a deferᵉ subtree counts as
-- a leaf — nothing under a defer is subscribed within the current
-- instant.  This is the size class the budget-sufficiency measure
-- reads (Verify-Budget-Sufficient): unfoldμ substitutes (μᵉ body)
-- only at defer-gated var positions, so μ-unfolding PRESERVES
-- syncSize while sizeᵉ grows.
------------------------------------------------------------------

mutual
  syncSizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  syncSizeᵉ (input i)        = 1
  syncSizeᵉ (ofᵉ ts)         = suc (syncSizeᵗˢ ts)
  syncSizeᵉ emptyᵉ           = 1
  syncSizeᵉ (mapᵉ f e)       = suc (syncSizeᵗ f + syncSizeᵉ e)
  syncSizeᵉ (takeᵉ c e)      = suc (syncSizeᵗ c + syncSizeᵉ e)
  syncSizeᵉ (scanᵉ f z e)    = suc (syncSizeᵗ f + syncSizeᵗ z + syncSizeᵉ e)
  syncSizeᵉ (mergeAllᵉ e)    = suc (syncSizeᵉ e)
  syncSizeᵉ (concatAllᵉ e)   = suc (syncSizeᵉ e)
  syncSizeᵉ (switchAllᵉ e)   = suc (syncSizeᵉ e)
  syncSizeᵉ (exhaustAllᵉ e)  = suc (syncSizeᵉ e)
  syncSizeᵉ (μᵉ e)           = suc (syncSizeᵉ e)
  syncSizeᵉ (varᵉ x)         = 1
  syncSizeᵉ (deferᵉ e)       = 1

  syncSizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  syncSizeᵗ (varᵗ x)      = 1
  syncSizeᵗ unit̂          = 1
  syncSizeᵗ (bool̂ _)      = 1
  syncSizeᵗ (nat̂ _)       = 1
  syncSizeᵗ (pairᵗ a b)   = suc (syncSizeᵗ a + syncSizeᵗ b)
  syncSizeᵗ (fstᵗ p)      = suc (syncSizeᵗ p)
  syncSizeᵗ (sndᵗ p)      = suc (syncSizeᵗ p)
  syncSizeᵗ (inlᵗ a)      = suc (syncSizeᵗ a)
  syncSizeᵗ (inrᵗ a)      = suc (syncSizeᵗ a)
  syncSizeᵗ (caseᵗ s l r) = suc (syncSizeᵗ s + syncSizeᵗ l + syncSizeᵗ r)
  syncSizeᵗ (ifᵗ c a b)   = suc (syncSizeᵗ c + syncSizeᵗ a + syncSizeᵗ b)
  syncSizeᵗ (primᵗ _ a)   = suc (syncSizeᵗ a)
  syncSizeᵗ (strmᵗ e)     = suc (syncSizeᵉ e)

  syncSizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  syncSizeᵗˢ []       = 1
  syncSizeᵗˢ (y ∷ ys) = syncSizeᵗ y + syncSizeᵗˢ ys

-- the size of a runtime value: embedded observables count their full
-- syntax; base payloads are opaque.  Scripted slot values are sized
-- with this too — they are part of the program-as-given, and the
-- budget must dominate the subscription work THEY demand (a scripted
-- obs value is subscribed like any other inner)
sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
sizeᵛ unitᵗ    _        = 1
sizeᵛ boolᵗ    _        = 1
sizeᵛ natᵗ     _        = 1
sizeᵛ (s ×ᵗ t) (a , b)  = suc (sizeᵛ s a + sizeᵛ t b)
sizeᵛ (s +ᵗ t) (inj₁ a) = suc (sizeᵛ s a)
sizeᵛ (s +ᵗ t) (inj₂ b) = suc (sizeᵛ t b)
sizeᵛ (obs t)  e        = sizeᵉ e