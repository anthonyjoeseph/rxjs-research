module Rx.Exp where

open import Data.Nat     using (ℕ; suc; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Bool    using (Bool; true; false; not; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Vec     using (Vec; lookup)
open import Data.Fin     using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


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

postulate
  -- closing a runtime observable built from a fn's argument (strmᵗ under
  -- a non-empty Θ): a single-variable Θ-substitution, the one piece of the
  -- substitution framework still owed. Never forced by the current
  -- QuickCheck fragment (its fns never return observables).
  closeUnderFn : ∀ {n} {Γ : Ctx n} {s Θ t}
               → Exp Γ [] [] (s ∷ Θ) t → All (Val Γ) (s ∷ Θ) → Exp Γ [] [] [] t
  unfoldμ : ∀ {n} {Γ : Ctx n} {t} → Exp Γ (t ∷ []) [] [] t → Closed Γ t
  wkᵍ     : ∀ {n} {Γ : Ctx n} {g Δᵍ Δ Θ t}
          → Exp Γ Δᵍ Δ Θ t → Exp Γ (g ∷ Δᵍ) Δ Θ t     -- context weakening

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