module Rx.Exp where

open import Data.Nat     using (ℕ; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Bool    using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Vec     using (Vec; lookup)
open import Data.Fin     using (Fin; toℕ)
open import Data.Maybe   using (Maybe)
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

-- A type is DATA when no `obs` occurs anywhere inside it.  `Val Γ (obs u)`
-- is `Closed Γ u` — an observable value IS an arbitrary closed expression —
-- so a value at a non-data type smuggles unbounded syntax in from outside
-- the program.  Nested occurrences count: `natᵗ ×ᵗ obs natᵗ` is reachable
-- with `mapᵉ (sndᵗ …)`, so the check has to be hereditary.  This is the
-- side condition on scripted slots (Rx.Evaluator.Slot).
isData : Ty → Bool
isData unitᵗ    = true
isData boolᵗ    = true
isData natᵗ     = true
isData (s ×ᵗ t) = if isData s then isData t else false
isData (s +ᵗ t) = if isData s then isData t else false
isData (obs _)  = false

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
    mergeAllᵉ   : ∀ {t} → Maybe ℕ → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
                 -- ONE higher-order primitive, carrying rxjs's own
                 -- `concurrent` argument.  `nothing` is Infinity, which is
                 -- plain `mergeAll`; `just 1` is `concatAll`; `just k` for k ≥ 2
                 -- is the bounded `mergeMap(f , k)` that has no name of its
                 -- own in rxjs and that nothing in this development could
                 -- previously express.  The limit is a `Maybe ℕ` and NOT a
                 -- `Tm`, unlike `takeᵉ`'s count: rxjs fixes `concurrent` when
                 -- the pipeline is BUILT, not when it is subscribed, so a
                 -- limit that varied per subscription would be a capability
                 -- the real operator does not have.  `just 0` is degenerate
                 -- but well defined — the queue grows and nothing is ever
                 -- subscribed — and is left representable rather than ruled
                 -- out by a side condition, which would have to be threaded
                 -- through every well-formedness face to buy the exclusion
                 -- of one program already indistinguishable from `emptyᵉ` on
                 -- its outputs.
    switchAllᵉ exhaustAllᵉ :
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
  renExp ρg ρd ρt (mergeAllᵉ lim e) = mergeAllᵉ lim (renExp ρg ρd ρt e)
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
  subΘExp Θloc σ (mergeAllᵉ lim e) = mergeAllᵉ lim (subΘExp Θloc σ e)
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
  elimGExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
           → Exp Γ [] [] Θsub t → Exp Γ Δᵍ Δ (Θloc ++ Θsub) u
           → Exp Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u
  elimGExp Θl x cl (input i)      = input i
  elimGExp Θl x cl (ofᵉ ts)       = ofᵉ (elimGTms Θl x cl ts)
  elimGExp Θl x cl emptyᵉ         = emptyᵉ
  elimGExp Θl x cl (mapᵉ f e)     = mapᵉ (elimGTm (_ ∷ Θl) x cl f) (elimGExp Θl x cl e)
  elimGExp Θl x cl (takeᵉ n e)    = takeᵉ (elimGTm Θl x cl n) (elimGExp Θl x cl e)
  elimGExp Θl x cl (scanᵉ f i e)  =
    scanᵉ (elimGTm (_ ∷ Θl) x cl f) (elimGTm Θl x cl i) (elimGExp Θl x cl e)
  elimGExp Θl x cl (mergeAllᵉ lim e) = mergeAllᵉ lim (elimGExp Θl x cl e)
  elimGExp Θl x cl (switchAllᵉ e) = switchAllᵉ (elimGExp Θl x cl e)
  elimGExp Θl x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimGExp Θl x cl e)
  elimGExp Θl x cl (μᵉ e)         = μᵉ (elimGExp Θl (there x) cl e)
  elimGExp Θl x cl (varᵉ y)       = varᵉ y
  elimGExp Θl x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ˡ x) (elimDExp Θl (∈-++⁺ˡ x) cl e))

  elimGTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
          → Exp Γ [] [] Θsub t → Tm Γ Δᵍ Δ (Θloc ++ Θsub) u
          → Tm Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u
  elimGTm Θl x cl (varᵗ y)     = varᵗ y
  elimGTm Θl x cl unit̂         = unit̂
  elimGTm Θl x cl (bool̂ b)     = bool̂ b
  elimGTm Θl x cl (nat̂ n)      = nat̂ n
  elimGTm Θl x cl (pairᵗ a b)  = pairᵗ (elimGTm Θl x cl a) (elimGTm Θl x cl b)
  elimGTm Θl x cl (fstᵗ p)     = fstᵗ (elimGTm Θl x cl p)
  elimGTm Θl x cl (sndᵗ p)     = sndᵗ (elimGTm Θl x cl p)
  elimGTm Θl x cl (inlᵗ a)     = inlᵗ (elimGTm Θl x cl a)
  elimGTm Θl x cl (inrᵗ a)     = inrᵗ (elimGTm Θl x cl a)
  elimGTm Θl x cl (caseᵗ s l r) =
    caseᵗ (elimGTm Θl x cl s) (elimGTm (_ ∷ Θl) x cl l) (elimGTm (_ ∷ Θl) x cl r)
  elimGTm Θl x cl (ifᵗ c a b)  =
    ifᵗ (elimGTm Θl x cl c) (elimGTm Θl x cl a) (elimGTm Θl x cl b)
  elimGTm Θl x cl (primᵗ op a) = primᵗ op (elimGTm Θl x cl a)
  elimGTm Θl x cl (strmᵗ e)    = strmᵗ (elimGExp Θl x cl e)

  elimGTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
           → Exp Γ [] [] Θsub t → List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
           → List (Tm Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u)
  elimGTms Θl x cl []       = []
  elimGTms Θl x cl (y ∷ ys) = elimGTm Θl x cl y ∷ elimGTms Θl x cl ys

  elimDExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
           → Exp Γ [] [] Θsub t → Exp Γ Δᵍ Δ (Θloc ++ Θsub) u
           → Exp Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u
  elimDExp Θl x cl (input i)      = input i
  elimDExp Θl x cl (ofᵉ ts)       = ofᵉ (elimDTms Θl x cl ts)
  elimDExp Θl x cl emptyᵉ         = emptyᵉ
  elimDExp Θl x cl (mapᵉ f e)     = mapᵉ (elimDTm (_ ∷ Θl) x cl f) (elimDExp Θl x cl e)
  elimDExp Θl x cl (takeᵉ n e)    = takeᵉ (elimDTm Θl x cl n) (elimDExp Θl x cl e)
  elimDExp Θl x cl (scanᵉ f i e)  =
    scanᵉ (elimDTm (_ ∷ Θl) x cl f) (elimDTm Θl x cl i) (elimDExp Θl x cl e)
  elimDExp Θl x cl (mergeAllᵉ lim e) = mergeAllᵉ lim (elimDExp Θl x cl e)
  elimDExp Θl x cl (switchAllᵉ e) = switchAllᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (μᵉ e)         = μᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (varᵉ y)       with compare∈ x y
  ... | inj₁ refl = renExp (λ ()) (λ ()) (∈-++⁺ʳ Θl) cl
  ... | inj₂ y′   = varᵉ y′
  elimDExp Θl x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ʳ x) (elimDExp Θl (∈-++⁺ʳ _ x) cl e))

  elimDTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
          → Exp Γ [] [] Θsub t → Tm Γ Δᵍ Δ (Θloc ++ Θsub) u
          → Tm Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u
  elimDTm Θl x cl (varᵗ y)     = varᵗ y
  elimDTm Θl x cl unit̂         = unit̂
  elimDTm Θl x cl (bool̂ b)     = bool̂ b
  elimDTm Θl x cl (nat̂ n)      = nat̂ n
  elimDTm Θl x cl (pairᵗ a b)  = pairᵗ (elimDTm Θl x cl a) (elimDTm Θl x cl b)
  elimDTm Θl x cl (fstᵗ p)     = fstᵗ (elimDTm Θl x cl p)
  elimDTm Θl x cl (sndᵗ p)     = sndᵗ (elimDTm Θl x cl p)
  elimDTm Θl x cl (inlᵗ a)     = inlᵗ (elimDTm Θl x cl a)
  elimDTm Θl x cl (inrᵗ a)     = inrᵗ (elimDTm Θl x cl a)
  elimDTm Θl x cl (caseᵗ s l r) =
    caseᵗ (elimDTm Θl x cl s) (elimDTm (_ ∷ Θl) x cl l) (elimDTm (_ ∷ Θl) x cl r)
  elimDTm Θl x cl (ifᵗ c a b)  =
    ifᵗ (elimDTm Θl x cl c) (elimDTm Θl x cl a) (elimDTm Θl x cl b)
  elimDTm Θl x cl (primᵗ op a) = primᵗ op (elimDTm Θl x cl a)
  elimDTm Θl x cl (strmᵗ e)    = strmᵗ (elimDExp Θl x cl e)

  elimDTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
           → Exp Γ [] [] Θsub t → List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
           → List (Tm Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u)
  elimDTms Θl x cl []       = []
  elimDTms Θl x cl (y ∷ ys) = elimDTm Θl x cl y ∷ elimDTms Θl x cl ys

unfoldμ : ∀ {n} {Γ : Ctx n} {Θ t} → Exp Γ (t ∷ []) [] Θ t → Exp Γ [] [] Θ t
unfoldμ body = elimGExp [] (here refl) (μᵉ body) body

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
-- STRATIFICATION of the slot telescope: every `input j` an
-- expression mentions has j < k.  A shared slot's def carries this
-- as a side condition (Rx.Slots.shared), so the telescope is a real
-- JS `const` telescope — a def can read only strictly-earlier
-- bindings, exactly what the TS generator already builds and what a
-- JS const can reference without a TDZ error.  It exists so that a
-- per-slot measure is computable by recursion on the slot index:
-- slot k reads only slots j < k.
--
-- deferᵉ is NOT cut: a deferred subtree
-- subscribes later, but its `input` references are just as real
-- when it does.  The check is about which slots a def can EVER
-- reach, not about when.
------------------------------------------------------------------
mutual
  inputsBelowᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → Exp Γ Δᵍ Δ Θ t → Bool
  inputsBelowᵉ k (input i)       = toℕ i <ᵇ k
  inputsBelowᵉ k (ofᵉ ts)        = inputsBelowᵗˢ k ts
  inputsBelowᵉ k emptyᵉ          = true
  inputsBelowᵉ k (mapᵉ f e)      = inputsBelowᵗ k f ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (takeᵉ c e)     = inputsBelowᵗ k c ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (scanᵉ f z e)   =
    inputsBelowᵗ k f ∧ inputsBelowᵗ k z ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (mergeAllᵉ lim e) = inputsBelowᵉ k e
  inputsBelowᵉ k (switchAllᵉ e)  = inputsBelowᵉ k e
  inputsBelowᵉ k (exhaustAllᵉ e) = inputsBelowᵉ k e
  inputsBelowᵉ k (μᵉ e)          = inputsBelowᵉ k e
  inputsBelowᵉ k (varᵉ x)        = true
  inputsBelowᵉ k (deferᵉ e)      = inputsBelowᵉ k e

  inputsBelowᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → Tm Γ Δᵍ Δ Θ t → Bool
  inputsBelowᵗ k (varᵗ x)      = true
  inputsBelowᵗ k unit̂          = true
  inputsBelowᵗ k (bool̂ _)      = true
  inputsBelowᵗ k (nat̂ _)       = true
  inputsBelowᵗ k (pairᵗ a b)   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
  inputsBelowᵗ k (fstᵗ p)      = inputsBelowᵗ k p
  inputsBelowᵗ k (sndᵗ p)      = inputsBelowᵗ k p
  inputsBelowᵗ k (inlᵗ a)      = inputsBelowᵗ k a
  inputsBelowᵗ k (inrᵗ a)      = inputsBelowᵗ k a
  inputsBelowᵗ k (caseᵗ s l r) =
    inputsBelowᵗ k s ∧ inputsBelowᵗ k l ∧ inputsBelowᵗ k r
  inputsBelowᵗ k (ifᵗ c a b)   =
    inputsBelowᵗ k c ∧ inputsBelowᵗ k a ∧ inputsBelowᵗ k b
  inputsBelowᵗ k (primᵗ _ a)   = inputsBelowᵗ k a
  inputsBelowᵗ k (strmᵗ e)     = inputsBelowᵉ k e

  inputsBelowᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → List (Tm Γ Δᵍ Δ Θ t) → Bool
  inputsBelowᵗˢ k []       = true
  inputsBelowᵗˢ k (y ∷ ys) = inputsBelowᵗ k y ∧ inputsBelowᵗˢ k ys
