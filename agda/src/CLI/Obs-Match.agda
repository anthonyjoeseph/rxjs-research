------------------------------------------------------------------
-- AN OBSERVABLE'S TERMS, COMPARED.  `ObsRel` relates an impl inner to a
-- plain one when the impl's term is the plain author's tree run through
-- `toInstEmit` and renamed.  The plain term is `plainExp` of that tree,
-- constructor for constructor, so `unplain` reads the tree back; the
-- elaborated term and the impl's are then walked together, and the walk
-- returns the value variables the renaming has to send where, or
-- nothing when the two differ anywhere else.
--
-- A RENAMING LIFTS UNDER A BINDER, so the walk counts the binders it
-- has passed: a variable below that count is the same binder on both
-- sides, and one above it is a pair the renaming must take.  The
-- `μ`-variables are renamed by the identity, and so must be equal.
------------------------------------------------------------------
module CLI.Obs-Match where

open import Data.Bool    using (Bool; true; false; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (toℕ)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; suc; _∸_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_)

open import Rx.Exp       using (Ty; Ctx; Exp; Tm; PrimOp; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ;
  input; ofᵉ; emptyᵉ; takeWhileᵉ; batchSyncᵉ; mapᵉ; scanᵉ; flattenᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; primᵗ; strmᵗ)
open import SExp.Syntax  using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeWhileˢ; mapˢ; scanˢ; flattenˢ; μˢ; varˢ; deferˢ;
  varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ; caseˢ; foldˢ; ifˢ; primˢ; strmˢ)

infixl 4 _⊛_
_⊛_ : ∀ {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
just f ⊛ just a = just (f a)
_      ⊛ _      = nothing

------------------------------------------------------------------
-- `plainExp`, read back
------------------------------------------------------------------

mutual
  unplain : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Maybe (SExp Γ Δᵍ Δ Θ t)
  unplain (input i)        = just (inputˢ i)
  unplain (ofᵉ ts)         = just ofˢ ⊛ unplainTms ts
  unplain emptyᵉ           = just emptyˢ
  unplain (takeWhileᵉ f e) = just takeWhileˢ ⊛ unplainTm f ⊛ unplain e
  unplain (mapᵉ f e)       = just mapˢ ⊛ unplainTm f ⊛ unplain e
  unplain (scanᵉ f z e)    = just scanˢ ⊛ unplainTm f ⊛ unplainTm z ⊛ unplain e
  unplain (flattenᵉ op e)  = just (flattenˢ op) ⊛ unplain e
  unplain (μᵉ e)           = just μˢ ⊛ unplain e
  unplain (varᵉ x)         = just (varˢ x)
  unplain (deferᵉ e)       = just deferˢ ⊛ unplain e
  unplain (batchSyncᵉ _)   = nothing
  unplain (mintᵉ _)        = nothing

  unplainTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → Maybe (STm Γ Δᵍ Δ Θ t)
  unplainTm (varᵗ x)      = just (varˢᵗ x)
  unplainTm unit̂          = just unitˢ
  unplainTm (bool̂ b)      = just (boolˢ b)
  unplainTm (nat̂ k)       = just (natˢ k)
  unplainTm (pairᵗ a b)   = just pairˢ ⊛ unplainTm a ⊛ unplainTm b
  unplainTm (fstᵗ p)      = just fstˢ ⊛ unplainTm p
  unplainTm (sndᵗ p)      = just sndˢ ⊛ unplainTm p
  unplainTm nilᵗ          = just nilˢ
  unplainTm (consᵗ h t)   = just consˢ ⊛ unplainTm h ⊛ unplainTm t
  unplainTm (inlᵗ a)      = just inlˢ ⊛ unplainTm a
  unplainTm (inrᵗ b)      = just inrˢ ⊛ unplainTm b
  unplainTm (caseᵗ s l r) = just caseˢ ⊛ unplainTm s ⊛ unplainTm l ⊛ unplainTm r
  unplainTm (foldᵗ l z f) = just foldˢ ⊛ unplainTm l ⊛ unplainTm z ⊛ unplainTm f
  unplainTm (ifᵗ c a b)   = just ifˢ ⊛ unplainTm c ⊛ unplainTm a ⊛ unplainTm b
  unplainTm (primᵗ p a)   = just (primˢ p) ⊛ unplainTm a
  unplainTm (strmᵗ e)     = just strmˢ ⊛ unplain e

  unplainTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → Maybe (List (STm Γ Δᵍ Δ Θ t))
  unplainTms []       = just []
  unplainTms (m ∷ ms) = just _∷_ ⊛ unplainTm m ⊛ unplainTms ms

------------------------------------------------------------------
-- Two terms over one input context, walked together
------------------------------------------------------------------

ix : ∀ {t : Ty} {xs} → t ∈ xs → ℕ
ix (here _)  = 0
ix (there p) = suc (ix p)

primIx : ∀ {s t} → PrimOp s t → ℕ
primIx add  = 0
primIx sub  = 1
primIx mul  = 2
primIx eqᵖ  = 3
primIx ltᵖ  = 4
primIx eqᵘ  = 5
primIx notᵖ = 6

eqLim : Maybe ℕ → Maybe ℕ → Bool
eqLim nothing  nothing  = true
eqLim (just a) (just b) = a ≡ᵇ b
eqLim _        _        = false

eqFlat : FlatOp → FlatOp → Bool
eqFlat (mergeᶠ l) (mergeᶠ l′) = eqLim l l′
eqFlat switchᶠ    switchᶠ     = true
eqFlat exhaustᶠ   exhaustᶠ    = true
eqFlat _          _           = false

-- the value variables the renaming takes, source to target
Pairs : Set
Pairs = Maybe (List (ℕ × ℕ))

infixr 5 _&_
_&_ : Pairs → Pairs → Pairs
just a & just b = just (a ++ b)
_      & _      = nothing

when : Bool → Pairs → Pairs
when b p = if b then p else nothing

-- a variable `k` binders deep: a binder is itself, a free one a pair
var : ℕ → ℕ → ℕ → Pairs
var k i j = if i <ᵇ k then when (i ≡ᵇ j) (just [])
            else when (not (j <ᵇ k)) (just ((i ∸ k , j ∸ k) ∷ []))

module _ {m} {Γ : Ctx m} where

  mutual
    matchExp : ∀ {Δᵍ Δ Θ t Δᵍ′ Δ′ Θ′ t′} → ℕ → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ′ Δ′ Θ′ t′ → Pairs
    matchExp k (input i)        (input j)          = when (toℕ i ≡ᵇ toℕ j) (just [])
    matchExp k (ofᵉ ts)         (ofᵉ us)           = matchTms k ts us
    matchExp k emptyᵉ           emptyᵉ             = just []
    matchExp k (takeWhileᵉ f e) (takeWhileᵉ g e′)  = matchTm (suc k) f g & matchExp k e e′
    matchExp k (batchSyncᵉ e)   (batchSyncᵉ e′)    = matchExp k e e′
    matchExp k (mapᵉ f e)       (mapᵉ g e′)        = matchTm (suc k) f g & matchExp k e e′
    matchExp k (scanᵉ f z e)    (scanᵉ g z′ e′)    = matchTm (suc k) f g & matchTm k z z′ & matchExp k e e′
    matchExp k (flattenᵉ o e)   (flattenᵉ o′ e′)   = when (eqFlat o o′) (matchExp k e e′)
    matchExp k (μᵉ e)           (μᵉ e′)            = matchExp k e e′
    matchExp k (varᵉ x)         (varᵉ y)           = when (ix x ≡ᵇ ix y) (just [])
    matchExp k (deferᵉ e)       (deferᵉ e′)        = matchExp k e e′
    matchExp k (mintᵉ e)        (mintᵉ e′)         = matchExp (suc k) e e′
    matchExp k _                _                  = nothing

    matchTm : ∀ {Δᵍ Δ Θ t Δᵍ′ Δ′ Θ′ t′} → ℕ → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ′ Δ′ Θ′ t′ → Pairs
    matchTm k (varᵗ x)      (varᵗ y)         = var k (ix x) (ix y)
    matchTm k unit̂          unit̂             = just []
    matchTm k (bool̂ b)      (bool̂ c)         = when (if b then c else not c) (just [])
    matchTm k (nat̂ a)       (nat̂ b)          = when (a ≡ᵇ b) (just [])
    matchTm k (pairᵗ a b)   (pairᵗ a′ b′)    = matchTm k a a′ & matchTm k b b′
    matchTm k (fstᵗ p)      (fstᵗ p′)        = matchTm k p p′
    matchTm k (sndᵗ p)      (sndᵗ p′)        = matchTm k p p′
    matchTm k nilᵗ          nilᵗ             = just []
    matchTm k (consᵗ h t)   (consᵗ h′ t′)    = matchTm k h h′ & matchTm k t t′
    matchTm k (inlᵗ a)      (inlᵗ a′)        = matchTm k a a′
    matchTm k (inrᵗ b)      (inrᵗ b′)        = matchTm k b b′
    matchTm k (caseᵗ s l r) (caseᵗ s′ l′ r′) = matchTm k s s′ & matchTm (suc k) l l′ & matchTm (suc k) r r′
    matchTm k (foldᵗ l z f) (foldᵗ l′ z′ f′) = matchTm k l l′ & matchTm k z z′ & matchTm (suc (suc k)) f f′
    matchTm k (ifᵗ c a b)   (ifᵗ c′ a′ b′)   = matchTm k c c′ & matchTm k a a′ & matchTm k b b′
    matchTm k (primᵗ p a)   (primᵗ p′ a′)    = when (primIx p ≡ᵇ primIx p′) (matchTm k a a′)
    matchTm k (strmᵗ e)     (strmᵗ e′)       = matchExp k e e′
    matchTm k _             _                = nothing

    matchTms : ∀ {Δᵍ Δ Θ t Δᵍ′ Δ′ Θ′ t′} → ℕ → List (Tm Γ Δᵍ Δ Θ t) → List (Tm Γ Δᵍ′ Δ′ Θ′ t′) → Pairs
    matchTms k []       []       = just []
    matchTms k (a ∷ as) (b ∷ bs) = matchTm k a b & matchTms k as bs
    matchTms k _        _        = nothing

-- the pairs are one renaming: no source sent two places
functional : List (ℕ × ℕ) → Bool
functional ps = all (λ (i , j) → all (λ (i′ , j′) → not (i ≡ᵇ i′) ∨ (j ≡ᵇ j′)) ps) ps

-- where the renaming sends a source, the identity where the terms never say
image : List (ℕ × ℕ) → ℕ → ℕ
image []             i = i
image ((a , b) ∷ ps) i = if a ≡ᵇ i then b else image ps i
