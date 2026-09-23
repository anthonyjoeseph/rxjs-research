------------------------------------------------------------------
-- COMPARING TWO VALUES, WITH THE PROOF WHEN THEY ARE THE SAME.
------------------------------------------------------------------

-- WHAT THE CONSUMER NEEDS IS ONE DIRECTION.  A held candidate is spent
-- on a stored value only when the two are equal, and a comparison that
-- answers "not known equal" hands back an unvouched value, which the
-- consumer already has to cope with.  So this answers `Maybe (a ≡ b)`:
-- a `just` carries the equality the candidate is transported along,
-- and nothing ever has to be refuted.
--
-- IT IS STRUCTURAL ON THE TYPE AT DATA, AND ON THE SYNTAX AT AN
-- OBSERVABLE.  An observable value is a telescope, a body and an
-- environment of values, so the comparison decides the telescope,
-- walks the two bodies former by former, and compares the environments
-- entry by entry -- which is the one place it re-enters the value
-- comparison, on an entry of the environment it was handed.
--
-- AND IT IS COMPLETE ON EVERY FORMER, so two values that are the same
-- syntax always come back `just`.  That is not stated, because nothing
-- consumes it: an incomplete answer costs a guard, never a wrong run.
module Rx.Exp.ValEq where

open import Data.Bool using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeP
open import Data.Nat using () renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (lookup)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; _≟ᵗ_;
  Ctx; Val; Env; []ᵉ; _∷ᵉ_; Exp; Tm; PrimOp;
  input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ;
  foldᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)

-- a decision is in particular a semi-decision
known : ∀ {A : Set} {a b : A} → Dec (a ≡ b) → Maybe (a ≡ b)
known (yes p) = just p
known (no _)  = nothing

-- A MEMBERSHIP PROOF IS A POSITION, so two of them are equal exactly
-- when they count to the same place.
eqMem : ∀ {A : Set} {x : A} {xs : List A} (p q : x ∈ xs) → Maybe (p ≡ q)
eqMem (here refl) (here refl) = just refl
eqMem (there p)   (there q)   with eqMem p q
... | just refl = just refl
... | nothing   = nothing
eqMem _ _ = nothing

eqPrim : ∀ {s t} (p q : PrimOp s t) → Maybe (p ≡ q)
eqPrim add  add  = just refl
eqPrim sub  sub  = just refl
eqPrim mul  mul  = just refl
eqPrim eqᵖ  eqᵖ  = just refl
eqPrim ltᵖ  ltᵖ  = just refl
eqPrim eqᵘ  eqᵘ  = just refl
eqPrim notᵖ notᵖ = just refl
eqPrim _    _    = nothing

-- THE INPUT FORMER'S INDEX IS A LOOKUP, so two of them cannot be
-- matched against each other at one type: the unifier would have to
-- solve `lookup Γ i = lookup Γ j`.  Stated at a type the second one
-- is transported to, the index is a variable and the match goes
-- through; once the slots agree the transport is reflexivity.
eqInput : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} (i : _) (p : lookup Γ i ≡ u)
          (b : Exp Γ Δᵍ Δ Θ u) → Maybe (subst (Exp Γ Δᵍ Δ Θ) p (input i) ≡ b)
eqInput i p (input j) with i ≟ᶠ j
... | no  _    = nothing
... | yes refl with p
...   | refl = just refl
eqInput i p _ = nothing

eqExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (a b : Exp Γ Δᵍ Δ Θ t) → Maybe (a ≡ b)
eqTm  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (a b : Tm Γ Δᵍ Δ Θ t) → Maybe (a ≡ b)
eqTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (a b : List (Tm Γ Δᵍ Δ Θ t)) → Maybe (a ≡ b)

-- the bracket's index is a pair built from its source's, and a second
-- expression at that index may be an input, so it is transported the
-- same way the input former is
eqBatch : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t u} (a : Exp Γ Δᵍ Δ Θ t) (p : (t ×ᵗ listᵗ t) ≡ u)
          (b : Exp Γ Δᵍ Δ Θ u) → Maybe (subst (Exp Γ Δᵍ Δ Θ) p (batchSyncᵉ a) ≡ b)

eqExp (input i) b = eqInput i refl b
eqExp (ofᵉ ts) (ofᵉ ts′) with eqTms ts ts′
... | just refl = just refl
... | nothing   = nothing
eqExp emptyᵉ emptyᵉ = just refl
eqExp (takeᵉ c a) (takeᵉ c′ a′) with eqTm c c′ | eqExp a a′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqExp (batchSyncᵉ a) b = eqBatch a refl b
eqExp (mapᵉ {s = s} f a) (mapᵉ {s = s′} f′ a′) with s ≟ᵗ s′
... | no  _    = nothing
... | yes refl with eqTm f f′ | eqExp a a′
...   | just refl | just refl = just refl
...   | _         | _         = nothing
eqExp (scanᵉ {s = s} f z a) (scanᵉ {s = s′} f′ z′ a′) with s ≟ᵗ s′
... | no  _    = nothing
... | yes refl with eqTm f f′ | eqTm z z′ | eqExp a a′
...   | just refl | just refl | just refl = just refl
...   | _         | _         | _         = nothing
eqExp (mergeAllᵉ l a) (mergeAllᵉ l′ a′) with MaybeP.≡-dec _≟ⁿ_ l l′ | eqExp a a′
... | yes refl | just refl = just refl
... | _        | _         = nothing
eqExp (switchAllᵉ a) (switchAllᵉ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqExp (exhaustAllᵉ a) (exhaustAllᵉ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqExp (μᵉ a) (μᵉ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqExp (varᵉ x) (varᵉ x′) with eqMem x x′
... | just refl = just refl
... | nothing   = nothing
eqExp (deferᵉ a) (deferᵉ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqExp (mintᵉ a) (mintᵉ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqExp _ _ = nothing

eqBatch a p (batchSyncᵉ a′) with p
... | refl with eqExp a a′
...   | just refl = just refl
...   | nothing   = nothing
eqBatch a p _ = nothing

eqTm (varᵗ x) (varᵗ x′) with eqMem x x′
... | just refl = just refl
... | nothing   = nothing
eqTm unit̂ unit̂ = just refl
eqTm (bool̂ b) (bool̂ b′) with b ≟ᵇ b′
... | yes refl = just refl
... | no  _    = nothing
eqTm (nat̂ k) (nat̂ k′) with k ≟ⁿ k′
... | yes refl = just refl
... | no  _    = nothing
eqTm (pairᵗ a b) (pairᵗ a′ b′) with eqTm a a′ | eqTm b b′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqTm (fstᵗ {t = t} a) (fstᵗ {t = t′} a′) with t ≟ᵗ t′
... | no  _    = nothing
... | yes refl with eqTm a a′
...   | just refl = just refl
...   | nothing   = nothing
eqTm (sndᵗ {s = s} a) (sndᵗ {s = s′} a′) with s ≟ᵗ s′
... | no  _    = nothing
... | yes refl with eqTm a a′
...   | just refl = just refl
...   | nothing   = nothing
eqTm nilᵗ nilᵗ = just refl
eqTm (consᵗ a as) (consᵗ a′ as′) with eqTm a a′ | eqTm as as′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqTm (inlᵗ a) (inlᵗ a′) with eqTm a a′
... | just refl = just refl
... | nothing   = nothing
eqTm (inrᵗ a) (inrᵗ a′) with eqTm a a′
... | just refl = just refl
... | nothing   = nothing
eqTm (caseᵗ {s = s} {t = t} a l r) (caseᵗ {s = s′} {t = t′} a′ l′ r′)
  with s ≟ᵗ s′ | t ≟ᵗ t′
... | yes refl | yes refl with eqTm a a′ | eqTm l l′ | eqTm r r′
...   | just refl | just refl | just refl = just refl
...   | _         | _         | _         = nothing
eqTm (caseᵗ _ _ _) (caseᵗ _ _ _) | _ | _ = nothing
eqTm (foldᵗ {s = s} xs z f) (foldᵗ {s = s′} xs′ z′ f′) with s ≟ᵗ s′
... | no  _    = nothing
... | yes refl with eqTm xs xs′ | eqTm z z′ | eqTm f f′
...   | just refl | just refl | just refl = just refl
...   | _         | _         | _         = nothing
eqTm (ifᵗ c a b) (ifᵗ c′ a′ b′) with eqTm c c′ | eqTm a a′ | eqTm b b′
... | just refl | just refl | just refl = just refl
... | _         | _         | _         = nothing
eqTm (primᵗ {s = s} p a) (primᵗ {s = s′} p′ a′) with s ≟ᵗ s′
... | no  _    = nothing
... | yes refl with eqPrim p p′ | eqTm a a′
...   | just refl | just refl = just refl
...   | _         | _         = nothing
eqTm (strmᵗ a) (strmᵗ a′) with eqExp a a′
... | just refl = just refl
... | nothing   = nothing
eqTm _ _ = nothing

eqTms []       []         = just refl
eqTms (a ∷ as) (a′ ∷ as′) with eqTm a a′ | eqTms as as′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqTms _ _ = nothing

-- THE VALUE COMPARISON, by the type at data and by the closure at an
-- observable.  The environment's entries are compared at their own
-- types, which are not below `obs t`; what shrinks there is the value.
eqVal : ∀ {n} {Γ : Ctx n} (t : Ty) (a b : Val Γ t) → Maybe (a ≡ b)
eqEnv : ∀ {n} {Γ : Ctx n} {Θ} (ρ ρ′ : Env Γ Θ) → Maybe (ρ ≡ ρ′)

eqVal unitᵗ    _ _ = just refl
eqVal boolᵗ    a b = known (a ≟ᵇ b)
eqVal natᵗ     a b = known (a ≟ⁿ b)
eqVal uniqᵗ    a b = known (a ≟ⁿ b)
eqVal (s ×ᵗ t) (a , b) (a′ , b′) with eqVal s a a′ | eqVal t b b′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqVal (s +ᵗ t) (inj₁ a) (inj₁ a′) with eqVal s a a′
... | just refl = just refl
... | nothing   = nothing
eqVal (s +ᵗ t) (inj₂ b) (inj₂ b′) with eqVal t b b′
... | just refl = just refl
... | nothing   = nothing
eqVal (s +ᵗ t) _ _ = nothing
eqVal (listᵗ t) []       []         = just refl
eqVal (listᵗ t) (a ∷ as) (a′ ∷ as′) with eqVal t a a′ | eqVal (listᵗ t) as as′
... | just refl | just refl = just refl
... | _         | _         = nothing
eqVal (listᵗ t) _ _ = nothing
eqVal (obs t) (Θ , a , ρ) (Θ′ , a′ , ρ′) with ≡-dec _≟ᵗ_ Θ Θ′
... | no  _    = nothing
... | yes refl with eqExp a a′ | eqEnv ρ ρ′
...   | just refl | just refl = just refl
...   | _         | _         = nothing

eqEnv []ᵉ       []ᵉ         = just refl
eqEnv (_∷ᵉ_ {s = s} v vs) (v′ ∷ᵉ vs′) with eqVal s v v′ | eqEnv vs vs′
... | just refl | just refl = just refl
... | _         | _         = nothing
