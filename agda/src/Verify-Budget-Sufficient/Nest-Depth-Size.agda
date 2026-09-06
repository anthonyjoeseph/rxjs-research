-- THE DEPTH-UNDER-SIZE INDUCTION, ON ITS OWN.  It is a fact about the
-- TERM LANGUAGE and about nothing else in this tower -- no cap, no
-- path, no store -- so it belongs under everything that reads it
-- rather than inside whichever face happened to need it first.  Two
-- faces read it now and they sit on opposite sides of the store, so a
-- shared home is what keeps the walk's currency out of the delivery
-- face's cone.
module Verify-Budget-Sufficient.Nest-Depth-Size where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (_+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-assoc; +-comm; +-mono-≤; ⊔-lub)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import Rx.Exp using
  (Ctx; Exp; Tm; Ty; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ;
  inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵗˢ; nestDᵛ)

-- EVERY NEST DEPTH IS UNDER A SIZE, over the whole term language at
-- once.  The mutuality is the language's: a term may carry a stream and
-- a stream may carry terms, so the three arms are one induction.
mutual
  nestDᵉ≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → nestDᵉ e ≤ sizeᵉ e
  nestDᵉ≤sizeᵉ (input i)        = z≤n
  nestDᵉ≤sizeᵉ (ofᵉ ts)         = m≤n⇒m≤1+n (nestDᵗˢ≤sizeᵗˢ ts)
  nestDᵉ≤sizeᵉ emptyᵉ           = z≤n
  nestDᵉ≤sizeᵉ (mapᵉ f e)       = m≤n⇒m≤1+n (+-mono-≤ (nestDᵗ≤sizeᵗ f) (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (takeᵉ c e)      = m≤n⇒m≤1+n (≤-trans (nestDᵉ≤sizeᵉ e) (m≤n+m (sizeᵉ e) (sizeᵗ c)))
  nestDᵉ≤sizeᵉ (scanᵉ f z e)    =
    m≤n⇒m≤1+n (+-mono-≤ (≤-trans (+-mono-≤ (nestDᵗ≤sizeᵗ z) (nestDᵗ≤sizeᵗ f))
                                 (≤-reflexive (+-comm (sizeᵗ z) (sizeᵗ f))))
                        (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (mergeAllᵉ _ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (switchAllᵉ e)   = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (exhaustAllᵉ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (μᵉ e)           = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (varᵉ x)         = z≤n
  nestDᵉ≤sizeᵉ (deferᵉ e)       = z≤n

  nestDᵗ≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (f : Tm Γ Δᵍ Δ Θ t) → nestDᵗ f ≤ sizeᵗ f
  nestDᵗ≤sizeᵗ (varᵗ x)      = z≤n
  nestDᵗ≤sizeᵗ unit̂          = z≤n
  nestDᵗ≤sizeᵗ (bool̂ _)      = z≤n
  nestDᵗ≤sizeᵗ (nat̂ _)       = z≤n
  nestDᵗ≤sizeᵗ (pairᵗ a b)   =
    m≤n⇒m≤1+n (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                     (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
  nestDᵗ≤sizeᵗ (fstᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (sndᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (inlᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (inrᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (caseᵗ s l r) =
    m≤n⇒m≤1+n (≤-trans
      (+-mono-≤ (nestDᵗ≤sizeᵗ s)
                (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ l) (m≤m+n (sizeᵗ l) (sizeᵗ r)))
                       (≤-trans (nestDᵗ≤sizeᵗ r) (m≤n+m (sizeᵗ r) (sizeᵗ l)))))
      (≤-reflexive (sym (+-assoc (sizeᵗ s) (sizeᵗ l) (sizeᵗ r)))))
  nestDᵗ≤sizeᵗ (ifᵗ c a b)   =
    m≤n⇒m≤1+n (⊔-lub (⊔-lub
      (≤-trans (nestDᵗ≤sizeᵗ c) (≤-trans (m≤m+n (sizeᵗ c) (sizeᵗ a)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
      (≤-trans (nestDᵗ≤sizeᵗ a) (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))))
      (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
  nestDᵗ≤sizeᵗ (primᵗ _ a)   = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (strmᵗ e)     = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)

  nestDᵗˢ≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → nestDᵗˢ ts ≤ sizeᵗˢ ts
  nestDᵗˢ≤sizeᵗˢ []       = z≤n
  nestDᵗˢ≤sizeᵗˢ (y ∷ ys) =
    ⊔-lub (≤-trans (nestDᵗ≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
          (≤-trans (nestDᵗˢ≤sizeᵗˢ ys) (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))

-- AND THE SAME AT A STORED VALUE, which is where the store's own
-- places read it.  `Val` is computed from the `Ty`, so this recurses
-- on the type and meets the term induction above at exactly one
-- constructor: `obs`, where a value becomes syntax again.  Every
-- other arm is a max or a sum under a `suc` that the size already
-- pays for, so the depth reading of a store place is POINTWISE under
-- its size reading -- which is what lets a size cap discharge a depth
-- obligation with no induction over the machine at all.
nestDᵛ≤sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → nestDᵛ t v ≤ sizeᵛ t v
nestDᵛ≤sizeᵛ unitᵗ    _        = z≤n
nestDᵛ≤sizeᵛ boolᵗ    _        = z≤n
nestDᵛ≤sizeᵛ natᵗ     _        = z≤n
nestDᵛ≤sizeᵛ (s ×ᵗ t) (a , b)  =
  m≤n⇒m≤1+n (⊔-lub (≤-trans (nestDᵛ≤sizeᵛ s a) (m≤m+n (sizeᵛ s a) (sizeᵛ t b)))
                   (≤-trans (nestDᵛ≤sizeᵛ t b) (m≤n+m (sizeᵛ t b) (sizeᵛ s a))))
nestDᵛ≤sizeᵛ (s +ᵗ t) (inj₁ a) = m≤n⇒m≤1+n (nestDᵛ≤sizeᵛ s a)
nestDᵛ≤sizeᵛ (s +ᵗ t) (inj₂ b) = m≤n⇒m≤1+n (nestDᵛ≤sizeᵛ t b)
nestDᵛ≤sizeᵛ (obs t)  e        = nestDᵉ≤sizeᵉ e
