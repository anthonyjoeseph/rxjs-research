------------------------------------------------------------------
-- WHAT THE SUBSCRIBE BUDGET `k` IS ACTUALLY COUNTING, and the two
-- things it is NOT.
--
-- k descends at exactly one place — `sLvlD S W d (suc k) J ↦
-- opIterD S W d k …` — so the receipt pass needs a hypothesis that
-- steps by one at the μ edge and is preserved everywhere else.  Two
-- candidates fail, and this probe is the record of why; the one that
-- works is in .Verify-Budget-Sufficient.Caps-Nest, where `M` and its
-- edge steps live, on .Measures' `syncSize-unfoldμ`.
--
-- § 1  A BARE `1 ≤ k` IS NOT MAINTAINABLE.  Chain walking (`op-step`,
--   `op-step-eval`) keeps k and decrements m; the payload walk
--   (`walk-step`) keeps k; a frame REFRESHES it.  So the one
--   k-consuming recursion inside a subscribe's own subtree is
--   `op-step-mu`, and `subscribeE-caps`'s μ clause calls itself at
--   `k − 1` — which a side condition saying only "there is budget left"
--   cannot supply.  The maintenance step at k = 1 demands `1 ≤ 0`.
--
-- § 2  AND A TERM-ONLY MEASURE DOES NOT SURVIVE THE SHARE EDGE.
--   `sharedConnect` is a nesting edge like μ — it peels a gas and calls
--   `subscribeE` — but its callee is the SLOT'S STORED DEFINITION, and
--   the evaluator says so in as many words (Rx.Evaluator, above
--   `sharedConnect`): "the def d is a stored expression, STRUCTURALLY
--   UNRELATED to the `input i` being subscribed".  The caller's term is
--   `input i`, whose syncSize is 1, so a hypothesis speaking only of
--   the subscribed term has ONE unit to spend on a callee that may need
--   anything up to the size cap.
--
-- That second refutation is the whole reason the landed measure carries
-- a residue over the unconnected shares rather than the term alone.
------------------------------------------------------------------
module Mu-Nest-Probe where

open import Data.Nat  using (ℕ; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Fin  using (Fin; zero)
open import Data.List using ([])
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)

open import Rx.Exp
  using (Ctx; Closed; Ty; natᵗ; input; emptyᵉ; syncSizeᵉ)

------------------------------------------------------------------
-- § 1.  THE BARE SIDE CONDITION, stated as the maintenance step it
-- would have to be, and refuted at the only place it could fail
------------------------------------------------------------------

One≤K-Maintains : Set
One≤K-Maintains = ∀ (k : ℕ) → 1 ≤ suc k → 1 ≤ k

one≤k-absurd : One≤K-Maintains → ⊥
one≤k-absurd H with H 0 (s≤s z≤n)
... | ()

------------------------------------------------------------------
-- § 2.  THE TERM-ONLY MEASURE AT THE SHARE EDGE, refuted at k = 0 with
-- the smallest slot there is
------------------------------------------------------------------

Plain-Share-Maintains : Set
Plain-Share-Maintains = ∀ {n} {Γ : Ctx n} {t} (i : Fin n) (d : Closed Γ t) (k : ℕ) →
  syncSizeᵉ (input {Γ = Γ} {Δᵍ = []} {Δ = []} {Θ = []} i) ≤ suc k →
  syncSizeᵉ d ≤ k

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

plain-share-absurd : Plain-Share-Maintains → ⊥
plain-share-absurd H with H {Γ = Γ₁} {t = natᵗ} zero emptyᵉ 0 (s≤s z≤n)
... | ()
