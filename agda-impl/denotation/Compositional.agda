{-# OPTIONS --guardedness #-}

-- COMPOSITIONALITY: a tree's meaning is its operator applied to its
-- children's meanings, up to `_≈_`.  `Denote` defines the meaning as a
-- limit of approximants, so this is what lets a proof about a program
-- reason one operator at a time instead of one approximant at a time.
--
-- The assembly: the approximants settle (`settles`), each approximant
-- reads its environment non-expansively (`approx-ne`), so each clause is
-- the operator's approximant moved to the limit by its non-expansiveness.
-- The operators' non-expansiveness is `denotation.NonExpansive`'s, and
-- `deferᴰ` is contractive outright.
module denotation.Compositional where

open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (ix; idle)
open import denotation.MonotonicList using (MonotonicList; coldᴰ; skip⁼; stop; stopᵀ; agreeᵀ-refl; _≈[_]_; agrees; agree; agreeᵀ; _≈_;
  Settling; Contractive; lub-limit; ≈ₖ-refl; ≈ₖ-sym; ≈ₖ-trans; ≈ₖ-pred; emptyᴰ; ofᴰ; mapᴰ;
  scanᴰ; takeWhileᴰ; flatMapᴰ; connectᴰ; deferᴰ)
open import denotation.Denote using (DenEnv; flatOp)
import denotation.Denote as D
open import denotation.NonExpansive using (mapᴰ-ne; scanᴰ-ne; takeWhileᴰ-ne; flatMapᴰ-ne; connectᴰ-ne)

-- A `defer` shows a skip before its body, so it settles one step more.
deferᴰ-contractive : ∀ {A} → Contractive (deferᴰ {A})
deferᴰ-contractive xy = agrees (λ p → agreeᵀ-refl _ idle) λ p → skip⁼ (agreeᵀ xy (p ++ [ ix 1 ])) (agree xy (p ++ [ ix 1 ]))

------------------------------------------------------------------------
-- Environments agreeing for k steps, handle by handle.

data EnvAgree (k : ℕ) : ∀ {Γ} → DenEnv Γ → DenEnv Γ → Set₁ where
  []ᵉ  : EnvAgree k [] []
  _∷ᵉ_ : ∀ {A Γ} {r r′ : MonotonicList A} {ρ σ : DenEnv Γ}
       → r ≈[ k ] r′ → EnvAgree k ρ σ → EnvAgree k (r ∷ ρ) (r′ ∷ σ)

env-refl : ∀ {k Γ} (ρ : DenEnv Γ) → EnvAgree k ρ ρ
env-refl []      = []ᵉ
env-refl (r ∷ ρ) = ≈ₖ-refl r ∷ᵉ env-refl ρ

lookup-agree : ∀ {k Γ A} {ρ σ : DenEnv Γ} → EnvAgree k ρ σ → (i : A ∈ Γ) → lookup ρ i ≈[ k ] lookup σ i
lookup-agree (a ∷ᵉ _) (here refl) = a
lookup-agree (_ ∷ᵉ e) (there i)   = lookup-agree e i

-- Generic in the leaf, as the meaning is.
module Over {C : Set → Set₁} (leaf : ∀ {A} → C A → MonotonicList A) where

  open D.Over leaf using (approx; ⟦_⟧)

  -- An approximant reads its environment non-expansively.  Lexicographic
  -- on (n , tree), as `approx` is.
  approx-ne : ∀ {Γ A k} n (o : Obs C Γ A) {ρ σ : DenEnv Γ} → EnvAgree k ρ σ → approx n o ρ ≈[ k ] approx n o σ
  approx-ne n       (cold c)          e = ≈ₖ-refl _
  approx-ne n       empty             e = ≈ₖ-refl _
  approx-ne n       (of xs)           e = ≈ₖ-refl _
  approx-ne n       (map f s)         e = mapᴰ-ne f (approx-ne n s e)
  approx-ne n       (scan f z s)      e = scanᴰ-ne f z (approx-ne n s e)
  approx-ne n       (takeWhile i p s) e = takeWhileᴰ-ne i p (approx-ne n s e)
  approx-ne n       (flatMap op f s)  e = flatMapᴰ-ne (flatOp op) (approx-ne n s e) λ a → approx-ne n (f a) e
  approx-ne n       (connect s b)     e = connectᴰ-ne (approx-ne n s e) λ rr → approx-ne n b (rr ∷ᵉ e)
  approx-ne n       (connected i)     e = lookup-agree e i
  approx-ne zero    (defer l)         e = ≈ₖ-refl _
  approx-ne (suc n) (defer l)         e = ≈ₖ-pred (deferᴰ-contractive (approx-ne n (Later.force l) e))

  -- Approximant n agrees with the next for n steps: every cut sits under
  -- n `defer`s, each a skip before it.
  settle : ∀ {Γ A} n (o : Obs C Γ A) (ρ : DenEnv Γ) → approx n o ρ ≈[ n ] approx (suc n) o ρ
  settle n       (cold c)          ρ = ≈ₖ-refl _
  settle n       empty             ρ = ≈ₖ-refl _
  settle n       (of xs)           ρ = ≈ₖ-refl _
  settle n       (map f s)         ρ = mapᴰ-ne f (settle n s ρ)
  settle n       (scan f z s)      ρ = scanᴰ-ne f z (settle n s ρ)
  settle n       (takeWhile i p s) ρ = takeWhileᴰ-ne i p (settle n s ρ)
  settle n       (flatMap op f s)  ρ = flatMapᴰ-ne (flatOp op) (settle n s ρ) λ a → settle n (f a) ρ
  settle n       (connect s b)     ρ = connectᴰ-ne (settle n s ρ) λ {r} {r′} rr →
    ≈ₖ-trans (approx-ne n b (rr ∷ᵉ env-refl ρ)) (settle n b (r′ ∷ ρ))
  settle n       (connected i)     ρ = ≈ₖ-refl _
  settle zero    (defer l)         ρ = agrees (λ p → stopᵀ) λ p → stop
  settle (suc n) (defer l)         ρ = deferᴰ-contractive (settle n (Later.force l) ρ)

  settles : ∀ {Γ A} (o : Obs C Γ A) (ρ : DenEnv Γ) → Settling (λ n → approx n o ρ)
  settles o ρ n = settle n o ρ

  -- Approximant k is the meaning for k steps.
  toward : ∀ {Γ A} k (o : Obs C Γ A) (ρ : DenEnv Γ) → approx k o ρ ≈[ k ] ⟦ o ⟧ ρ
  toward k o ρ = lub-limit (settles o ρ) k


  -- The meaning is approximant k for k steps.
  from : ∀ {Γ A} k (o : Obs C Γ A) (ρ : DenEnv Γ) → ⟦ o ⟧ ρ ≈[ k ] approx k o ρ
  from k o ρ = ≈ₖ-sym (toward k o ρ)

  ------------------------------------------------------------------------
  -- THE THEOREM: each node's meaning is its operator's `MonotonicList`
  -- function applied to its children's meanings.

  record Compositional : Set₁ where
    field
      coldᶜ      : ∀ {Γ A} (c : C A) (ρ : DenEnv Γ) → ⟦ cold c ⟧ ρ ≈ leaf c
      emptyᶜ     : ∀ {Γ A} (ρ : DenEnv Γ) → ⟦ empty {Γ = Γ} {A = A} ⟧ ρ ≈ emptyᴰ
      ofᶜ        : ∀ {Γ A} (xs : List A) (ρ : DenEnv Γ) → ⟦ of xs ⟧ ρ ≈ ofᴰ xs
      mapᶜ       : ∀ {Γ A B} (f : A → B) (s : Obs C Γ A) ρ → ⟦ map f s ⟧ ρ ≈ mapᴰ f (⟦ s ⟧ ρ)
      scanᶜ      : ∀ {Γ A B} (f : B → A → B) z (s : Obs C Γ A) ρ → ⟦ scan f z s ⟧ ρ ≈ scanᴰ f z (⟦ s ⟧ ρ)
      takeWhileᶜ : ∀ {Γ A} i p (s : Obs C Γ A) ρ → ⟦ takeWhile i p s ⟧ ρ ≈ takeWhileᴰ i p (⟦ s ⟧ ρ)
      flatMapᶜ   : ∀ {Γ A B} op (f : A → Obs C Γ B) (s : Obs C Γ A) ρ
                 → ⟦ flatMap op f s ⟧ ρ ≈ flatMapᴰ (flatOp op) (λ a → ⟦ f a ⟧ ρ) (⟦ s ⟧ ρ)
      connectᶜ   : ∀ {Γ A B} (s : Obs C Γ A) (b : Obs C (A ∷ Γ) B) ρ
                 → ⟦ connect s b ⟧ ρ ≈ connectᴰ (⟦ s ⟧ ρ) (λ r → ⟦ b ⟧ (r ∷ ρ))
      connectedᶜ : ∀ {Γ A} (i : A ∈ Γ) (ρ : DenEnv Γ) → ⟦ connected i ⟧ ρ ≈ lookup ρ i
      deferᶜ     : ∀ {Γ A} (l : Later C Γ A) ρ → ⟦ defer l ⟧ ρ ≈ deferᴰ (⟦ Later.force l ⟧ ρ)

  compositional : Compositional
  compositional = record
    { coldᶜ      = λ c ρ k → from k (cold c) ρ
    ; emptyᶜ     = λ ρ k → from k empty ρ
    ; ofᶜ        = λ xs ρ k → from k (of xs) ρ
    ; mapᶜ       = λ f s ρ k → ≈ₖ-trans (from k (map f s) ρ) (mapᴰ-ne f (toward k s ρ))
    ; scanᶜ      = λ f z s ρ k → ≈ₖ-trans (from k (scan f z s) ρ) (scanᴰ-ne f z (toward k s ρ))
    ; takeWhileᶜ = λ i p s ρ k → ≈ₖ-trans (from k (takeWhile i p s) ρ) (takeWhileᴰ-ne i p (toward k s ρ))
    ; flatMapᶜ   = λ op f s ρ k → ≈ₖ-trans (from k (flatMap op f s) ρ)
                     (flatMapᴰ-ne (flatOp op) (toward k s ρ) λ a → toward k (f a) ρ)
    ; connectᶜ   = λ s b ρ k → ≈ₖ-trans (from k (connect s b) ρ)
                     (connectᴰ-ne (toward k s ρ) λ {r} {r′} rr →
                       ≈ₖ-trans (approx-ne k b (rr ∷ᵉ env-refl ρ)) (toward k b (r′ ∷ ρ)))
    ; connectedᶜ = λ i ρ k → from k (connected i) ρ
    ; deferᶜ     = λ l ρ k → ≈ₖ-pred (≈ₖ-trans (from (suc k) (defer l) ρ)
                     (deferᴰ-contractive (toward k (Later.force l) ρ)))
    }

open Over (λ c → coldᴰ (lower c)) public
