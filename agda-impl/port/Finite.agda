{-# OPTIONS --guardedness #-}

-- FINITELY DEFERRED PROGRAMS.  Induction over a program is not structural
-- at `defer`: `Later.force` is not smaller.  A program's truncation at `n`
-- is one whose every `defer` nested `n` deep holds `empty`; it is
-- `Finite`, an inductive witness the recursion can descend, and it agrees
-- with the program for `n` steps, since a `defer` shows a skip before its
-- body.  A safety property closed under agreement at every depth then
-- holds of every program once it holds of every finite one.
module port.Finite where

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline)
open import denotation.MonotonicList using (Agree; _≈[_]_; agree; ≈ₖ-refl; ≈ₖ-sym; ≈ₖ-trans; ≈ₖ-pred)
open import denotation.Denote using (DenEnv; flatOp; approx)
open import denotation.Compositional using (EnvAgree; _∷ᵉ_; env-refl; lookup-agree; deferᴰ-contractive; from; toward)
open import denotation.NonExpansive using (mapᴰ-ne; scanᴰ-ne; takeWhileᴰ-ne; flatMapᴰ-ne; connectᴰ-ne)
import denotation.Unfold as U

-- Every `defer` nested `n` deep holds `empty`.
trunc : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Obs Timeline Γ A
trunc n       (cold c)          = cold c
trunc n       empty             = empty
trunc n       (of xs)           = of xs
trunc n       (map f s)         = map f (trunc n s)
trunc n       (scan f z s)      = scan f z (trunc n s)
trunc n       (takeWhile i q s) = takeWhile i q (trunc n s)
trunc n       (flatMap op f s)  = flatMap op (λ a → trunc n (f a)) (trunc n s)
trunc n       (connect s b)     = connect (trunc n s) (trunc n b)
trunc n       (connected i)     = connected i
trunc zero    (defer l)         = defer λ where .Later.force → empty
trunc (suc n) (defer l)         = defer λ where .Later.force → trunc n (Later.force l)

-- Finitely many `defer`s down every path.
data Finite : ∀ {Γ A} → Obs Timeline Γ A → Set₁ where
  cold-f      : ∀ {Γ A} c → Finite {Γ} {A} (cold c)
  empty-f     : ∀ {Γ A} → Finite {Γ} {A} empty
  of-f        : ∀ {Γ A} xs → Finite {Γ} {A} (of xs)
  map-f       : ∀ {Γ A B} {f : A → B} {s : Obs Timeline Γ A} → Finite s → Finite (map f s)
  scan-f      : ∀ {Γ A B} {f : B → A → B} {z} {s : Obs Timeline Γ A} → Finite s → Finite (scan f z s)
  takeWhile-f : ∀ {Γ A} {i q} {s : Obs Timeline Γ A} → Finite s → Finite (takeWhile i q s)
  flatMap-f   : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {s} → (∀ a → Finite (f a)) → Finite s → Finite (flatMap op f s)
  connect-f   : ∀ {Γ A B} {s : Obs Timeline Γ A} {b : Obs Timeline (A ∷ Γ) B} → Finite s → Finite b → Finite (connect s b)
  connected-f : ∀ {Γ A} i → Finite {Γ} {A} (connected i)
  defer-f     : ∀ {Γ A} {l : Later Timeline Γ A} → Finite (Later.force l) → Finite (defer l)

finite-trunc : ∀ {Γ A} n (o : Obs Timeline Γ A) → Finite (trunc n o)
finite-trunc n       (cold c)          = cold-f c
finite-trunc n       empty             = empty-f
finite-trunc n       (of xs)           = of-f xs
finite-trunc n       (map f s)         = map-f (finite-trunc n s)
finite-trunc n       (scan f z s)      = scan-f (finite-trunc n s)
finite-trunc n       (takeWhile i q s) = takeWhile-f (finite-trunc n s)
finite-trunc n       (flatMap op f s)  = flatMap-f (λ a → finite-trunc n (f a)) (finite-trunc n s)
finite-trunc n       (connect s b)     = connect-f (finite-trunc n s) (finite-trunc n b)
finite-trunc n       (connected i)     = connected-f i
finite-trunc zero    (defer l)         = defer-f empty-f
finite-trunc (suc n) (defer l)         = defer-f (finite-trunc n (Later.force l))

-- Approximant `n` cuts where the truncation does.
approx-trunc : ∀ {Γ A k} n (o : Obs Timeline Γ A) {ρ σ : DenEnv Γ} → EnvAgree k ρ σ → approx n (trunc n o) ρ ≈[ k ] approx n o σ
approx-trunc n       (cold c)          e = ≈ₖ-refl _
approx-trunc n       empty             e = ≈ₖ-refl _
approx-trunc n       (of xs)           e = ≈ₖ-refl _
approx-trunc n       (map f s)         e = mapᴰ-ne f (approx-trunc n s e)
approx-trunc n       (scan f z s)      e = scanᴰ-ne f z (approx-trunc n s e)
approx-trunc n       (takeWhile i q s) e = takeWhileᴰ-ne i q (approx-trunc n s e)
approx-trunc n       (flatMap op f s)  e = flatMapᴰ-ne (flatOp op) (approx-trunc n s e) λ a → approx-trunc n (f a) e
approx-trunc n       (connect s b)     e = connectᴰ-ne (approx-trunc n s e) λ rr → approx-trunc n b (rr ∷ᵉ e)
approx-trunc n       (connected i)     e = lookup-agree e i
approx-trunc zero    (defer l)         e = ≈ₖ-refl _
approx-trunc (suc n) (defer l)         e = ≈ₖ-pred (deferᴰ-contractive (approx-trunc n (Later.force l) e))

-- A program subscribed agrees with its truncation at `n` for `n` steps.
trunc-agree : ∀ {Γ A} n (o : Obs Timeline Γ A) p (ρ : U.NEnv Γ)
            → Agree n (U.meaning (U.subscribe (trunc n o) p) ρ) (U.meaning (U.subscribe o p) ρ)
trunc-agree n o p ρ = agree
  (≈ₖ-trans (U.subscribed (trunc n o) (env-refl (U.hots ρ)))
  (≈ₖ-trans (from n (trunc n o) (U.hots ρ))
  (≈ₖ-trans (approx-trunc n o (env-refl (U.hots ρ)))
  (≈ₖ-trans (toward n o (U.hots ρ))
            (≈ₖ-sym (U.subscribed o (env-refl (U.hots ρ)))))))) p
