{-# OPTIONS --guardedness #-}

-- EVERY PROGRAM SHOWS ITS HANGS, under its meaning and under every
-- approximant.  By induction on the cover's size, then on the tree: each
-- operator keeps the size, and only a `defer`'s guard spends a position,
-- so its body is read one size down.  A bound reader is shown by its
-- environment.
module denotation.Laws.ShowsEv where

open import Data.List using (_++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline; ix)
open import denotation.EmissionSet using (DenEnv; enter; hot; ⟦_⟧; approx)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons; aft; defer-lim)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Worlds using (Ok; Lawful; InvD; Hots; GoodEnv; ok-step; _⊕_)
open import denotation.Laws.Shows using (ShowsK; shows-k; sk-same; sk-trunc; module Guard)
open import denotation.Laws.ShowsOps using (sk-cold; sk-empty; sk-of; sk-⊥; sk-map; sk-scan; sk-take; sk-connect)
open import denotation.Laws.ShowsJoin using (module Flat)

sk-⟦⟧ : ∀ n {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p → ShowsK n (enter (⟦ o ⟧ ρ) p)
sk-⟦⟧ n (cold c)          ρ g p ok = sk-cold c p
sk-⟦⟧ n empty             ρ g p ok = sk-empty p
sk-⟦⟧ n (of xs)           ρ g p ok = sk-of xs p
sk-⟦⟧ n (map f s)         ρ g p ok = sk-map f (⟦ s ⟧ ρ) p (sk-⟦⟧ n s ρ g p ok)
sk-⟦⟧ n (scan f z s)      ρ g p ok = sk-scan f z (⟦ s ⟧ ρ) p (sk-⟦⟧ n s ρ g p ok)
sk-⟦⟧ n (takeWhile i k s) ρ g p ok = sk-take i k (⟦ s ⟧ ρ) p (inv-⟦⟧ s ρ g p ok) (sk-⟦⟧ n s ρ g p ok)
sk-⟦⟧ n (flatMap op f s)  ρ g p ok =
  Flat.sk-flat (⟦ s ⟧ ρ) (λ a → ⟦ f a ⟧ ρ) (inv-⟦⟧ s ρ g) (λ a → inv-⟦⟧ (f a) ρ g) p ok
    (sk-⟦⟧ n s ρ g p ok) (λ a q okq → sk-⟦⟧ n (f a) ρ g q okq) op
sk-⟦⟧ n (connect s b)     ρ g p ok =
  sk-connect (⟦ s ⟧ ρ) F Is p ok (sk-⟦⟧ n s ρ g (p ++ [ ix 1 ]) (ok-step p ok))
    (sk-⟦⟧ n b (hot _ ∷ ρ) (good-cons (src-lawful {s = ⟦ s ⟧ ρ} {F = F} Is IF p ok) g) (p ++ [ ix 0 ]) (body-ok {s = ⟦ s ⟧ ρ} {F = F} Is IF p ok))
  where
    F = λ h → ⟦ b ⟧ (h ∷ ρ)
    Is = inv-⟦⟧ s ρ g
    IF : ∀ {t} → Lawful t → InvD (Hots ρ ⊕ t) (F (hot t))
    IF L = inv-⟦⟧ b (hot _ ∷ ρ) (good-cons L g)
sk-⟦⟧ n (connected i)     ρ g p ok = shows-k (proj₂ (g i) p)
sk-⟦⟧ n (defer l)         ρ g p ok =
  sk-same (λ x ¬y → ¬y (_ , proj₁ (defer-lim l ρ g p ok) x)) (λ x ¬y → ¬y (_ , proj₂ (defer-lim l ρ g p ok) x))
    (sk-trunc (Guard.sk-guard b p (λ x → proj₁ (aft b (inv-⟦⟧ (Later.force l) ρ g) p ok x)) (body n)))
  where
    b = ⟦ Later.force l ⟧ ρ
    body : ∀ n {m} → n ≡ suc m → ShowsK m (enter b (p ++ [ ix 1 ]))
    body zero    ()
    body (suc n) eq = subst (λ m → ShowsK m (enter b (p ++ [ ix 1 ]))) (suc-injective eq) (sk-⟦⟧ n (Later.force l) ρ g (p ++ [ ix 1 ]) (ok-step p ok))

sk-approx : ∀ n k {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ p → Ok (Hots ρ) p → ShowsK n (enter (approx k o ρ) p)
sk-approx n k       (cold c)          ρ g p ok = sk-cold c p
sk-approx n k       empty             ρ g p ok = sk-empty p
sk-approx n k       (of xs)           ρ g p ok = sk-of xs p
sk-approx n k       (map f s)         ρ g p ok = sk-map f (approx k s ρ) p (sk-approx n k s ρ g p ok)
sk-approx n k       (scan f z s)      ρ g p ok = sk-scan f z (approx k s ρ) p (sk-approx n k s ρ g p ok)
sk-approx n k       (takeWhile i c s) ρ g p ok = sk-take i c (approx k s ρ) p (inv-approx k s ρ g p ok) (sk-approx n k s ρ g p ok)
sk-approx n k       (flatMap op f s)  ρ g p ok =
  Flat.sk-flat (approx k s ρ) (λ a → approx k (f a) ρ) (inv-approx k s ρ g) (λ a → inv-approx k (f a) ρ g) p ok
    (sk-approx n k s ρ g p ok) (λ a q okq → sk-approx n k (f a) ρ g q okq) op
sk-approx n k       (connect s b)     ρ g p ok =
  sk-connect (approx k s ρ) F Is p ok (sk-approx n k s ρ g (p ++ [ ix 1 ]) (ok-step p ok))
    (sk-approx n k b (hot _ ∷ ρ) (good-cons (src-lawful {s = approx k s ρ} {F = F} Is IF p ok) g) (p ++ [ ix 0 ]) (body-ok {s = approx k s ρ} {F = F} Is IF p ok))
  where
    F = λ h → approx k b (h ∷ ρ)
    Is = inv-approx k s ρ g
    IF : ∀ {t} → Lawful t → InvD (Hots ρ ⊕ t) (F (hot t))
    IF L = inv-approx k b (hot _ ∷ ρ) (good-cons L g)
sk-approx n k       (connected i)     ρ g p ok = shows-k (proj₂ (g i) p)
sk-approx n zero    (defer l)         ρ g p ok = sk-⊥ p
sk-approx n (suc k) (defer l)         ρ g p ok =
  sk-trunc (Guard.sk-guard b p (λ x → proj₁ (aft b (inv-approx k (Later.force l) ρ g) p ok x)) (body n))
  where
    b = approx k (Later.force l) ρ
    body : ∀ n {m} → n ≡ suc m → ShowsK m (enter b (p ++ [ ix 1 ]))
    body zero    ()
    body (suc n) eq = subst (λ m → ShowsK m (enter b (p ++ [ ix 1 ]))) (suc-injective eq) (sk-approx n k (Later.force l) ρ g (p ++ [ ix 1 ]) (ok-step p ok))
