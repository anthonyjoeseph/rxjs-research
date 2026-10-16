{-# OPTIONS --guardedness #-}

-- SEQUENCING: acts in sequence re-associated up to `_≗_`.  A bind hands
-- each continuation the weakening its binder reached, so the two
-- nestings differ by weakening twice against once along the composite,
-- which agree up to `_≗_`.
module adequacy.Seq where

open import Data.Unit using (⊤)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

open import operation.AbstractObservable using (module Heap; module Run; base; ref; sink; quiet; list; maybe; _⊗_; joins; fifo)
open import operation.PureObservable using (Pureᴾ)
open import adequacy.Strong using (module Strongly)
open import adequacy.Unsub using (module Unsubbing)

module Sequencing (R : Set) where
  open Heap using (_∋_; there; _⊑_; same; grow; _⨾_; wk∋)
  open Run (Pureᴾ R) using (Act; done; newRef; readRef; writeRef; register; send; finish; startCold; stop; stash; cancel; eff; under; diverge;
    unfold; wkAct; _>>=ᴬ_; _>>ᴬ_; El; wkEl; Env; wkEnv; Subject) renaming (here to hereᴬ)
  open Strongly R using (_≗_; done≗; newRef≗; readRef≗; writeRef≗; register≗; send≗; finish≗; startCold≗; stop≗; stash≗; cancel≗; eff≗;
    here≗; under≗; diverge≗; unfold≗; ≗-refl)
  open Unsubbing R using (≗-trans; bind≗)

  ⨾-assoc : ∀ {u v w x} (σ : u ⊑ v) (τ : v ⊑ w) (υ : w ⊑ x) → σ ⨾ (τ ⨾ υ) ≡ (σ ⨾ τ) ⨾ υ
  ⨾-assoc σ τ same     = refl
  ⨾-assoc σ τ (grow υ) = cong grow (⨾-assoc σ τ υ)

  wk∋-wk : ∀ {u v w k} (σ : u ⊑ v) (τ : v ⊑ w) (i : u ∋ k) → wk∋ τ (wk∋ σ i) ≡ wk∋ (σ ⨾ τ) i
  wk∋-wk σ same     i = refl
  wk∋-wk σ (grow τ) i = cong there (wk∋-wk σ τ i)

  wkEl-wk : ∀ {u v w} t (σ : u ⊑ v) (τ : v ⊑ w) (x : El u t) → wkEl t τ (wkEl t σ x) ≡ wkEl t (σ ⨾ τ) x
  wkEl-wk (base X)  σ τ x              = refl
  wkEl-wk (ref t)   σ τ r              = wk∋-wk σ τ r
  wkEl-wk (sink A)  σ τ s              = wk∋-wk σ τ s
  wkEl-wk quiet     σ τ q              = wk∋-wk σ τ q
  wkEl-wk (list t)  σ τ []             = refl
  wkEl-wk (list t)  σ τ (x ∷ xs)       = cong₂ _∷_ (wkEl-wk t σ τ x) (wkEl-wk (list t) σ τ xs)
  wkEl-wk (maybe t) σ τ nothing        = refl
  wkEl-wk (maybe t) σ τ (just x)       = cong just (wkEl-wk t σ τ x)
  wkEl-wk (s ⊗ t)   σ τ (x , y)        = cong₂ _,_ (wkEl-wk s σ τ x) (wkEl-wk t σ τ y)
  wkEl-wk (joins A) σ τ []             = refl
  wkEl-wk (joins A) σ τ ((s , j) ∷ xs) = cong₂ (λ a b → (a , j) ∷ b) (wk∋-wk σ τ s) (wkEl-wk (joins A) σ τ xs)
  wkEl-wk (fifo X)  σ τ xs             = refl

  subject≡ : ∀ {A w} {s s′ : Subject A w} → Subject.subscribers s ≡ Subject.subscribers s′ → Subject.closed s ≡ Subject.closed s′ → s ≡ s′
  subject≡ refl refl = refl

  wkEnv-wk : ∀ {Γ u v w} (σ : u ⊑ v) (τ : v ⊑ w) (e : Env Γ u) → wkEnv τ (wkEnv σ e) ≡ wkEnv (σ ⨾ τ) e
  wkEnv-wk σ τ []         = refl
  wkEnv-wk σ τ (st ∷ sts) = cong₂ _∷_ (subject≡ (wk∋-wk σ τ (Subject.subscribers st)) (wk∋-wk σ τ (Subject.closed st))) (wkEnv-wk σ τ sts)

  -- A continuation reached along a composite, either way it nests.
  from-⨾ : ∀ {u v w x B} (F : u ⊑ x → Act x B) (σ : u ⊑ v) (τ : v ⊑ w) (υ : w ⊑ x) → F (σ ⨾ (τ ⨾ υ)) ≗ F ((σ ⨾ τ) ⨾ υ)
  from-⨾ F σ τ υ = subst (λ ζ → F (σ ⨾ (τ ⨾ υ)) ≗ F ζ) (⨾-assoc σ τ υ) (≗-refl _)

  -- Weakened twice, as once along the composite.
  wk-wk : ∀ {u v w B} (σ : u ⊑ v) (τ : v ⊑ w) (m : Act u B) → wkAct τ (wkAct σ m) ≗ wkAct (σ ⨾ τ) m
  wk-wk σ τ (done b)                 = done≗ refl
  wk-wk σ τ (newRef t a k)           = newRef≗ (wkEl-wk t σ τ a) λ υ r → from-⨾ (λ ζ → k ζ r) σ τ υ
  wk-wk σ τ (readRef r k)            = readRef≗ (wk∋-wk σ τ r) λ υ x → from-⨾ (λ ζ → k ζ x) σ τ υ
  wk-wk σ τ (writeRef {t = t} r a k) = writeRef≗ (wk∋-wk σ τ r) (wkEl-wk t σ τ a) (wk-wk σ τ k)
  wk-wk σ τ (register n c x k)       = register≗ (λ a → wk-wk σ τ (n a)) (wk-wk σ τ c) (wk-wk σ τ x) λ υ s → from-⨾ (λ ζ → k ζ s) σ τ υ
  wk-wk σ τ (send s a k)             = send≗ (wk∋-wk σ τ s) (wk-wk σ τ k)
  wk-wk σ τ (finish s k)             = finish≗ (wk∋-wk σ τ s) (wk-wk σ τ k)
  wk-wk σ τ (startCold c s k)        = startCold≗ (wk∋-wk σ τ s) λ υ h → from-⨾ (λ ζ → k ζ h) σ τ υ
  wk-wk σ τ (stop h k)               = stop≗ (wk∋-wk σ τ h) (wk-wk σ τ k)
  wk-wk σ τ (stash m k)              = stash≗ (wk-wk σ τ m) λ υ q → from-⨾ (λ ζ → k ζ q) σ τ υ
  wk-wk σ τ (cancel q k)             = cancel≗ (wk∋-wk σ τ q) (wk-wk σ τ k)
  wk-wk σ τ (eff e k)                = eff≗ λ a → wk-wk σ τ (k a)
  wk-wk σ τ (hereᴬ k)                = here≗ λ p → wk-wk σ τ (k p)
  wk-wk σ τ (under l m k)            = under≗ (wk-wk σ τ m) (wk-wk σ τ k)
  wk-wk σ τ diverge                  = diverge≗
  wk-wk σ τ (unfold l e n c x k m)   =
    unfold≗ (wkEnv-wk σ τ e) (λ a → wk-wk σ τ (n a)) (wk-wk σ τ c) (wk-wk σ τ x) (λ υ q → from-⨾ (λ ζ → k ζ q) σ τ υ) (wk-wk σ τ m)

  -- Weakening a sequence, as weakening each act of it.
  seq-wk : ∀ {u v B} (σ : u ⊑ v) (n : Act u ⊤) (k : Act u B) → (wkAct σ n >>ᴬ wkAct σ k) ≗ wkAct σ (n >>ᴬ k)
  seq-wk σ (done b)                 k = ≗-refl _
  seq-wk σ (newRef t a k′)          k = newRef≗ refl λ υ r → bind≗ (≗-refl (k′ (σ ⨾ υ) r)) λ _ → wk-wk σ υ k
  seq-wk σ (readRef r k′)           k = readRef≗ refl λ υ x → bind≗ (≗-refl (k′ (σ ⨾ υ) x)) λ _ → wk-wk σ υ k
  seq-wk σ (writeRef r a k′)        k = writeRef≗ refl refl (seq-wk σ k′ k)
  seq-wk σ (register n c x k′)      k = register≗ (λ a → ≗-refl _) (≗-refl _) (≗-refl _) λ υ s → bind≗ (≗-refl (k′ (σ ⨾ υ) s)) λ _ → wk-wk σ υ k
  seq-wk σ (send s a k′)            k = send≗ refl (seq-wk σ k′ k)
  seq-wk σ (finish s k′)            k = finish≗ refl (seq-wk σ k′ k)
  seq-wk σ (startCold c s k′)       k = startCold≗ refl λ υ h → bind≗ (≗-refl (k′ (σ ⨾ υ) h)) λ _ → wk-wk σ υ k
  seq-wk σ (stop h k′)              k = stop≗ refl (seq-wk σ k′ k)
  seq-wk σ (stash m k′)             k = stash≗ (≗-refl _) λ υ q → bind≗ (≗-refl (k′ (σ ⨾ υ) q)) λ _ → wk-wk σ υ k
  seq-wk σ (cancel q k′)            k = cancel≗ refl (seq-wk σ k′ k)
  seq-wk σ (eff e k′)               k = eff≗ λ a → seq-wk σ (k′ a) k
  seq-wk σ (hereᴬ k′)               k = here≗ λ p → seq-wk σ (k′ p) k
  seq-wk σ (under l m k′)           k = under≗ (≗-refl _) (seq-wk σ k′ k)
  seq-wk σ diverge                  k = diverge≗
  seq-wk σ (unfold l e n c x k′ m)  k = unfold≗ refl (λ a → ≗-refl _) (≗-refl _) (≗-refl _) (λ υ q → ≗-refl _) (seq-wk σ m k)

  -- A sequence re-associated.
  seq-assoc : ∀ {w B} (m n : Act w ⊤) (k : Act w B) → ((m >>ᴬ n) >>ᴬ k) ≗ (m >>ᴬ (n >>ᴬ k))
  seq-assoc (done b)                n k = ≗-refl _
  seq-assoc (newRef t a k′)         n k = newRef≗ refl λ σ r → ≗-trans (seq-assoc (k′ σ r) (wkAct σ n) (wkAct σ k)) (bind≗ (≗-refl (k′ σ r)) λ _ → seq-wk σ n k)
  seq-assoc (readRef r k′)          n k = readRef≗ refl λ σ x → ≗-trans (seq-assoc (k′ σ x) (wkAct σ n) (wkAct σ k)) (bind≗ (≗-refl (k′ σ x)) λ _ → seq-wk σ n k)
  seq-assoc (writeRef r a k′)       n k = writeRef≗ refl refl (seq-assoc k′ n k)
  seq-assoc (register n′ c x k′)    n k = register≗ (λ a → ≗-refl _) (≗-refl _) (≗-refl _) λ σ s →
    ≗-trans (seq-assoc (k′ σ s) (wkAct σ n) (wkAct σ k)) (bind≗ (≗-refl (k′ σ s)) λ _ → seq-wk σ n k)
  seq-assoc (send s a k′)           n k = send≗ refl (seq-assoc k′ n k)
  seq-assoc (finish s k′)           n k = finish≗ refl (seq-assoc k′ n k)
  seq-assoc (startCold c s k′)      n k = startCold≗ refl λ σ h → ≗-trans (seq-assoc (k′ σ h) (wkAct σ n) (wkAct σ k)) (bind≗ (≗-refl (k′ σ h)) λ _ → seq-wk σ n k)
  seq-assoc (stop h k′)             n k = stop≗ refl (seq-assoc k′ n k)
  seq-assoc (stash m k′)            n k = stash≗ (≗-refl _) λ σ q → ≗-trans (seq-assoc (k′ σ q) (wkAct σ n) (wkAct σ k)) (bind≗ (≗-refl (k′ σ q)) λ _ → seq-wk σ n k)
  seq-assoc (cancel q k′)           n k = cancel≗ refl (seq-assoc k′ n k)
  seq-assoc (eff e k′)              n k = eff≗ λ a → seq-assoc (k′ a) n k
  seq-assoc (hereᴬ k′)              n k = here≗ λ p → seq-assoc (k′ p) n k
  seq-assoc (under l m k′)          n k = under≗ (≗-refl _) (seq-assoc k′ n k)
  seq-assoc diverge                 n k = diverge≗
  seq-assoc (unfold l e n′ c x k′ m) n k = unfold≗ refl (λ a → ≗-refl _) (≗-refl _) (≗-refl _) (λ σ q → ≗-refl _) (seq-assoc m n k)
