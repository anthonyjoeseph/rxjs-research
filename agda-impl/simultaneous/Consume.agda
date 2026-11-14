{-# OPTIONS --guardedness #-}

-- THE ELABORATION SIMULATES ITS PROGRAM (`simultaneous.Sim`), former by
-- former, at every approximant: each former's leaf carries its
-- children's simulations to its own, and the closed program's, listed
-- whole, is the top's (`sim-root`).

module simultaneous.Consume where

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; <⇒<ᵇ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; _∙_; last; frame; cascade; tick)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; _≺_; enter; approx)
open import simultaneous.Listing using (Listing)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)
open import simultaneous.Sim using (PMap; Emb; Sim; ListedB; Shows; Shown; SimIH)
open import simultaneous.SimMap using (sim-map)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; elaborate)

------------------------------------------------------------------------
-- A finite run, listed

maxTick : List Pos → ℕ
maxTick []       = 0
maxTick (k ∷ ks) = tick k ⊔ maxTick ks

tick≤ : ∀ {k ks} → k ∈ ks → tick k ≤ maxTick ks
tick≤ {ks = k′ ∷ ks} (here refl) = m≤m⊔n (tick k′) (maxTick ks)
tick≤ {ks = k′ ∷ ks} (there m)   = ≤-trans (tick≤ m) (m≤n⊔m (tick k′) (maxTick ks))

-- A position past every one of a list: an instant at a later tick.
beyond : List Pos → Pos
beyond ks = cascade (suc (maxTick ks)) root last ∙ []

beyond-≺ : ∀ {k ks} → k ∈ ks → k ≺ beyond ks
beyond-≺ {frame ∙ _}         m = tt
beyond-≺ {cascade t e a ∙ _} {ks} m with t <ᵇ suc (maxTick ks) | <⇒<ᵇ (s≤s (tick≤ m))
... | true | _ = tt

-- A FINITE RUN THAT LISTS IS LISTED WHOLE, each row with its row: all of
-- it lies before a position past its rows.
listed-all : ∀ {A} {T : EmissionSet A} → Listing T → (ks : List Pos) → (∀ {k e} → T k e → k ∈ ks) → ListedB T nothing
listed-all lst ks every with lst {beyond ks} (ks , λ x _ → every x)
... | ks′ , cov , back = ks′ , (λ x _ → cov x (beyond-≺ (every x))) , λ m → proj₂ (back m)

-- EACH ELABORATED FORMER SIMULATES ITS FORMER when its children do.
postulate
  sim-cold      : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → SimIH n ρ (cold c)
  sim-empty     : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → SimIH n ρ (empty {A = A})
  sim-of        : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : List A) → SimIH n ρ (of xs)
  sim-scan      : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) (z : B) (s : Obs Timeline Γ A)
                → SimIH n ρ s → SimIH n ρ (scan f z s)
  sim-takeWhile : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (keep : A → Bool) (s : Obs Timeline Γ A)
                → SimIH n ρ s → SimIH n ρ (takeWhile i keep s)
  sim-flatMap   : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
                → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ s)
                → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → SimIH n ρ′ (f a)) → SimIH n ρ (flatMap op f s)
  sim-connect   : ∀ n {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                → SimIH n ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → SimIH n ρ′ b) → SimIH n ρ (connect s b)
  sim-connected : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → SimIH n ρ (connected i)
  -- THE BOTTOM APPROXIMANT, and each further one under a `defer`'s guard.
  sim-⊥         : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → SimIH zero ρ (defer l)
  sim-next      : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
                → SimIH n ρ (Later.force l) → SimIH (suc n) ρ (defer l)

sim-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → SimIH n ρ o
sim-approx n       ρ (cold c)          = sim-cold n ρ c
sim-approx n       ρ empty             = sim-empty n ρ
sim-approx n       ρ (of xs)           = sim-of n ρ xs
sim-approx n       ρ (map f s)         = sim-map n ρ f s (sim-approx n ρ s)
sim-approx n       ρ (scan f z s)      = sim-scan n ρ f z s (sim-approx n ρ s)
sim-approx n       ρ (takeWhile i p s) = sim-takeWhile n ρ i p s (sim-approx n ρ s)
sim-approx n       ρ (flatMap op f s)  = sim-flatMap n ρ op f s (λ ρ′ → sim-approx n ρ′ s) λ a ρ′ → sim-approx n ρ′ (f a)
sim-approx n       ρ (connect s b)     = sim-connect n ρ s b (sim-approx n ρ s) λ ρ′ → sim-approx n ρ′ b
sim-approx n       ρ (connected i)     = sim-connected n ρ i
sim-approx zero    ρ (defer l)         = sim-⊥ ρ l
sim-approx (suc n) ρ (defer l)         = sim-next n ρ l (sim-approx n ρ (Later.force l))

-- THE CLOSED PROGRAM: its elaboration, restamped beside the subscribe
-- and completion marks, simulates it from the root, wherever its rows
-- are listed.
postulate
  sim-top : ∀ n {A} (o : Obs Timeline [] A) → SimIH n (λ i → i) o → ListedB (enter (approx n o []) root) nothing → Σ PMap λ M → Emb M
          × Sim Shows Shown M nothing (enter (approx n o []) root) (enter (approx n (elaborate o) []) root)

sim-root : ∀ n {A} (o : SObs [] A) → ListedB (enter (approx n (plain o) []) root) nothing → Σ PMap λ M → Emb M
         × Sim Shows Shown M nothing (enter (approx n (plain o) []) root) (enter (approx n (elaborate (plain o)) []) root)
sim-root n o = sim-top n (plain o) (sim-approx n (λ i → i) (plain o))
