{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM KEEPS ITS ROUTES, former by former.  A stream
-- subscribed at `p` HOLDS (`Held`) when its begins are named for their
-- instants, none lies in a burst it is exempt for, every value, stop,
-- over and end outside those bursts finds the count holding a route of
-- its own instant, and its dead instants stay dead (`Shut`).
--
-- THE EXEMPT BURSTS are the subscribe bursts of the stream itself and of
-- every connect it reads under, each within its own instant: what runs
-- there runs synchronously under the subscription, so whatever route
-- covers it is held above, by the row that subscribed.
--
-- AN INSTANT'S NAME IS READ OFF THE INSTANT: the cold's step at `I`
-- renders under a lane at `I ++ [ ix 1 ]`, where `mint` is subscribed, and
-- a completion's step one queued lane and one `of` further down.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix; sub; last; inside)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over)
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Met; values; elaborated)
open import simultaneous.Shut using (Shut; r₀)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; AIE; Routes; count; elab; annotate)

------------------------------------------------------------------------
-- What a stream holds

-- The name a cold's step at instant `I` mints.
nm : Pos → Pos
nm (ix t ∷ sub e ∷ last ∷ []) = ix t ∷ sub e ∷ last ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ []
nm (ix t ∷ sub e ∷ l ∷ [])    = ix t ∷ sub e ∷ l ∷ ix 1 ∷ []
nm _                          = root

nameOf : Pos → Pos
nameOf y = nm (instantOf y)

-- `y` lies in the subscribe burst at `c`, within its instant.
Sync : Pos → Pos → Set
Sync c y = T (inside c y) × instantOf y ≡ instantOf c

-- In one of the bursts `cs`.
Ex : List Pos → Pos → Set
Ex cs y = Any (λ c → Sync c y) cs

-- The routes a run's rows leave counted.
cnt : ∀ {A} → List (Pos × Ev (IE A)) → Routes
cnt rs = L.foldl count r₀ (values rs)

-- A row a route carries: anything but a begin, and the end.
data Carried {A : Set} : Ev (IE A) → Set where
  c-value : ∀ {a n} → Carried (out (instEmit (value a) n))
  c-stop  : ∀ {n} → Carried (out (instEmit (mark stop) n))
  c-over  : ∀ {n} → Carried (out (instEmit (mark over) n))
  c-end   : Carried end

record Held {A : Set} (t : EmissionSet (IE A)) (cs : List Pos) : Set where
  field
    named   : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    late    : ∀ {y n} → t y (out (instEmit (mark begin) n)) → Ex cs y → ⊥
    covered : ∀ {rs} → Met t rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    shut    : Shut t

-- Held at every subscription, exempt for its own burst and `cs`.
HeldD : ∀ {A} → Den (IE A) → List Pos → Set
HeldD d cs = ∀ p → Held (enter d p) (p ∷ cs)

------------------------------------------------------------------------
-- Programs and their binders

-- The meaning, or its n-th approximant.
ev : Maybe ℕ → ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
ev nothing  o ρ = ⟦ o ⟧ ρ
ev (just n) o ρ = approx n o ρ

-- A connect's binder: its source annotated, read hot past the connect
-- at `at`, the source holding, and every burst it is exempt for one the
-- reader is exempt for too.
record Bound {X : Set} (d : Den (AIE X)) (cs : List Pos) : Set₁ where
  field
    {Θ}   : List Set
    m     : Maybe ℕ
    src   : Obs Timeline Θ (IE X)
    env   : DenEnv Θ
    at    : Pos
    outer : List Pos
    held  : HeldD (ev m src env) outer
    under : ∀ {c} → c ∈ at ∷ outer → c ∈ cs
    is    : d ≡ hot (Proper (enter (ev m (annotate src) env) (at ++ [ ix 1 ])))

EnvHeld : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Δ → List Pos → Set₁
EnvHeld {Γ} ρ env cs = ∀ {X} (i : X ∈ Γ) → Bound (lookup env (ρ (∈-map⁺ AIE i))) cs

-- Held under every environment of held binders.  A record, so that a
-- statement about a former is compared by its arguments, never by the
-- elaborated tree its meaning unfolds to.
record IH (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor ih
  field holds : ∀ (env : DenEnv Δ) cs → EnvHeld ρ env cs → HeldD (ev m (elab ρ o) env) cs

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER HOLDS when its children do, under the meaning
-- and under every approximant alike.
postulate
  held-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
  held-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → IH m ρ (empty {A = A})
  held-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
  held-map       : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → IH m ρ s → IH m ρ (map f s)
  held-scan      : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → IH m ρ s → IH m ρ (scan f z s)
  held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
  held-flatMap   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → IH m ρ s
                 → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
  held-connect   : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
                 → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
  held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)

-- THE BOTTOM APPROXIMANT shows only skips; each further one is the body
-- under a `defer`'s guard; the meaning is the approximants' limit.
postulate
  held-⊥    : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → IH (just zero) ρ (defer l)
  held-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
            → IH (just n) ρ (Later.force l) → IH (just (suc n)) ρ (defer l)
  held-lim  : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
            → (∀ n → IH (just n) ρ (defer l)) → IH nothing ρ (defer l)

held-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH (just n) ρ o
held-approx n       ρ (cold c)          = held-cold (just n) ρ c
held-approx n       ρ empty             = held-empty (just n) ρ
held-approx n       ρ (of xs)           = held-of (just n) ρ xs
held-approx n       ρ (map f s)         = held-map (just n) ρ f s (held-approx n ρ s)
held-approx n       ρ (scan f z s)      = held-scan (just n) ρ f z s (held-approx n ρ s)
held-approx n       ρ (takeWhile i p s) = held-takeWhile (just n) ρ i p s (held-approx n ρ s)
held-approx n       ρ (flatMap op f s)  = held-flatMap (just n) ρ op f s (held-approx n ρ s) λ a ρ′ → held-approx n ρ′ (f a)
held-approx n       ρ (connect s b)     = held-connect (just n) ρ s b (held-approx n ρ s) λ ρ′ → held-approx n ρ′ b
held-approx n       ρ (connected i)     = held-connected (just n) ρ i
held-approx zero    ρ (defer l)         = held-⊥ ρ l
held-approx (suc n) ρ (defer l)         = held-next n ρ l (held-approx n ρ (Later.force l))

held-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH nothing ρ o
held-⟦⟧ ρ (cold c)          = held-cold nothing ρ c
held-⟦⟧ ρ empty             = held-empty nothing ρ
held-⟦⟧ ρ (of xs)           = held-of nothing ρ xs
held-⟦⟧ ρ (map f s)         = held-map nothing ρ f s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (scan f z s)      = held-scan nothing ρ f z s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (takeWhile i p s) = held-takeWhile nothing ρ i p s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (flatMap op f s)  = held-flatMap nothing ρ op f s (held-⟦⟧ ρ s) λ a ρ′ → held-⟦⟧ ρ′ (f a)
held-⟦⟧ ρ (connect s b)     = held-connect nothing ρ s b (held-⟦⟧ ρ s) λ ρ′ → held-⟦⟧ ρ′ b
held-⟦⟧ ρ (connected i)     = held-connected nothing ρ i
held-⟦⟧ ρ (defer l)         = held-lim ρ l λ n → held-approx n ρ (defer l)

------------------------------------------------------------------------
-- The top

-- THE BATCHER'S SOURCE HOLDS: the elaborated program, restamped, beside
-- the subscribe and completion marks, exempt for the subscribe burst.
postulate
  held-top : ∀ {A} (o : SObs [] A) → IH nothing (λ i → i) o → Held (elaborated o) (root ∷ [])

held : ∀ {A} (o : SObs [] A) → Held (elaborated o) (root ∷ [])
held o = held-top o (held-⟦⟧ (λ i → i) o)

-- The elaborated program's instants stay dead.
shut : ∀ {A : Set} (o : SObs [] A) → Shut (elaborated o)
shut o = Held.shut (held o)
