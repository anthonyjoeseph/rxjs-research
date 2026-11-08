{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM HOLDS (`simultaneous.Routed.Held`), former by
-- former, and so the batcher's source keeps its dead instants dead.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; ⟦_⟧; DenEnv; approx)
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Relations using (elaborated)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; HeldD; Early)
open import denotation.Laws.Worlds using (Hots; GoodEnv)
open import simultaneous.HeldMap using (held-map-den)
open import simultaneous.HeldScan using (held-scan-den)
open import simultaneous.HeldConnect using (held-conn; early-snoc)
open import denotation.Laws using (inv-⟦⟧; inv-approx; good-cons)
open import denotation.Laws.Worlds using (Ok; InvD; Lawful; TimerRoot; _⊕_; plain-untimed; plain-ix)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.InstEmit using (begin; valuesOf)
open import Data.Product using (_×_; _,_; proj₁)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; AIE; Routes; elab; annotate; marked; trackers; closer; combined; laneˢ; each)

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
    held  : HeldD (Hots env) (ev m src env) outer
    under : ∀ {c} → c ∈ at ∷ outer → c ∈ cs
    is    : d ≡ hot (Proper (enter (ev m (annotate src) env) (at ++ [ ix 1 ])))

EnvHeld : ∀ {Γ Δ} → (∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → DenEnv Δ → List Pos → Set₁
EnvHeld {Γ} ρ env cs = ∀ {X} (i : X ∈ Γ) → Bound (lookup env (ρ (∈-map⁺ AIE i))) cs

-- Held under every environment of held binders.  A record, so that a
-- statement about a former is compared by its arguments, never by the
-- elaborated tree its meaning unfolds to.
record IH (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) : Set₁ where
  constructor ih
  field holds : ∀ (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → HeldD (Hots env) (ev m (elab ρ o) env) cs

------------------------------------------------------------------------
-- The formers

-- EACH ELABORATED FORMER HOLDS when its children do, under the meaning
-- and under every approximant alike.
postulate
  held-cold      : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (c : Timeline A) → IH m ρ (cold c)
  held-empty     : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) → IH m ρ (empty {A = A})
  held-of        : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (xs : L.List A) → IH m ρ (of xs)
  held-takeWhile : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) i (p : A → _) s → IH m ρ s → IH m ρ (takeWhile i p s)
  held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)

held-map : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : A → B) s → IH m ρ s → IH m ρ (map f s)
held-map nothing  ρ f s (ih h) = ih λ env cs g eh → held-map-den f (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-map (just n) ρ f s (ih h) = ih λ env cs g eh → held-map-den f (approx n (elab ρ s) env) cs (h env cs g eh)

held-scan : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (f : B → A → B) z s → IH m ρ s → IH m ρ (scan f z s)
held-scan nothing  ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (⟦ elab ρ s ⟧ env) cs (h env cs g eh)
held-scan (just n) ρ f z s (ih h) = ih λ env cs g eh → held-scan-den f (z , marked begin) (approx n (elab ρ s) env) cs (h env cs g eh)

-- A binder held under `cs` is held under more.
widen : ∀ {X} {d : Den (AIE X)} {c cs} → Bound d cs → Bound d (c ∷ cs)
widen b = record
  { m = Bound.m b ; src = Bound.src b ; env = Bound.env b ; at = Bound.at b ; outer = Bound.outer b
  ; held = Bound.held b ; under = λ i → there (Bound.under b i) ; is = Bound.is b }

-- A connect shows its body, read over its source made hot.
conn-ev : ∀ m {Δ X B} (A′ : Obs Timeline Δ X) (B′ : Obs Timeline (X ∷ Δ) (IE B)) (env : DenEnv Δ) cs → GoodEnv env
        → ∀ p → Ok (Hots env) p → (TimerRoot p → ⊥) → Early p
        → (Lawful (Proper (enter (ev m A′ env) (p ++ [ ix 1 ])))
           → Ok (Hots env ⊕ Proper (enter (ev m A′ env) (p ++ [ ix 1 ]))) (p ++ [ ix 0 ]) → Early (p ++ [ ix 0 ])
           → Held (enter (ev m B′ (hot (Proper (enter (ev m A′ env) (p ++ [ ix 1 ]))) ∷ env)) (p ++ [ ix 0 ])) ((p ++ [ ix 0 ]) ∷ p ∷ cs))
        → Held (enter (ev m (connect A′ B′) env) p) (p ∷ cs)
conn-ev nothing A′ B′ env cs g p ok nt ep k =
  held-conn (⟦ A′ ⟧ env) (λ h → ⟦ B′ ⟧ (h ∷ env)) Is IF p ok nt cs
    (k (src-lawful {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok) (body-ok {s = ⟦ A′ ⟧ env} {F = λ h → ⟦ B′ ⟧ (h ∷ env)} Is IF p ok)
       (early-snoc (ix 0) (proj₁ ok) nt ep))
  where
    Is = inv-⟦⟧ A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ⊕ t) (⟦ B′ ⟧ (hot t ∷ env))
    IF L = inv-⟦⟧ B′ (hot _ ∷ env) (good-cons L g)
conn-ev (just n) A′ B′ env cs g p ok nt ep k =
  held-conn (approx n A′ env) (λ h → approx n B′ (h ∷ env)) Is IF p ok nt cs
    (k (src-lawful {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (body-ok {s = approx n A′ env} {F = λ h → approx n B′ (h ∷ env)} Is IF p ok)
       (early-snoc (ix 0) (proj₁ ok) nt ep))
  where
    Is = inv-approx n A′ env g
    IF : ∀ {t} → Lawful t → InvD (Hots env ⊕ t) (approx n B′ (hot t ∷ env))
    IF L = inv-approx n B′ (hot _ ∷ env) (good-cons L g)

held-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
             → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
held-connect m ρ s b (ih hs) hb = ih λ env cs g eh p ok nt ep →
  conn-ev m (annotate (elab ρ s)) _ env cs g p ok nt ep λ L ok₀ ep₀ →
    IH.holds (hb _) _ (p ∷ cs) (good-cons L g)
      (λ { (here refl) → record { m = m ; src = elab ρ s ; env = env ; at = p ; outer = cs ; held = hs env cs g eh
                                ; under = λ i → i ; is = refl }
         ; (there i)   → widen (eh i) })
      (p ++ [ ix 0 ]) ok₀ (plain-untimed p plain-ix) ep₀

-- A FLATMAP'S SCAN HOLDS, read past the three connects that share its
-- outer: the outer at `p ++ [ ix 1 ]`, the closer, then the real
-- flatMap, each made hot.  What it reads: the connects in scope, the
-- outer, the lanes and the closer.
module FlatHots (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
                (s : Obs Timeline Γ A) (env : DenEnv Δ) (p : Pos) where

  g : A → Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  g a = elab (λ i → there (there (ρ i))) (f a)

  tk : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)
  tk = trackers Γ 0 (λ i → there (there (there (ρ i))))

  real : Obs Timeline (IE B ∷ IE A ∷ Δ) (IE B)
  real = flatMap op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl))))

  p₀ p₀₀ : Pos
  p₀  = p ++ [ ix 0 ]
  p₀₀ = p₀ ++ [ ix 0 ]

  σ₁ : EmissionSet (IE A)
  σ₁ = Proper (enter (ev m (elab ρ s) env) (p ++ [ ix 1 ]))

  σ₂ : EmissionSet (IE B)
  σ₂ = Proper (enter (ev m closer (hot σ₁ ∷ env)) (p₀ ++ [ ix 1 ]))

  σ₃ : EmissionSet (IE B)
  σ₃ = Proper (enter (ev m real (hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ++ [ ix 1 ]))

  scanned : EmissionSet (IE B)
  scanned = enter (ev m (combined op tk) (hot σ₃ ∷ hot σ₂ ∷ hot σ₁ ∷ env)) (p₀₀ ++ [ ix 0 ])

postulate
  held-comb : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
              (env : DenEnv Δ) cs → GoodEnv env → EnvHeld ρ env cs → HeldD (Hots env) (ev m (elab ρ s) env) cs
            → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
            → ∀ p → Ok (Hots env) p → (TimerRoot p → ⊥) → Early p
            → Held (FlatHots.scanned m ρ op f s env p)
                   ((FlatHots.p₀₀ m ρ op f s env p ++ [ ix 0 ]) ∷ FlatHots.p₀₀ m ρ op f s env p ∷ FlatHots.p₀ m ρ op f s env p ∷ p ∷ cs)

held-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s → IH m ρ s
             → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
held-flatMap m ρ op f s (ih hs) hf = ih λ env cs g eh p ok nt ep →
  conn-ev m (elab ρ s) _ env cs g p ok nt ep λ L₁ ok₁ ep₁ →
    conn-ev m closer _ _ (p ∷ cs) (good-cons L₁ g) (p ++ [ ix 0 ]) ok₁ (plain-untimed p plain-ix) ep₁ λ L₂ ok₂ ep₂ →
      conn-ev m (FlatHots.real m ρ op f s env p) _ _ ((p ++ [ ix 0 ]) ∷ p ∷ cs) (good-cons L₂ (good-cons L₁ g))
        ((p ++ [ ix 0 ]) ++ [ ix 0 ]) ok₂ (plain-untimed (p ++ [ ix 0 ]) plain-ix) ep₂ λ _ _ _ →
        held-comb m ρ op f s env cs g eh (hs env cs g eh) hf p ok nt ep

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
