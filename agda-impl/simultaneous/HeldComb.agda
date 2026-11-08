{-# OPTIONS --guardedness #-}

-- A FLATMAP'S SCAN HOLDS WHAT ITS SOURCE PROMISES.  The scan steps
-- `react` over each row its source meets and lays the step's outputs
-- under that row, the `j`-th at `q ++ ix 1 ∷ ix j ∷ []`; past the
-- source's end it ends at the same position.  So what the scanned
-- stream holds is read off its source's rows alone: what a begin is
-- named, what precedes an over, and, run by run, the counts of the
-- outputs laid out (`CombIn`).
module simultaneous.HeldComb where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; scan)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; DenEnv; ⟦_⟧; approx)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; _⊑_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over)
open import simultaneous.SObs using (flat; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Routed using (Held; Carried; cnt; Ex; nameOf; Early; Valued; opos; Routing)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count; Out; Input; react; each)

------------------------------------------------------------------------
-- What the scan lays out

-- The meaning, or its n-th approximant.
ev : Maybe ℕ → ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
ev nothing  o ρ = ⟦ o ⟧ ρ
ev (just n) o ρ = approx n o ρ

-- The scan's first state: nothing counted, no output.
init : ∀ {B} → Out B
init = flat root 0 0 false false false false 0 0 0 0 0 [] , []

-- A step's outputs, laid under the row that caused them.
lay : ∀ {B} → Pos → ℕ → List (IE B) → List (Pos × Ev (IE B))
lay q j []       = []
lay q j (x ∷ xs) = (q ++ ix 1 ∷ ix j ∷ [] , out x) ∷ lay q (suc j) xs

-- Every output a run of the source causes, from a state, then the end.
outRows : ∀ {B} → FlatOp → Out B → List (Pos × Ev (Maybe (Input B))) → List (Pos × Ev (IE B))
outRows op o []                  = []
outRows op o ((q , out x) ∷ rx)  = lay q 0 (proj₂ (react op o x)) ++ outRows op (react op o x) rx
outRows op o ((q , end) ∷ rx)    = (q , end) ∷ []
outRows op o ((q , skip) ∷ rx)   = outRows op o rx
outRows op o ((q , pin _) ∷ rx)  = outRows op o rx

------------------------------------------------------------------------
-- Held, run by run

-- What `Held` asks of one run met.
record RunHeld {A : Set} (cs : List Pos) (rs : List (Pos × Ev (IE A))) : Set where
  field
    covered : ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    current : ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → proj₂ (cnt r₁) ≡ 0 ⊎ proj₁ (cnt r₁) ≡ nameOf y
    shut    : ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (cnt r₁) ≡ 0
            → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁)))) ∈ r₁
            → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → instantOf y ≡ instantOf q → ⊥

-- Held is its rows' facts and every run's.
held-runs : ∀ {A} {t : EmissionSet (IE A)} {cs}
          → (∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y)
          → (∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m)
          → (∀ {y a n} → t y (out (instEmit (value a) n)) → Early y)
          → (∀ {y} → t y end → Early y)
          → (∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (instantOf y) × opos (instantOf y) ⊑ y)
          → (∀ {rs} → Met t rs → RunHeld cs rs)
          → Held t cs
held-runs nm rt ea en lt rh = record
  { named = nm
  ; covered = λ m → RunHeld.covered (rh m)
  ; exact = λ m → RunHeld.exact (rh m)
  ; routing = rt
  ; shut = λ m r₁ r₂ e z bq vy iq → RunHeld.shut (rh m) r₁ r₂ e z bq vy iq
  ; early = ea
  ; ends = en
  ; late = lt
  ; current = λ m → RunHeld.current (rh m)
  }

------------------------------------------------------------------------
-- What the source promises

record CombIn {B : Set} (op : FlatOp) (M : EmissionSet (Maybe (Input B))) (cs : List Pos) : Set where
  field
    named  : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
    early  : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
    ends   : ∀ {q} → M q end → Early q
    late   : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (instantOf q) × opos (instantOf q) ⊑ q
    runs   : ∀ {rx} → Met M rx → RunHeld cs (outRows op init rx)

-- THE SCANNED STREAM HOLDS what its source promises: a run met of it is
-- laid out from a run met of the source, a prefix of what that run lays.
postulate
  comb-held : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs → GoodEnv ρ → Ok (Hots ρ) P
            → CombIn op (enter (ev m s ρ) P) cs → Held (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) cs
