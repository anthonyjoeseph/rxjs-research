{-# OPTIONS --guardedness #-}

-- WHAT IT IS FOR A SUBTERM'S CUTS TO CORRESPOND (`Rel`): the record
-- `simultaneous.TableRel.rel` builds former by former, and the tables'
-- rows (`TR`) and shapes (`Sh`) it is stated over.
module simultaneous.TableCorr where

open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Every; One; Reads; Match; Shown)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- An event's value mapped, its constructor kept.
ev : ∀ {A B : Set} → (A → B) → Ev A → Ev B
ev f (out a) = out (f a)
ev f skip    = skip
ev f end     = end
ev f (pin r) = pin r

-- A run's shape: where its rows lie, and of what constructor.
Sh : ∀ {X : Set} → EmissionSet X → EmissionSet ⊤
Sh {X} a y e = Σ (Ev X) λ e₀ → a y e₀ × e ≡ ev (λ _ → tt) e₀

-- Agreement between runs carries to runs holding the same rows.
ag-≃ : ∀ {X : Set} {a a′ b b′ : EmissionSet X} {q}
     → (∀ {k e} → a k e → a′ k e) → (∀ {k e} → a′ k e → a k e) → (∀ {k e} → b k e → b′ k e) → (∀ {k e} → b′ k e → b k e)
     → AgreeTo q a b → AgreeTo q a′ b′
ag-≃ f f′ g g′ ⟨ a ⟩ = ⟨ (λ {y} {e} yq → (λ x → g (proj₁ (a {y} {e} yq) (f′ x))) , (λ x → f (proj₂ (a {y} {e} yq) (g′ x)))) ⟩

-- Rows of a cut program's table.
Rows : ∀ {X : Set} → Tb.Listed X → Pos → Ev X → Set
Rows L k e = (k , e) ∈ rows L

-- Rows of a table, if there is one.
TR : ∀ {X : Set} → Maybe (Tb.Listed X) → EmissionSet X
TR {X} m k e = Σ (Tb.Listed X) λ L → m ≡ just L × Rows L k e

M : ∀ {A : Set} → Ev A → Ev (IE A) → Set
M = Match Every (One valuesOf) (Reads valuesOf)

-- TWO RUNS CORRESPOND along `φ`, subscribed at `s` and `s*`: each
-- unpinned plain row on its image, a skip possibly put late instead, as
-- a pin is (`put`, homed in the subscription's instant or a carried
-- row's before it); each shown elaborated row back on a plain one; each
-- elaborated row in the subscription's instant or a carried row's, the
-- image at or before it unless the row leads its instant (an async
-- step's `begin` comes before the step's value); the images keeping the
-- order and the instants of the rows they image.
record Corr {A : Set} (s s* : Pos) (φ : Pos → Pos) (Put : Pos → Pos → Set) (L : EmissionSet A) (L* : EmissionSet (IE A)) : Set where
  Imaged : Pos → Ev A → Set
  Imaged k e = Σ (Ev (IE A)) λ e′ → L* (φ k) e′ × M e e′

  Homed : Pos → Set
  Homed k = instantOf k ≡ instantOf s ⊎ Σ Pos λ k₀ → Σ (Ev A) λ e₀ → L k₀ e₀ × Unpinned e₀ × Imaged k₀ e₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k

  PutAt : Pos → Set
  PutAt k = (Σ Pos λ l → Σ (Ev (IE A)) λ e′ → L* l e′ × Put k l) × Homed k

  -- No unpinned row of its instant lies before `k`.
  Leads : Pos → Set
  Leads k = ∀ {k′ e′} → L k′ e′ → Unpinned e′ → instantOf k′ ≡ instantOf k → k ≼ k′

  field
    row→   : ∀ {k e} → L k e → Unpinned e → Imaged k e ⊎ (e ≡ skip × PutAt k)
    pin→   : ∀ {k p} → L k (pin p) → PutAt k
    shown← : ∀ {l e′} → L* l e′ → Shown (One valuesOf) e′
           → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ k × L k e × Unpinned e × M e e′
    place  : ∀ {m e′} → L* m e′
           → instantOf m ≡ instantOf s* ⊎ Σ Pos λ k → Σ (Ev A) λ e → L k e × Unpinned e × Imaged k e × (φ k ≼ m ⊎ Leads k) × instantOf (φ k) ≡ instantOf m
    mono   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ k ≺ φ k′
    inst   : ∀ {k k′ e e′} → L k e → L k′ e′ → Unpinned e → Unpinned e′
           → (instantOf (φ k) ≡ instantOf (φ k′) ⇔ instantOf k ≡ instantOf k′)
    home   : ∀ {k e} → L k e → Unpinned e → (instantOf (φ k) ≡ instantOf s* ⇔ instantOf k ≡ instantOf s)

-- A SUBTERM'S CUTS CORRESPOND, each along its own map and late
-- placement, read off the two families of tables: two cuts agreeing up to
-- a row map it alike; each position is imaged by finitely many, whatever
-- the cut; agreement crosses between cuts along the map, up to an image
-- and back, up to a late placement, from a row of the instant a row leads
-- to its image, and everywhere; and two cuts of either side agreeing in
-- shape up to a row agree there outright, a value a truncation changes
-- showing first as a row it removes.
record Rel {A : Set} (P : ℕ → Maybe (Tb.Listed A)) (Q : ℕ → Maybe (Tb.Listed (IE A))) (s s* : Pos) : Set₁ where
  field
    φ           : ℕ → Pos → Pos
    Put         : ℕ → Pos → Pos → Set
    corr        : ∀ N → Corr s s* (φ N) (Put N) (TR (P N)) (TR (Q N))
    φ-agree     : ∀ {N N′ k} → AgreeTo k (TR (P N)) (TR (P N′)) → φ N k ≡ φ N′ k
    bk          : Pos → List Pos
    in-bk       : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ bk (φ N k)
    pb-few      : ∀ l → Σ (List Pos) λ ks → ∀ {N k} → Put N k l → k ∈ ks
    elab-causal : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo k (TR (P N′)) (TR (P N))
                → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N))
    stable←     : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N))
                → AgreeTo k (TR (P N′)) (TR (P N))
    stable-put  : ∀ {N N′ k l e′} → N ≤ N′ → AgreeTo k (TR (P N′)) (TR (P N)) → TR (Q N) l e′ → Put N k l
                → AgreeTo l (TR (Q N′)) (TR (Q N))
    stable-lead : ∀ {N N′ k e m} → N ≤ N′ → TR (P N) k e → Unpinned e → Corr.Leads (corr N) k
                → instantOf m ≡ instantOf (φ N k) → AgreeTo m (TR (Q N′)) (TR (Q N)) → AgreeTo (φ N k) (TR (Q N′)) (TR (Q N))
    elab-all    : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
    coh         : ∀ {N N′ k} → AgreeTo k (Sh (TR (P N))) (Sh (TR (P N′))) → AgreeTo k (TR (P N)) (TR (P N′))
    coh*        : ∀ {N N′ k} → AgreeTo k (Sh (TR (Q N))) (Sh (TR (Q N′))) → AgreeTo k (TR (Q N)) (TR (Q N′))
