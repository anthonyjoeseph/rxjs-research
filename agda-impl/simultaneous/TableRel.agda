{-# OPTIONS --guardedness #-}

-- THE POSITION MAP, PER SUBTERM.  A subterm's plain cuts and its
-- elaborated cuts, subscribed at `s` and `s*`, correspond along a map of
-- positions per cut (`Rel`), read off the cuts' tables and never
-- asserted: the map, the late placement, the correspondence of the two
-- tables at each cut, and the lifting facts that carry agreement between
-- cuts across it.  `rel` builds the record by recursion over the tree,
-- each former's case from its children's, in any environment whose hots
-- are related as the record relates them (`EnvR`): a `connected` meets
-- its hot through the environment, and a `connect` relates the plain hot
-- to its annotated, read one for its body.
--
-- Each case touches only its own operator: a one-to-one former carries
-- its child's record through its operator's table (`map-tab`,
-- `scan-tab`, `take-tab`, `defer-tab`); `flatMap` and `connect` take
-- their children's records for every environment, so their cases never
-- unfold a child's elaboration.  The cuts are at least three rows deep,
-- past the elaboration's own leaves.
module simultaneous.TableRel where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_)
open import Function using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; skip; pin; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; short; bind; _⊣_; mapRows; scanRows; takeRows)
open import simultaneous.InstEmit using (valuesOf; begin)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Listing using (listC; UncutEnv; spinRows)
open import simultaneous.Attribution using (Every; One; Reads; Match; Shown)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; elaborate; mapIE; scanIE; passes; marked)

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
-- the cut; and agreement crosses between cuts along the map, up to an
-- image and back, up to a late placement, from a row of the instant a
-- row leads to its image, and everywhere.
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

------------------------------------------------------------------------
-- The subterm's two families of tables

-- The elaboration's scope for a plain scope.
Ren : List Set → List Set → Set₁
Ren Γ Δ = ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ

Tab : ∀ {Γ A} → ℕ → Obs Timeline Γ A → (ℕ → All Tb.Listed Γ) → Pos → ℕ → Maybe (Tb.Listed A)
Tab n o ρ p N = listC (3 + N) n o (ρ N) p

Tab* : ∀ {Γ Δ A} → ℕ → Ren Γ Δ → Obs Timeline Γ A → (ℕ → All Tb.Listed Δ) → Pos → ℕ → Maybe (Tb.Listed (IE A))
Tab* n ρι o ρ* p N = listC (3 + N) n (elab ρι o) (ρ* N) p

-- Wherever the two are subscribed.
Holds : ∀ {Γ Δ A} → ℕ → Obs Timeline Γ A → (ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → Set₁
Holds n o ρ ρι ρ* = ∀ p p* → Rel (Tab n o ρ p) (Tab* n ρι o ρ* p*) p p*

-- Every hot in scope, read where a `connected` reads it.
EnvR : ∀ {Γ Δ} → (ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → Set₁
EnvR {Γ} ρ ρι ρ* = ∀ {X} (i : X ∈ Γ) n → Holds n (connected i) ρ ρι ρ*

-- In every environment of uncut tables whose hots are related.
Full : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Set₁
Full {Γ} n o = ∀ (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N))
             → ∀ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → (∀ N → UncutEnv (ρ* N)) → EnvR ρ ρι ρ* → Holds n o ρ ρι ρ*

------------------------------------------------------------------------
-- Each former's case

postulate
  -- THE LEAVES.
  -- RECOVERY: git show e63b1f32 restores the per-former inversions of an elaborated run over approx (simultaneous/ReadRows.agda, ReadLane, ReadMap, ReadFold, FlatRows, ToldRows), each to be restated over the tables for its former's case.
  cold-rel : ∀ {Γ A} n (c : Timeline A) → Full {Γ} n (cold c)
  empty-rel : ∀ {Γ A} n → Full {Γ} {A} n empty
  of-rel    : ∀ {Γ A} n (xs : List A) → Full {Γ} n (of xs)
  spin-tab  : ∀ {A} p p* → Rel {A} (λ N → just (spinRows (3 + N) p ⊣ false)) (λ N → just (spinRows (3 + N) p* ⊣ false)) p p*

  -- THE ONE-TO-ONE FORMERS carry a record through their operator.
  map-tab   : ∀ {A B} (f : A → B) {P Q s s*} → Rel P Q s s*
            → Rel (λ N → bind (P N) λ l → just (mapRows f l)) (λ N → bind (Q N) λ l → just (mapRows (mapIE f) l)) s s*
  scan-tab  : ∀ {A B} (f : B → A → B) (z : B) {P Q s s*} → Rel P Q s s*
            → Rel (λ N → bind (P N) λ l → just (scanRows f z l))
                  (λ N → bind (bind (Q N) λ l → just (scanRows (scanIE f) (z , marked begin) l)) λ l → just (mapRows proj₂ l)) s s*
  take-tab  : ∀ {A} (i : Bool) (q : A → Bool) {P Q s s*} → Rel P Q s s*
            → Rel (λ N → bind (P N) λ l → just (takeRows i q l)) (λ N → bind (Q N) λ l → just (takeRows i (passes q) l)) s s*
  defer-tab : ∀ {A} p p* {P Q} → Rel {A} P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ])
            → Rel (λ N → bind (P N) λ b → just (((p ⊕ [ ix 0 ] , skip) ∷ rows b) ⊣ short b))
                  (λ N → bind (Q N) λ b → just (((p* ⊕ [ ix 0 ] , skip) ∷ rows b) ⊣ short b)) p p*

  -- THE TWO FORMERS WITH CONTENT, over their children's records in
  -- every environment.
  flat-rel  : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
            → Full n s → (∀ a → Full n (f a)) → Full n (flatMap op f s)
  conn-rel  : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
            → Full n s → Full n b → Full n (connect s b)

  -- THE TOP: the program's elaboration, under the batcher's own
  -- plumbing, subscribed where the program is.
  top-rel   : ∀ {A} n (o : Obs Timeline [] A)
            → Rel (Tab n o (λ _ → []) root) (Tab* n (λ i → i) o (λ _ → []) (root ⊕ (ix 0 ∷ ix 1 ∷ ix 1 ∷ []))) root (root ⊕ (ix 0 ∷ ix 1 ∷ ix 1 ∷ []))
            → Rel (Tab n o (λ _ → []) root) (λ N → listC (3 + N) n (elaborate o) [] root) root root

-- EVERY SUBTERM'S CUTS CORRESPOND.
rel : ∀ {Γ A} n (o : Obs Timeline Γ A) → Full n o
rel n (cold c)          = cold-rel n c
rel n empty             = empty-rel n
rel n (of xs)           = of-rel n xs
rel n (map f s)         ρ uρ ρι ρ* uρ* env p p* = map-tab f (rel n s ρ uρ ρι ρ* uρ* env p p*)
rel n (scan f z s)      ρ uρ ρι ρ* uρ* env p p* = scan-tab f z (rel n s ρ uρ ρι ρ* uρ* env p p*)
rel n (takeWhile i q s) ρ uρ ρι ρ* uρ* env p p* = take-tab i q (rel n s ρ uρ ρι ρ* uρ* env p p*)
rel n (flatMap op f s)  = flat-rel n op f s (rel n s) (λ a → rel n (f a))
rel n (connect s b)     = conn-rel n s b (rel n s) (rel n b)
rel n (connected i)     ρ uρ ρι ρ* uρ* env = env i n
rel zero    (defer l)   ρ uρ ρι ρ* uρ* env p p* = spin-tab p p*
rel (suc n) (defer l)   ρ uρ ρι ρ* uρ* env p p* = defer-tab p p* (rel n (Later.force l) ρ uρ ρι ρ* uρ* env (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]))
