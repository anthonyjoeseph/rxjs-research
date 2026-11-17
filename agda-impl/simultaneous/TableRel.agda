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

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (skip)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; short; bind; _⊣_)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv; spinRows)
open import simultaneous.TableCorr using (Rel)
open import simultaneous.TableMap using (map-tab)
open import simultaneous.TableTake using (take-tab)
open import simultaneous.TableScan using (scan-tab)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; elaborate)

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
