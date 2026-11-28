{-# OPTIONS --guardedness #-}

-- THE SCAN READ ACROSS ONE ROW: a run meets every visible row before
-- one it meets (`run-catch`), and the scan past a row is the scan past
-- what came before, stepped once (`past-split`).  The outer's end cuts
-- the outer's routes while a lane runs or waits (`left-cut`).
module simultaneous.ScanPast where

open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; _≺_)
open import denotation.Read using (Run; _∷_; Visible; After)
open import denotation.Laws.Modulus using (≼-split)
open import simultaneous.SObs using (Flat; isZero; lone; module Elaborate)
open import simultaneous.HeldComb using (past)
open import simultaneous.FlatLanes using (BProj; brTag; drop)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Out; react; cut; left; anyHolds)

-- A visible row before one a run meets is met before it.
run-catch : ∀ {X} {t : EmissionSet X} {c} r {q e r′ k e′} → Run t c (r ++ (q , e) ∷ r′) → t k e′ → Visible e′ → After c k → k ≺ q
          → Σ (List (Pos × Ev X)) λ r₁ → Σ (List (Pos × Ev X)) λ r₂ → Σ (Ev X) λ e″ → r ≡ r₁ ++ (k , e″) ∷ r₂
run-catch [] ((_ , _ , _ , lst) ∷ _) tk vk ak kq = ⊥-elim (lst tk vk ak kq)
run-catch ((q₀ , e₀) ∷ r) {k = k} ((_ , _ , _ , lst) ∷ rn) tk vk ak kq with q₀ ≟ᵖ k
... | Nl.yes refl = [] , r , e₀ , refl
... | Nl.no ne with ≼-split {q₀} {k} (lst tk vk ak)
...   | inj₂ eq = ⊥-elim (ne eq)
...   | inj₁ lt with run-catch r rn tk vk lt kq
...     | r₁ , r₂ , e″ , refl = (q₀ , e₀) ∷ r₁ , r₂ , e″ , refl

-- No list ends before its last element.
nonempty : ∀ {X : Set} (r : List X) {y r′} → r ++ y ∷ r′ ≡ [] → ⊥
nonempty []      ()
nonempty (_ ∷ _) ()

-- The scan past a row it reads, past what it read before.
past-split : ∀ {B} op (o : Out B) r₁ {q x r₂} → (∀ a₁ {c} a₂ → r₁ ++ (q , out x) ∷ r₂ ≡ a₁ ++ (c , end) ∷ a₂ → a₂ ≡ [])
           → past op o (r₁ ++ (q , out x) ∷ r₂) ≡ past op (react op (past op o r₁) x) r₂
past-split op o []                 tl = refl
past-split op o ((c , out y) ∷ r₁) tl = past-split op (react op o y) r₁ (λ a₁ a₂ eq → tl (_ ∷ a₁) a₂ (cong (_ ∷_) eq))
past-split op o ((c , end) ∷ r₁) {q} {x} {r₂} tl = ⊥-elim (nonempty r₁ (tl [] (r₁ ++ (q , out x) ∷ r₂) refl))
past-split op o ((c , skip) ∷ r₁)  tl = past-split op o r₁ (λ a₁ a₂ eq → tl (_ ∷ a₁) a₂ (cong (_ ∷_) eq))
past-split op o ((c , pin _) ∷ r₁) tl = past-split op o r₁ (λ a₁ a₂ eq → tl (_ ∷ a₁) a₂ (cong (_ ∷_) eq))

-- A cut leaves the outer's routes as they were.
cut-zero : ∀ {B} k n s → Flat.outer s ≡ 0 → Flat.outer (proj₁ (cut {B} k n s)) ≡ 0
cut-zero k n s z with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | _     = z
... | false | true  = z
... | false | false = z

-- THE OUTER'S END CUTS ITS ROUTES while a lane runs or waits.
left-cut : ∀ {B} n s → (isZero (Flat.active s) ∧ isZero (Flat.queue s)) ≡ false → Flat.outer (proj₁ (left {B} n s)) ≡ 0
left-cut n s h with isZero (Flat.active s) ∧ isZero (Flat.queue s)
left-cut n s () | true
left-cut n s h  | false = cut-zero (Flat.outer s) n (record s { outer = 0 }) refl

both-zero : ∀ a b → (isZero a ∧ isZero b) ≡ true → a ≡ 0 × b ≡ 0
both-zero zero    zero    _  = refl , refl
both-zero zero    (suc _) ()
both-zero (suc _) _       ()

-- A run with no row of the branch projects onto nothing.
all-drop : ∀ {A B b} {h : IE A → IE B} {J} rx → (∀ {k e} → (k , e) ∈ rx → brTag b e ≡ nothing) → BProj b h J rx []
all-drop []       _ = BProj.[]
all-drop (_ ∷ rx) f = drop (f (here refl)) (all-drop rx (λ i → f (there i)))
