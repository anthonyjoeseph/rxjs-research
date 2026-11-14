{-# OPTIONS --guardedness #-}

-- A READER'S LANE: what a step of its fold sends, a run of `begin`s and
-- then, for an emit met, that emit.  So the one value a lane shows is
-- its last, and a lane for an end shows none.
module simultaneous.ReadLane where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (does)

open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; ix)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (out; skip; InE; at-out; on-out)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed; valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (Shown)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; joins; joinStep)

-- Emits showing no value.
Marks : ∀ {X} → List (IE X) → Set
Marks = All (λ m → valuesOf m ≡ [])

rep-marks : ∀ {X} k n → Marks {X} (replicate k (instEmit (mark begin) n))
rep-marks zero    n = []
rep-marks (suc k) n = refl ∷ rep-marks k n

joins-marks : ∀ {X} r (e : IE X) → Marks (joins r e)
joins-marks (m , k) (instEmit (value _) _)       = rep-marks k m
joins-marks (m , k) (instEmit (mark begin) n) with does (n ≟ᵖ m)
... | true  = rep-marks k m
... | false = []
joins-marks (m , k) (instEmit (mark over) _)       = rep-marks k m
joins-marks (m , k) (instEmit (mark stop) _)       = rep-marks k m
joins-marks (m , k) (instEmit (mark outerOpen) _)  = rep-marks k m
joins-marks (m , k) (instEmit (mark outerClose) _) = rep-marks k m
joins-marks (m , k) (instEmit (mark laneStart) _)  = rep-marks k m
joins-marks (m , k) (instEmit (mark carry) _)      = rep-marks k m
joins-marks (m , k) (instEmit (mark laneDone) _)   = rep-marks k m
joins-marks (m , k) (instEmit (mark burstEnd) _)   = rep-marks k m
joins-marks (m , k) (instEmit (mark outerDone) _)  = rep-marks k m
joins-marks (m , k) (instEmit (mark subscribed) _) = rep-marks k m
joins-marks (m , k) (instEmit (mark completed) _)  = rep-marks k m

-- A step meeting an emit: marks, then the emit.
step-just : ∀ {X} (β : Bool × List (IE X)) r e → Σ (List (IE X)) λ ms → Marks ms × proj₂ (joinStep β (r , just e)) ≡ ms ++ e ∷ []
step-just (true  , _) r e = joins r e , joins-marks r e , refl
step-just (false , _) r e = [] , [] , refl

-- A step meeting the end: marks.
step-nothing : ∀ {X} (β : Bool × List (IE X)) r → Marks (proj₂ (joinStep β (r , nothing)))
step-nothing (true  , _) (m , k) = rep-marks k m
step-nothing (false , _) r       = []

------------------------------------------------------------------------
-- An `of` of such a list

-- Marks show nothing.
of-marks : ∀ {X} w j (ms : List (IE X)) {y b} → Marks ms → InE (ofᴱ w j ms) y (out b) → Shown b → ⊥
of-marks w j (m ∷ ms) (v ∷ _)  at-out     sh = sh v
of-marks w j (m ∷ ms) (_ ∷ vs) (on-out r) sh = of-marks w (suc j) ms vs r sh

-- Marks then an emit: the one shown is the emit, last.
of-last⁻ : ∀ {X} w j (ms : List (IE X)) e {y b} → Marks ms → InE (ofᴱ w j (ms ++ e ∷ [])) y (out b) → Shown b
         → b ≡ e × y ≡ w ⊕ (ix (j + length ms) ∷ [])
of-last⁻ w j []       e []       at-out     _  = refl , subst (λ n → w ⊕ (ix j ∷ []) ≡ w ⊕ (ix n ∷ [])) (sym (+-identityʳ j)) refl
of-last⁻ w j []       e []       (on-out r) _  = ⊥-elim (none r)
  where none : ∀ {y b} → InE (ofᴱ w (suc j) []) y (out b) → ⊥
        none ()
of-last⁻ w j (m ∷ ms) e (v ∷ _)  at-out     sh = ⊥-elim (sh v)
of-last⁻ w j (m ∷ ms) e {y} (_ ∷ vs) (on-out r) sh with of-last⁻ w (suc j) ms e vs r sh
... | eb , ey = eb , subst (λ n → y ≡ w ⊕ (ix n ∷ [])) (sym (+-suc j (length ms))) ey

of-last : ∀ {X} w j (ms : List (IE X)) e → InE (ofᴱ w j (ms ++ e ∷ [])) (w ⊕ (ix (j + length ms) ∷ [])) (out e)
of-last w j []       e = subst (λ n → InE (ofᴱ w j (e ∷ [])) (w ⊕ (ix n ∷ [])) (out e)) (sym (+-identityʳ j)) at-out
of-last w j (m ∷ ms) e = on-out (subst (λ n → InE (ofᴱ w (suc j) (ms ++ e ∷ [])) (w ⊕ (ix n ∷ [])) (out e)) (sym (+-suc j (length ms))) (of-last w (suc j) ms e))

-- An `of` steps over nothing.
of-skip : ∀ {A} w j (xs : List A) {y} → InE (ofᴱ w j xs) y skip → ⊥
of-skip w j []       ()
of-skip w j (x ∷ xs) (on-out r) = of-skip w (suc j) xs r

------------------------------------------------------------------------
-- The lane's last index

len-snoc : ∀ {A : Set} (ms : List A) e → length (ms ++ e ∷ []) ≡ suc (length ms)
len-snoc []       e = refl
len-snoc (m ∷ ms) e = cong suc (len-snoc ms e)

pred-snoc : ∀ {A : Set} (ms : List A) e → pred (length (ms ++ e ∷ [])) ≡ length ms
pred-snoc ms e = cong pred (len-snoc ms e)

-- Marks then an emit: the emit at the last index.
of-at-last : ∀ {X} w (xs ms : List (IE X)) e → xs ≡ ms ++ e ∷ [] → InE (ofᴱ w 0 xs) (w ⊕ (ix (pred (length xs)) ∷ [])) (out e)
of-at-last w xs ms e refl = subst (λ n → InE (ofᴱ w 0 (ms ++ e ∷ [])) (w ⊕ (ix n ∷ [])) (out e)) (sym (pred-snoc ms e)) (of-last w 0 ms e)

of-at-last⁻ : ∀ {X} w (xs ms : List (IE X)) e {y b} → Marks ms → xs ≡ ms ++ e ∷ [] → InE (ofᴱ w 0 xs) y (out b) → Shown b
            → b ≡ e × y ≡ w ⊕ (ix (pred (length xs)) ∷ [])
of-at-last⁻ w xs ms e mk refl r sh with of-last⁻ w 0 ms e mk r sh
... | eb , ey = eb , trans ey (cong (λ n → w ⊕ (ix n ∷ [])) (sym (pred-snoc ms e)))
