{-# OPTIONS --guardedness #-}

-- WHAT THE SCAN'S SOURCE SENDS, read back: a branch's row is that
-- branch's, where its reader met it, and the trackers and the closing
-- `nothing` send no branch's row.  Nothing under the source is deferred,
-- so every approximant reads it as the meaning does.
module simultaneous.CombSent where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)

open import Tree using (mergeᶠ; takeWhile; flatMap; of; map)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; enter; DenEnv; ⟦_⟧; approx; out; module Op; module TakeWhile)
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB; laneB; closeB)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (merge-out; map-out′; of-mem; each-one; module Cat)
open import simultaneous.InstEmit using (instEmit; value; mark; outerClose; outerDone)
open import Data.List.Relation.Unary.All using (lookup)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (E; IE; Routes; Input; going; fed; branch; closer; closing; marked)

-- A takeWhile that never includes its failure keeps a value where it was.
take-at : ∀ {X} (keep : X → Bool) (d : Den X) p {k y} → enter (Op.takeWhile false keep d) p k (out y) → enter d p k (out y)
take-at keep d p (TakeWhile.pass t _ _ , _) = t
take-at keep d p (TakeWhile.fail _ _ _ () , _)

module _ {Δ A B} (tk : E (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) where

  Fed : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Fed = flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ []))

  Src : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Src = takeWhile false going Fed

  -- The flatMap's own branches, each tagged.
  Tag : Branch → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Tag b = map (λ e → just (inj₁ (b , e))) (branch b)

  Own : E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Own = flatMap (mergeᶠ nothing) Tag (of (outerB ∷ laneB ∷ closeB ∷ []))

  Cat-of : Bool → E (IE B ∷ IE B ∷ IE A ∷ Δ) (Maybe (Input B))
  Cat-of c = if c then Own else of (nothing ∷ [])

  -- A branch reads a hot, under every approximant as under the meaning.
  branch-ev : ∀ m b {s q y} → enter (ev m (branch {A = A} {B} b) env) s q y → enter (⟦ branch b ⟧ env) s q y
  branch-ev nothing  b      r = r
  branch-ev (just n) outerB r = r
  branch-ev (just n) laneB  r = r
  branch-ev (just n) closeB r = r

  -- A branch's row the source sends is the branch's, at the same row.
  sent-branch : ∀ m P {q b y} → enter (ev m Src env) P q (out (just (inj₁ (b , y))))
              → Σ Pos λ s → enter (⟦ branch b ⟧ env) s q (out y)
  sent-branch nothing P r with merge-out (λ a → ⟦ fed tk a ⟧ env) (Op.of (true ∷ false ∷ [])) P (take-at going (⟦ Fed ⟧ env) P r)
  ... | _ , true , _ , l , _ with map-out′ _ (⟦ tk ⟧ env) _ l
  ...   | _ , _ , ()
  sent-branch nothing P r | _ , false , _ , l , _ with Cat.cat-out (λ c → ⟦ Cat-of c ⟧ env) _ l
  ... | inj₂ (_ , l′) with of-mem _ 0 (nothing ∷ []) (proj₁ l′)
  ...   | here ()
  ...   | there ()
  sent-branch nothing P r | _ , false , _ , l , _ | inj₁ l′ with merge-out (λ b → ⟦ Tag b ⟧ env) (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) _ l′
  ... | _ , b′ , _ , l″ , _ with map-out′ (λ e → just (inj₁ (b′ , e))) (⟦ branch b′ ⟧ env) _ l″
  ...   | _ , l‴ , refl = _ , l‴
  sent-branch (just n) P r with merge-out (λ a → approx n (fed tk a) env) (Op.of (true ∷ false ∷ [])) P (take-at going (approx n Fed env) P r)
  ... | _ , true , _ , l , _ with map-out′ _ (approx n tk env) _ l
  ...   | _ , _ , ()
  sent-branch (just n) P r | _ , false , _ , l , _ with Cat.cat-out (λ c → approx n (Cat-of c) env) _ l
  ... | inj₂ (_ , l′) with of-mem _ 0 (nothing ∷ []) (proj₁ l′)
  ...   | here ()
  ...   | there ()
  sent-branch (just n) P r | _ , false , _ , l , _ | inj₁ l′ with merge-out (λ b → approx n (Tag b) env) (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) _ l′
  ... | _ , b′ , _ , l″ , _ with map-out′ (λ e → just (inj₁ (b′ , e))) (approx n (branch b′) env) _ l″
  ...   | _ , l‴ , refl = _ , branch-ev (just n) b′ l‴

-- What the closer sends: a bracket's close, then the outer's end.
data Closing {B : Set} : IE B → Set where
  c-close : ∀ {n} → Closing (instEmit (mark outerClose) n)
  c-done  : ∀ {n} → Closing (instEmit (mark outerDone) n)

closing-mark : ∀ {B} {m n} → Closing {B} (instEmit (mark m) n) → (m ≡ outerClose → ⊥) → (m ≡ outerDone → ⊥) → ⊥
closing-mark c-close a _ = a refl
closing-mark c-done  _ b = b refl

closing-value : ∀ {B} {a n} → Closing {B} (instEmit (value a) n) → ⊥
closing-value ()

closer-marks : ∀ m {Δ A B} (env : DenEnv (IE A ∷ Δ)) s {q x} → enter (ev m (closer {Δ} {A} {B}) env) s q (out x) → Closing x
closer-marks nothing env s r with Cat.cat-out _ s r
... | inj₁ l with each-one closing (lookup env (here refl)) _ l
...   | _ , instEmit (value _) _ , _ , here refl = c-close
...   | _ , instEmit (value _) _ , _ , there ()
...   | _ , instEmit (mark _) _ , _ , ()
closer-marks nothing env s r | inj₂ (_ , l) with of-mem _ 0 (marked outerDone ∷ []) (proj₁ l)
... | here refl = c-done
... | there ()
closer-marks (just n) env s r with Cat.cat-out _ s r
... | inj₁ l with each-one closing (lookup env (here refl)) _ l
...   | _ , instEmit (value _) _ , _ , here refl = c-close
...   | _ , instEmit (value _) _ , _ , there ()
...   | _ , instEmit (mark _) _ , _ , ()
closer-marks (just n) env s r | inj₂ (_ , l) with of-mem _ 0 (marked outerDone ∷ []) (proj₁ l)
... | here refl = c-done
... | there ()
