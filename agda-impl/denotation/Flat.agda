-- THE ORDER IS THE CALL TREE'S PRE-ORDER.  Flatten a position into one
-- list of labels — its instant as a leading tick, then for a cascade its
-- creator and its step, then its path — and the position order is the lexicographic
-- order of those lists, and `inside` is a list prefix.  So the order
-- needs no instants to be read: a merge of two runs is a sorted merge of
-- their flat lists.
--
-- It holds of positions whose cascades fire past tick 0 (`Ok`), which
-- every cascade `frames` and the runtimes mint does: a tick-0 frame is
-- played in place, never as a cascade.  Every flat list led by a tick
-- and shaped so (`Flat`) is some position's flattening.
module denotation.Flat where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import denotation.Position using (Pos; Path; Label; ix; sub; last; frame; cascade; _∙_; Cmp; lt; eq; gt; cmpℕ; lexi; isLt;
  isEq; cmpLabel; cmpPath; cmpPos; insideᵗ; inside; _<ᵖ_)

------------------------------------------------------------------------
-- Flat lists of labels, ordered and nested as lists

data FLabel : Set where
  fix  : ℕ → FLabel
  fsub : List FLabel → FLabel
  flast : FLabel

FPos : Set
FPos = List FLabel

mutual
  cmpFL : FLabel → FLabel → Cmp
  cmpFL (fix m)  (fix n)  = cmpℕ m n
  cmpFL (fix _)  (fsub _) = lt
  cmpFL (fix _)  flast    = lt
  cmpFL (fsub _) (fix _)  = gt
  cmpFL (fsub p) (fsub q) = cmpFP p q
  cmpFL (fsub _) flast    = lt
  cmpFL flast    (fix _)  = gt
  cmpFL flast    (fsub _) = gt
  cmpFL flast    flast    = eq

  cmpFP : FPos → FPos → Cmp
  cmpFP []      []      = eq
  cmpFP []      (_ ∷ _) = lt
  cmpFP (_ ∷ _) []      = gt
  cmpFP (a ∷ p) (b ∷ q) = lexi (cmpFL a b) (cmpFP p q)

_<ᶠ_ : FPos → FPos → Bool
p <ᶠ q = isLt (cmpFP p q)

mutual
  insideᶠ : FPos → FPos → Bool
  insideᶠ []      k       = true
  insideᶠ (_ ∷ _) []      = false
  insideᶠ (a ∷ r) (b ∷ k) = sameᶠ (cmpFL a b) r k

  sameᶠ : Cmp → FPos → FPos → Bool
  sameᶠ eq r k = insideᶠ r k
  sameᶠ lt _ _ = false
  sameᶠ gt _ _ = false

------------------------------------------------------------------------
-- Flattening

mutual
  flat : Pos → FPos
  flat (frame ∙ p)       = fix 0 ∷ flatᵗ p
  flat (cascade t e a ∙ p) = fix t ∷ fsub (flat e) ∷ flatˡ a ∷ flatᵗ p

  flatᵗ : Path → FPos
  flatᵗ []      = []
  flatᵗ (a ∷ p) = flatˡ a ∷ flatᵗ p

  flatˡ : Label → FLabel
  flatˡ (ix i)  = fix i
  flatˡ (sub q) = fsub (flat q)
  flatˡ last    = flast

-- Every cascade, however deep, fires past tick 0.
mutual
  data Ok : Pos → Set where
    ok-frame   : ∀ {p} → Okᵗ p → Ok (frame ∙ p)
    ok-cascade : ∀ {t e a p} → Ok e → Okˡ a → Okᵗ p → Ok (cascade (suc t) e a ∙ p)

  data Okᵗ : Path → Set where
    []  : Okᵗ []
    _∷_ : ∀ {a p} → Okˡ a → Okᵗ p → Okᵗ (a ∷ p)

  data Okˡ : Label → Set where
    ok-ix   : ∀ {i} → Okˡ (ix i)
    ok-sub  : ∀ {q} → Ok q → Okˡ (sub q)
    ok-last : Okˡ last

-- A flat list led by a tick: tick 0 then any labels, or a later tick, a
-- creator, a step and any labels; every `fsub` holds one such.
mutual
  data Flat : FPos → Set where
    flat-frame   : ∀ {p} → Flatᵗ p → Flat (fix 0 ∷ p)
    flat-cascade : ∀ {t e a p} → Flat e → Flatˡ a → Flatᵗ p → Flat (fix (suc t) ∷ fsub e ∷ a ∷ p)

  data Flatᵗ : FPos → Set where
    []  : Flatᵗ []
    _∷_ : ∀ {a p} → Flatˡ a → Flatᵗ p → Flatᵗ (a ∷ p)

  data Flatˡ : FLabel → Set where
    flat-ix   : ∀ {i} → Flatˡ (fix i)
    flat-sub  : ∀ {q} → Flat q → Flatˡ (fsub q)
    flat-last : Flatˡ flast

------------------------------------------------------------------------
-- The order agrees

private
  lexi-assoc : ∀ x y z → lexi (lexi x y) z ≡ lexi x (lexi y z)
  lexi-assoc eq _ _ = refl
  lexi-assoc lt _ _ = refl
  lexi-assoc gt _ _ = refl

mutual
  cmp-flatˡ : ∀ {a b} → Okˡ a → Okˡ b → cmpFL (flatˡ a) (flatˡ b) ≡ cmpLabel a b
  cmp-flatˡ ok-ix      ok-ix      = refl
  cmp-flatˡ ok-ix      (ok-sub _) = refl
  cmp-flatˡ ok-ix      ok-last    = refl
  cmp-flatˡ (ok-sub _) ok-ix      = refl
  cmp-flatˡ (ok-sub x) (ok-sub y) = cmp-flat x y
  cmp-flatˡ (ok-sub _) ok-last    = refl
  cmp-flatˡ ok-last    ok-ix      = refl
  cmp-flatˡ ok-last    (ok-sub _) = refl
  cmp-flatˡ ok-last    ok-last    = refl

  cmp-flatᵗ : ∀ {p q} → Okᵗ p → Okᵗ q → cmpFP (flatᵗ p) (flatᵗ q) ≡ cmpPath p q
  cmp-flatᵗ []       []       = refl
  cmp-flatᵗ []       (_ ∷ _)  = refl
  cmp-flatᵗ (_ ∷ _)  []       = refl
  cmp-flatᵗ (x ∷ xs) (y ∷ ys) = cong₂ lexi (cmp-flatˡ x y) (cmp-flatᵗ xs ys)

  cmp-flat : ∀ {a b} → Ok a → Ok b → cmpFP (flat a) (flat b) ≡ cmpPos a b
  cmp-flat (ok-frame xs)   (ok-frame ys)   = cmp-flatᵗ xs ys
  cmp-flat (ok-frame _)      (ok-cascade _ _ _) = refl
  cmp-flat (ok-cascade _ _ _) (ok-frame _)     = refl
  cmp-flat {cascade (suc t) e a ∙ p} {cascade (suc u) d b ∙ q} (ok-cascade ex xa xs) (ok-cascade ey yb ys) =
    trans (cong (lexi (cmpℕ (suc t) (suc u))) (cong₂ lexi (cmp-flat ex ey) (cong₂ lexi (cmp-flatˡ xa yb) (cmp-flatᵗ xs ys))))
          (sym (trans (lexi-assoc (cmpℕ (suc t) (suc u)) (lexi (cmpPos e d) (cmpLabel a b)) (cmpPath p q))
                      (cong (lexi (cmpℕ (suc t) (suc u))) (lexi-assoc (cmpPos e d) (cmpLabel a b) (cmpPath p q)))))

-- THE ORDER IS THE FLAT ORDER.
flat-order : ∀ {a b} → Ok a → Ok b → (flat a <ᶠ flat b) ≡ (a <ᵖ b)
flat-order x y = cong isLt (cmp-flat x y)

------------------------------------------------------------------------
-- `inside` agrees

private
  same-∧ : ∀ c r k → sameᶠ c r k ≡ isEq c ∧ insideᶠ r k
  same-∧ eq _ _ = refl
  same-∧ lt _ _ = refl
  same-∧ gt _ _ = refl

  eq-lexi : ∀ c₁ c₂ x → isEq c₁ ∧ (isEq c₂ ∧ x) ≡ isEq (lexi c₁ c₂) ∧ x
  eq-lexi eq _ _ = refl
  eq-lexi lt _ _ = refl
  eq-lexi gt _ _ = refl

inside-flatᵗ : ∀ {r k} → Okᵗ r → Okᵗ k → insideᶠ (flatᵗ r) (flatᵗ k) ≡ insideᵗ r k
inside-flatᵗ []       _        = refl
inside-flatᵗ (_ ∷ _)  []       = refl
inside-flatᵗ {a ∷ r} {b ∷ k} (x ∷ xs) (y ∷ ys) =
  trans (same-∧ (cmpFL (flatˡ a) (flatˡ b)) (flatᵗ r) (flatᵗ k))
        (cong₂ (λ c z → isEq c ∧ z) (cmp-flatˡ x y) (inside-flatᵗ xs ys))

-- `INSIDE` IS A FLAT PREFIX.
flat-inside : ∀ {r k} → Ok r → Ok k → insideᶠ (flat r) (flat k) ≡ inside r k
flat-inside (ok-frame xs)    (ok-frame ys)    = inside-flatᵗ xs ys
flat-inside (ok-frame _)       (ok-cascade _ _ _) = refl
flat-inside (ok-cascade _ _ _) (ok-frame _)       = refl
flat-inside {cascade (suc t) e a ∙ r} {cascade (suc u) d b ∙ k} (ok-cascade ex xa xs) (ok-cascade ey yb ys) =
  trans (same-∧ (cmpℕ (suc t) (suc u)) (fsub (flat e) ∷ flatˡ a ∷ flatᵗ r) (fsub (flat d) ∷ flatˡ b ∷ flatᵗ k))
  (trans (cong (isEq (cmpℕ (suc t) (suc u)) ∧_)
           (trans (same-∧ (cmpFP (flat e) (flat d)) (flatˡ a ∷ flatᵗ r) (flatˡ b ∷ flatᵗ k))
                  (cong₂ (λ c z → isEq c ∧ z) (cmp-flat ex ey)
                    (trans (same-∧ (cmpFL (flatˡ a) (flatˡ b)) (flatᵗ r) (flatᵗ k))
                           (cong₂ (λ c z → isEq c ∧ z) (cmp-flatˡ xa yb) (inside-flatᵗ xs ys))))))
  (trans (cong (isEq (cmpℕ (suc t) (suc u)) ∧_) (eq-lexi (cmpPos e d) (cmpLabel a b) (insideᵗ r k)))
         (eq-lexi (cmpℕ (suc t) (suc u)) (lexi (cmpPos e d) (cmpLabel a b)) (insideᵗ r k))))

------------------------------------------------------------------------
-- Every flat list so shaped is a position's

mutual
  flat-onto : ∀ {f} → Flat f → Σ Pos λ a → Ok a × flat a ≡ f
  flat-onto (flat-frame xs) with flat-ontoᵗ xs
  ... | p , okp , ep = (frame ∙ p) , ok-frame okp , cong (fix 0 ∷_) ep
  flat-onto (flat-cascade {t} ex xa xs) with flat-onto ex | flat-ontoˡ xa | flat-ontoᵗ xs
  ... | e , oke , ee | a , oka , ea | p , okp , ep =
    (cascade (suc t) e a ∙ p) , ok-cascade oke oka okp , cong₂ (λ x y → fix (suc t) ∷ fsub x ∷ y) ee (cong₂ _∷_ ea ep)

  flat-ontoᵗ : ∀ {f} → Flatᵗ f → Σ Path λ p → Okᵗ p × flatᵗ p ≡ f
  flat-ontoᵗ [] = [] , [] , refl
  flat-ontoᵗ (x ∷ xs) with flat-ontoˡ x | flat-ontoᵗ xs
  ... | a , oka , ea | p , okp , ep = a ∷ p , oka ∷ okp , cong₂ _∷_ ea ep

  flat-ontoˡ : ∀ {f} → Flatˡ f → Σ Label λ a → Okˡ a × flatˡ a ≡ f
  flat-ontoˡ (flat-ix {i}) = ix i , ok-ix , refl
  flat-ontoˡ (flat-sub x) with flat-onto x
  ... | q , okq , eq′ = sub q , ok-sub okq , cong fsub eq′
  flat-ontoˡ flat-last = last , ok-last , refl
