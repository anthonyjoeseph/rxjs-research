{-# OPTIONS --guardedness #-}

-- WHERE A PROGRAM'S CUTS HANG, READ OFF ITS TREE.  A program's cut at
-- `N` is its listing at depth `N` (`Cut`), and its boundaries there are
-- a function of the tree alone (`bd`): nobody chooses them.  A leaf
-- that never moves has none; a spin has its next tick; a one-to-one
-- former keeps its child's, a take those no failing value precedes
-- (`TakeBd`); a connect keeps its body's and its source's as the body
-- lives (`ConnBd`), the body reading the source's as its hot's; a
-- reader has its hot's (`BdEnv`).
--
-- The plain program and its elaboration are both trees, so each has
-- its boundaries by this one function, and one proof bounds both
-- (`simultaneous.TreeBounded`).
module simultaneous.HorizonTree where

open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.TableKit using (TR)
open import simultaneous.Horizon using (Tag; module SpinB; module TakeBd; module ConnBd)
open import simultaneous.HorizonJoin using (module JoinBd)

------------------------------------------------------------------------
-- A program's cuts

-- The cut at `N`: the listing at depth `N`, three rows deep at least.
Cut : ∀ {Γ A} → ℕ → Obs Timeline Γ A → (ℕ → All Tb.Listed Γ) → Pos → ℕ → EmissionSet A
Cut n o ρ p N = TR (listC (3 + N) n o (ρ N) p)

-- A connect's source, listed in full under the connect's second label.
srcL : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} → (∀ N → UncutEnv (ρ N)) → Pos → ℕ → Tb.Listed A
srcL n s uρ p N = proj₁ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))

-- The scope a connect's body reads: the source's hot, then the rest.
bodyρ : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} → (∀ N → UncutEnv (ρ N)) → Pos → ℕ → All Tb.Listed (A ∷ Γ)
bodyρ n s {ρ} uρ p N = hotOf (srcL n s uρ p N) ∷ ρ N

bodyU : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p → ∀ N → UncutEnv (bodyρ n s uρ p N)
bodyU n s uρ p N = proj₂ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))) , uρ N

------------------------------------------------------------------------
-- Boundaries, per hot and per tree

-- Each hot in scope has its boundaries: its source's.
BdEnv : List Set → Set₁
BdEnv Γ = ∀ {X : Set} → X ∈ Γ → ℕ → Pos → Tag → Set

infixr 5 _∷ᵇ_
_∷ᵇ_ : ∀ {Γ} {A : Set} → (ℕ → Pos → Tag → Set) → BdEnv Γ → BdEnv (A ∷ Γ)
(B ∷ᵇ β) (here refl) = B
(B ∷ᵇ β) (there i)   = β i

-- A join's boundaries, from its outer's cuts and boundaries and each
-- lane's, by the lane's value and subscription.
JoinBdT : Set₁
JoinBdT = ∀ {A B : Set} → Pos
        → (ℕ → EmissionSet A) → (ℕ → Pos → Tag → Set)
        → (A → Pos → ℕ → EmissionSet B) → (A → Pos → ℕ → Pos → Tag → Set)
        → ℕ → Pos → Tag → Set

postulate
  -- A COLD'S BOUNDARIES: where its listing stopped short of its timeline.
  cold-bd : ∀ {A} → Timeline A → Pos → ℕ → Pos → Tag → Set

  -- THE OTHER JOINS' BOUNDARIES: the outer's, and each running lane's
  -- before the lane's cut, by each policy's running and cutting.
  cc-bd : ℕ → JoinBdT
  sw-bd : JoinBdT
  ex-bd : JoinBdT

-- A MERGE'S BOUNDARIES: its outer's, and every value's lane's, subscribed
-- under the value's row.
merge-bd : JoinBdT
merge-bd p o Bdo L BdL N = JoinBd.JBd (o N) (λ _ → ⊤) (λ _ _ → ⊥) (Bdo N) (λ q a → BdL a (q ⊕ [ ix 1 ]) N)

join-bd : FlatOp → JoinBdT
join-bd (mergeᶠ nothing)  = merge-bd
join-bd (mergeᶠ (just k)) = cc-bd k
join-bd switchᶠ           = sw-bd
join-bd exhaustᶠ          = ex-bd

-- A TREE'S BOUNDARIES, subscribed at `p` in a scope of hots.
bd : ∀ {Γ A} → ℕ → (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N)) → BdEnv Γ → Pos → ℕ → Pos → Tag → Set
bd n       (cold c)          ρ uρ β p = cold-bd c p
bd n       empty             ρ uρ β p = λ _ _ _ → ⊥
bd n       (of xs)           ρ uρ β p = λ _ _ _ → ⊥
bd n       (map f s)         ρ uρ β p = bd n s ρ uρ β p
bd n       (scan f z s)      ρ uρ β p = bd n s ρ uρ β p
bd n       (takeWhile i q s) ρ uρ β p = TakeBd.Bd′ i q (Cut n s ρ p) (bd n s ρ uρ β p)
bd n       (flatMap op f s)  ρ uρ β p =
  join-bd op p (Cut n s ρ p) (bd n s ρ uρ β p) (λ a q → Cut n (f a) ρ q) (λ a q → bd n (f a) ρ uρ β q)
bd n       (connect s b)     ρ uρ β p =
  ConnBd.CBd p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]))
    (bd n s ρ uρ β (p ⊕ [ ix 1 ]))
    (bd n b (bodyρ n s uρ p) (bodyU n s uρ p) (bd n s ρ uρ β (p ⊕ [ ix 1 ]) ∷ᵇ β) (p ⊕ [ ix 0 ]))
bd n       (connected i)     ρ uρ β p = β i
bd {A = A} zero (defer l)      ρ uρ β p = SpinB.Bd {A} p
bd (suc n) (defer l)         ρ uρ β p = bd n (Later.force l) ρ uρ β (p ⊕ [ ix 1 ])
