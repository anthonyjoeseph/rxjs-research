{-# OPTIONS --guardedness #-}

-- WHERE A SUBSCRIPTION'S ROWS LIE: the invariant every reading of a lawful
-- observable keeps, and the positions a run can reach.
--
-- A subscription at `p` places its rows in its WORLD: below `p` a plain
-- label at a time; at a timer's root `ix t ∷ sub e ∷ []`, for a timer
-- created at `e` in the world; and where a hot row `h` is joined at `e` in
-- the world, at `h ++ [ sub e ]`.  The world is what lets a connect's
-- source and body be told apart: neither's rows lie in the other's world.
--
-- A REACHABLE position is led by a tick, and every `sub e` in it names an
-- earlier, reachable position.  A subscription is ADMISSIBLE under hot rows
-- `H` when it is reachable and no hot row lies in its world: the hot was
-- made elsewhere.
module denotation.EmissionSet.Laws.Worlds where

open import Data.Bool using (T)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; []; lookup)
open import Data.Product using (Σ; _×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; inside)
open import denotation.EmissionSet using (Ev; end; EmissionSet; _≺_; _≼_; Den; hot; cold; enter; DenEnv)

-- A label that opens no subscription.
data Plain : Label → Set where
  plain-ix   : ∀ {i} → Plain (ix i)
  plain-last : Plain last

mutual
  -- The world of a subscription at `p` under hot rows `H`, `p` excluded.
  data W (H : Pos → Set) (p : Pos) : Pos → Set where
    step  : ∀ {x l} → W⁼ H p x → Plain l → W H p (x ++ [ l ])
    timer : ∀ {e} t → W⁼ H p e → W H p (ix t ∷ sub e ∷ [])
    join  : ∀ {h e} → H h ⊎ W H p h → W⁼ H p e → e ≺ h → W H p (h ++ [ sub e ])

  -- The world with `p` itself.
  data W⁼ (H : Pos → Set) (p : Pos) : Pos → Set where
    here  : W⁼ H p p
    inW   : ∀ {x} → W H p x → W⁼ H p x

mutual
  -- Led by a tick, every `sub` naming an earlier reachable position.
  Real : Pos → Set
  Real (ix i ∷ p) = Back (ix i ∷ []) p
  Real _          = ⊥

  Back : Pos → Pos → Set
  Back acc []          = ⊤
  Back acc (sub e ∷ p) = Real e × e ≺ (acc ++ [ sub e ]) × Back (acc ++ [ sub e ]) p
  Back acc (ix i ∷ p)  = Back (acc ++ [ ix i ]) p
  Back acc (last ∷ p)  = Back (acc ++ [ last ]) p

-- No hot row lies in the world.
Disj : (Pos → Set) → Pos → Set
Disj H p = ∀ {h w} → H h → W H p w → T (inside w h) → ⊥

-- ADMISSIBLE: reachable, and no hot row in its world.
Ok : (Pos → Set) → Pos → Set
Ok H p = Real p × Disj H p

-- The hot rows `H` and a hot's.
_⊕_ : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
_⊕_ {A} H t q = Σ (Ev A) (t q) ⊎ H q

-- A LAWFUL HOT: reachable rows, none below another, none past an end.
record Lawful {A} (t : EmissionSet A) : Set where
  field
    real   : ∀ {y e} → t y e → Real y
    flat   : ∀ {y e l ys e′} → t y e → t (y ++ l ∷ ys) e′ → ⊥
    proper : ∀ {c y e} → t c end → t y e → y ≼ c

-- THE INVARIANT of a reading at `p`: its rows lie in the world and are
-- reachable; none lies below another; and what follows an end lies with
-- it below one position of the world — the rest of the burst it ended in.
record InvAt {A} (H : Pos → Set) (p : Pos) (X : EmissionSet A) : Set where
  field
    world : ∀ {y e} → X y e → W H p y
    real  : ∀ {y e} → X y e → Real y
    flat  : ∀ {y e l ys e′} → X y e → X (y ++ l ∷ ys) e′ → ⊥
    burst : ∀ {c y e} → X c end → X y e → c ≺ y → Σ Pos λ w → W⁼ H p w × T (inside w c) × T (inside w y)

-- At every admissible subscription.
InvD : ∀ {A} → (Pos → Set) → Den A → Set
InvD H d = ∀ p → Ok H p → InvAt H p (enter d p)

-- The rows of an environment's hots.
Hots : ∀ {Γ} → DenEnv Γ → Pos → Set
Hots []           = λ _ → ⊥
Hots (hot t ∷ ρ)  = Hots ρ ⊕ t
Hots (cold _ ∷ ρ) = Hots ρ

-- A LAWFUL ENVIRONMENT: every handle keeps the invariant.
GoodEnv : ∀ {Γ} → DenEnv Γ → Set₁
GoodEnv {Γ} ρ = ∀ {A} (i : A ∈ Γ) → InvD (Hots ρ) (lookup ρ i)
