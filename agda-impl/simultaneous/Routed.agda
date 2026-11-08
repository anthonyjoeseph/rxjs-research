{-# OPTIONS --guardedness #-}

-- WHAT A STREAM HOLDS.  A stream subscribed at `p` HOLDS (`Held`) when
-- its begins are named for their instants, every value, stop, over and
-- end outside the bursts it is exempt for finds the count holding a route
-- of its own instant, and its dead instants stay dead (`Shut`).
--
-- THE EXEMPT BURSTS are the subscribe bursts of the stream itself and of
-- every connect it reads under, each within its own instant: what runs
-- there runs synchronously under the subscription, so whatever route
-- covers it is held above, by the row that subscribed.  A begin may lie
-- there: a reader subscribed inside an async instant joins the routes its
-- source holds at the first emit it meets, in that same instant.
--
-- AN INSTANT'S NAME IS READ OFF THE INSTANT: the cold's step at `I`
-- renders under a lane at `I ++ [ ix 1 ]`, where `mint` is subscribed, and
-- a completion's step one queued lane and one `of` further down.
module simultaneous.Routed where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix; sub; last; inside)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Den; enter)
open import simultaneous.InstEmit using (Mark; instEmit; value; mark; begin; stop; over; subscribed; completed)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (Shut; r₀)
open import denotation.Laws.Worlds using (Ok; TimerRoot)
open import Data.Empty using (⊥)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count)

------------------------------------------------------------------------
-- What a stream holds

-- The name a cold's step at instant `I` mints.
nm : Pos → Pos
nm (ix t ∷ sub e ∷ last ∷ []) = ix t ∷ sub e ∷ last ∷ ix 1 ∷ ix 0 ∷ ix 1 ∷ []
nm (ix t ∷ sub e ∷ l ∷ [])    = ix t ∷ sub e ∷ l ∷ ix 1 ∷ []
nm _                          = root

nameOf : Pos → Pos
nameOf y = nm (instantOf y)

-- `y` lies in the subscribe burst at `c`, within its instant.
Sync : Pos → Pos → Set
Sync c y = T (inside c y) × instantOf y ≡ instantOf c

-- In one of the bursts `cs`.
Ex : List Pos → Pos → Set
Ex cs y = Any (λ c → Sync c y) cs

-- The routes a run's rows leave counted.
cnt : ∀ {A} → List (Pos × Ev (IE A)) → Routes
cnt rs = L.foldl count r₀ (values rs)

-- A row a route carries: anything but a begin, and the end.
data Carried {A : Set} : Ev (IE A) → Set where
  c-value : ∀ {a n} → Carried (out (instEmit (value a) n))
  c-stop  : ∀ {n} → Carried (out (instEmit (mark stop) n))
  c-over  : ∀ {n} → Carried (out (instEmit (mark over) n))
  c-end   : Carried end

-- A mark read above a flatMap: never one a flatMap's scan consumes.
data Routing : Mark → Set where
  r-begin      : Routing begin
  r-stop       : Routing stop
  r-over       : Routing over
  r-subscribed : Routing subscribed
  r-completed  : Routing completed

-- A stop finds a route to stop even inside an exempt burst: no route is
-- stopped twice.
record Held {A : Set} (t : EmissionSet (IE A)) (cs : List Pos) : Set where
  field
    named   : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    covered : ∀ {rs} → Met t rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ {rs} → Met t rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
    shut    : Shut t

-- Held at every admissible subscription, exempt for its own burst and
-- `cs`.  No subscription is made at a timer's root, where a burst would
-- have no instant of its own.
HeldD : ∀ {A} → (Pos → Set) → Den (IE A) → List Pos → Set
HeldD H d cs = ∀ p → Ok H p → (TimerRoot p → ⊥) → Held (enter d p) (p ∷ cs)
