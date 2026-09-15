------------------------------------------------------------------
-- B, WITH NODE IDENTITY STATIC AND A RUNTIME COUNT.
--
-- The store, the array and the stack all model a fold step as a NEW
-- cell, so the index ASCENDS and the hop's budget is exceeded.  Node
-- identity models it as the SAME node re-entered: `scan` over
-- `acc.pipe(map(f))` is one `mapᵉ` node at a deeper count, not d
-- cells.  So growth is a COUNT, not an allocation, and subscribing to
-- the accumulator at count d reads count d-1.
--
-- THE NODE GRAPH IS NOT A TELESCOPE, WHICH IS WHAT THIS BUYS: `prog`
-- below lets any node mention any node, including itself, and the
-- descent is carried entirely by the count.
------------------------------------------------------------------
module Spike.Nodes where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<-trans; ≤-refl; <⇒≤; ≤-trans; n≤1+n; <-irrefl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

-- a value observed AT count c.  An observable it carries was built
-- STRICTLY EARLIER -- that is the whole invariant, and it is typed
data Val (n : ℕ) : ℕ → Set where
  natᵛ : ∀ {c} → ℕ → Val n c
  obsᵛ : ∀ {c} → Fin n → (c′ : ℕ) → c′ < c → Val n c

data Exp (n : ℕ) : ℕ → Set where
  ofᵉ  : ∀ {c} → List (Val n c) → Exp n c
  mrgᵉ : ∀ {c} → Exp n c → Exp n c

-- NO TELESCOPE: node h's body may mention any node at all
Prog : ℕ → Set
Prog n = (h : Fin n) → (c : ℕ) → Exp n c

wkV : ∀ {n c c′} → c ≤ c′ → Val n c → Val n c′
wkV le (natᵛ x)         = natᵛ x
wkV le (obsᵛ h d lt)    = obsᵛ h d (≤-trans lt le)

wkL : ∀ {n c c′} → c ≤ c′ → List (Val n c) → List (Val n c′)
wkL le []       = []
wkL le (v ∷ vs) = wkV le v ∷ wkL le vs

run : ∀ {n c} → Prog n → Acc _<_ c → Exp n c → List (Val n c)
hop : ∀ {n c} → Prog n → Acc _<_ c → List (Val n c) → List (Val n c)

run p a (ofᵉ vs)  = vs
run p a (mrgᵉ e)  = hop p a (run p a e)

hop p a []                        = []
hop p a (natᵛ x ∷ vs)             = natᵛ x ∷ hop p a vs
hop p (acc rec) (obsᵛ h d lt ∷ vs) =
  wkL (<⇒≤ lt) (run p (rec lt) (p h d)) ++ hop p (acc rec) vs

subscribe : ∀ {n} → Prog n → (c : ℕ) → Exp n c → List (Val n c)
subscribe p c = run p (<-wellFounded c)

------------------------------------------------------------------
-- AND THE RESIDUE, STATED RATHER THAN ASSERTED.  Across instants the
-- invariant is `deferᵉ`'s own discipline -- subscribe at tick k, body
-- at k+1 -- so a fold's accumulator was built at a strictly lower
-- count and `stepped` supplies the witness.  WITHIN one synchronous
-- burst it is not: a fold delivering three times in one instant
-- builds its accumulator at the count it is running at, so emitting
-- it owes `c < c`
------------------------------------------------------------------

stepped : ∀ {n c} → Fin n → Val n (suc c)
stepped {c = c} h = obsᵛ h c ≤-refl

same-instant-owes : ∀ {c} → c < c → ⊥
same-instant-owes = <-irrefl refl
