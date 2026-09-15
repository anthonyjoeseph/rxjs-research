------------------------------------------------------------------
-- THE UNCONNECTED COUNT'S ARITHMETIC, AND NOTHING ELSE.
------------------------------------------------------------------

-- WHAT LIVES HERE AND WHY IT IS ITS OWN MODULE.  The count reads no
-- program: it tabulates the slot table and adds one for every SHARED
-- slot whose index the connected set does not hold, so every fact
-- about it is a fact about a list gaining an element.  Two faces want
-- those facts -- the order's connect edge, which spends the strict
-- drop, and the walk over the subscribe families, which spends the
-- weak one -- and neither can import the other, so the fact goes in
-- the lowest module that reaches both.
--
-- AND THE STRICT FORM CARRIES THE SLOT'S OWN SHAPE, WHICH IS WHAT THE
-- MEMBERSHIP PREMISE ALONE COULD NOT SAY.  `unconnAt sl cs i ≡ 1` is
-- the single premise that fixes both halves at once: only a `shared`
-- slot ever reads one, and it reads one only while the set is without
-- it.  Stated with membership alone the claim is FALSE, and a table
-- of one scripted slot is the witness.
--
-- REFUTED: `Refuted.Scripted-Connect` -- the membership-only form, at
--   the smallest table there is.
module Rx.Evaluator.Unconn-Arith where

open import Data.Bool using (T; true; false; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; tabulate)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤-refl; +-mono-≤; +-mono-<-≤; +-mono-≤-<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


open import Data.Vec using (lookup)

open import Decide using (≡ᵇ-refl)
open import Rx.Exp using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Prim using (Source)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (unconn; unconnAt; memberSource; sameSource)

-- pointwise sums over the telescope
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {zero}  f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h fzero) (sum-tab-mono _ _ (λ i → h (fsuc i)))

-- and the same with one index moving strictly, which is the only way
-- a sum of naturals falls at all
sum-tab-mono-< : ∀ {m} (f g : Fin m → ℕ) (i : Fin m) → (∀ j → f j ≤ g j) →
  f i < g i → sum (tabulate f) < sum (tabulate g)
sum-tab-mono-< {suc m} f g fzero    h hi =
  +-mono-<-≤ hi (sum-tab-mono _ _ (λ j → h (fsuc j)))
sum-tab-mono-< {suc m} f g (fsuc i) h hi =
  +-mono-≤-< (h fzero) (sum-tab-mono-< _ _ i (λ j → h (fsuc j)) hi)

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

-- and so the count itself only falls
unconn-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
unconn-cons-≤ sl cs s = sum-tab-mono _ _ (unconnAt-cons-≤ sl cs s)

-- THE SLOT BEING CONNECTED, WHICH IS THE ONLY INDEX THAT MOVES.  A
-- slot reading one is shared and unheld, so putting its own index in
-- takes it to nought -- and `sameSource` at an index against itself is
-- where that is decided.
unconnAt-self-0 : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) → unconnAt sl cs i ≡ 1 → unconnAt sl (toℕ i ∷ cs) i < unconnAt sl cs i
unconnAt-self-0 sl cs i eq with sl i
unconnAt-self-0 sl cs i () | scripted _
unconnAt-self-0 sl cs i eq | shared _ rewrite ≡ᵇ-refl (toℕ i) | eq = s≤s z≤n

-- THE CONNECT EDGE'S OWN FACT.  Connecting a slot that reads one takes
-- the count strictly down, because that index falls by one and no
-- other rises.
connect-count-drops : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
                        (i : Fin n)
                    → unconnAt sl cs i ≡ 1
                    → unconn sl (toℕ i ∷ cs) < unconn sl cs
connect-count-drops sl cs i eq =
  sum-tab-mono-< _ _ i (unconnAt-cons-≤ sl cs (toℕ i)) (unconnAt-self-0 sl cs i eq)

-- AND WHAT THE CONNECT ARM HOLDS, IN THE CURRENCY THE FACT ABOVE
-- TAKES.  The arm reaches its clause down two branches -- the slot
-- matched `shared`, and membership read `false` -- which is exactly
-- the pair that makes the index read one.  Keeping them separate at
-- the edge and joining them here is what stops the shape being lost
-- again: the refuted statement is the one that carries only the
-- second.
unconnAt-shared-fresh : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
    (i : Fin n) {d : Closed Γ (lookup Γ i)}
    {ok : T (inputsBelowᵉ (toℕ i) d)}
  → sl i ≡ shared d {ok = ok}
  → memberSource (toℕ i) cs ≡ false
  → unconnAt sl cs i ≡ 1
unconnAt-shared-fresh sl cs i eqs eqm rewrite eqs | eqm = refl
