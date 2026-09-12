------------------------------------------------------------------
-- THE CONNECT PEEL'S EDGE: latching a fresh shared slot strictly drops
-- the unconnected-share count, which is the outermost component of the
-- descent's triple and the quantity the evaluator's connect guard
-- compares.
--
-- IT IS A ONE-WAY COUNT, AND THAT IS THE WHOLE OF WHY IT DESCENDS.  The
-- connect fires only behind a freshness test and prepends to the
-- connected list, which no function of the machine ever shrinks; the
-- slot telescope itself is fixed for the length of a run.  So the
-- latched slot goes one to zero, no other slot rises, and the sum over
-- the telescope strictly falls.  Nothing here asks what a run DID — the
-- premise is an equation on the telescope and a boolean the clause has
-- already tested for itself, which is what keeps this peel out of the
-- circularity the rank peel has to answer for.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Connect-Edge where

open import Data.Bool using (T; true; false)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; tabulate)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; +-mono-<-≤; +-mono-≤-<)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (unconnAt; unconn; memberSource)

-- the freshness test the clause has already run compares a slot index
-- with itself, so what the count's drop turns on is that `_≡ᵇ_` says
-- true there
≡ᵇ-refl : (k : ℕ) → (k ≡ᵇ k) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc k) = ≡ᵇ-refl k

-- pointwise sums over the telescope, and a strict version of the same:
-- one slot doing strictly better with the rest no worse is what a
-- latch buys, and it is the only shape of drop this component ever sees
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {0}     f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h fzero) (sum-tab-mono _ _ (λ i → h (fsuc i)))

sum-tab-strict : ∀ {m} (f g : Fin m → ℕ) → (∀ j → f j ≤ g j) →
  (i : Fin m) → f i < g i → sum (tabulate f) < sum (tabulate g)
sum-tab-strict {suc m} f g h fzero    fi<gi =
  +-mono-<-≤ fi<gi (sum-tab-mono _ _ (λ j → h (fsuc j)))
sum-tab-strict {suc m} f g h (fsuc i) fi<gi =
  +-mono-≤-< (h fzero) (sum-tab-strict _ _ (λ j → h (fsuc j)) i fi<gi)

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (toℕ i ≡ᵇ s) = z≤n
...   | false with (toℕ i ≡ᵇ s)
...     | true  = z≤n
...     | false = ≤-refl

unconn-insert : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) {d : Closed Γ (lookup Γ i)}
  {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
  memberSource (toℕ i) cs ≡ false →
  unconn sl (toℕ i ∷ cs) < unconn sl cs
unconn-insert sl cs i eqi fresh =
  sum-tab-strict _ _ (unconnAt-cons-≤ sl cs (toℕ i)) i strict
  where
  strict : unconnAt sl (toℕ i ∷ cs) i < unconnAt sl cs i
  strict rewrite eqi | fresh | ≡ᵇ-refl (toℕ i) = s≤s z≤n

-- THE GUARD'S OBLIGATION, AND THE ENTRY INVARIANT IS WHY IT IS AN
-- INEQUALITY HERE TOO — for a different reason from the μ peel's.  The
-- component is re-seeded only AT a connect, while the connected list
-- grows at every connect anywhere beneath; so a caller returning from a
-- nested latch holds a witness whose count is STALE and too large.  It
-- is never too small, because nothing un-latches, and `≤` is exactly
-- that reading.
connect-guard : ∀ {n} {Γ : Ctx n} {U} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) {d : Closed Γ (lookup Γ i)}
  {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
  memberSource (toℕ i) cs ≡ false →
  unconn sl cs ≤ U → unconn sl (toℕ i ∷ cs) < U
connect-guard sl cs i eqi fresh le = ≤-trans (unconn-insert sl cs i eqi fresh) le
