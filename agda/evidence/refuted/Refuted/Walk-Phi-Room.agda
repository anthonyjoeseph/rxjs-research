-- ══════════════════════════════════════════════════════════════════
-- WALK-PHI-ROOM: the depth face's instant has no room for a fold.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks -- unlike a
-- prose note, which decays silently.
--
-- THIS TREE IS OUTSIDE `agda/src` ON PURPOSE (Anthony).  Nothing in
-- `src` may import it; `src` refers to it in `-- REFUTED:` comments.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Phi-Room where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _*_; _^_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Evaluator using (iterSize)

-- THE CURRENCY, STATED HERE RATHER THAN IMPORTED, because what is
-- refuted is an arithmetic shape and not a definition of the tree.  An
-- instant's fuel supplies two to two-to-the-size -- that is what the
-- depth face's ceiling routes through -- so an exponent spent under it
-- may reach two to the size and no further.  A threading frame applies
-- its step function once per value it is handed, so a fold over a count
-- charges a power in that count, and its exponent is the count times a
-- size.  Affordability is therefore the product below, and the whole
-- question is what bounds the count.
--
-- WHAT IS KNOWN ABOUT THE COUNT IS THAT IT IS AT LEAST THE SIZE, AND
-- NOTHING MORE.  The width an instant admits sits under the NEXT
-- instant's size cap and under nothing smaller, and that cap is above
-- this one -- so a count as large as two to the size is admitted, and
-- the product leaves the room at once.
walk-fold-room-absurd :
  (∀ (S W : ℕ) → 21 ≤ S → S ≤ W → S * W ≤ 2 ^ S) → ⊥
walk-fold-room-absurd h =
  ≤⇒≤ᵇ (h 21 2097152 (≤ᵇ⇒≤ 21 21 tt) (≤ᵇ⇒≤ 21 2097152 tt))

-- AND THE WITNESS IS ADMITTED RATHER THAN INVENTED, which is the half a
-- bare arithmetic refutation would leave open.  The size cap steps by
-- `sizeStep` once per fold and an instant runs a tower's worth of them,
-- so the next instant's cap is what the count sits under; FOUR folds
-- from the floor of twenty-one already carry it past two to that floor,
-- and the count is free to be anything below.
room₂₁ : 2 ^ 21 ≡ 2097152
room₂₁ = refl

size₄ : iterSize 21 4 21 ≡ 66939411
size₄ = refl

charge₂₁ : 21 * 2097152 ≡ 44040192
charge₂₁ = refl
