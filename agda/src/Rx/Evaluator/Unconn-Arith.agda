------------------------------------------------------------------
-- THE UNCONNECTED COUNT, AND NOTHING ELSE.
------------------------------------------------------------------

-- WHAT LIVES HERE AND WHY IT IS ITS OWN MODULE.  The count reads no
-- program: it tabulates the slot table and adds one for every SHARED
-- slot whose index the connected set does not hold, so every fact
-- about it is a fact about a list gaining an element.  It sits above
-- `Rx.Evaluator` rather than in it because its only consumer is the
-- reducibility candidate, and a four-line arithmetic fact placed at
-- the bottom would invalidate the evaluator's whole cone to buy
-- nothing.

-- WHAT IT IS FOR.  The fan-out's cycle closes through a connect, and
-- this is the quantity that cycle descends on: the connect is the one
-- edge that moves it, it moves it strictly DOWN, and nothing anywhere
-- moves it up.

-- RECOVERY: git show 3abdafa1:agda/src/Rx/Evaluator/Unconn-Arith.agda
--   holds the arithmetic every arm's room proof spent -- the strict
--   fall at a connect, the antitone form under membership
--   preservation, and the state relation that feeds it -- with the
--   refutation of the membership-only strict form recorded beside it.
module Rx.Evaluator.Unconn-Arith where

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; tabulate)
open import Data.Nat using (ℕ)
open import Data.Nat.ListAction using (sum)

open import Rx.Exp using (Ctx)
open import Rx.Prim using (Source)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator using (memberSource)

-- ONE SLOT'S CONTRIBUTION.  A scripted slot has no definition to
-- subscribe, so connecting it is not an operation and it never counts;
-- a shared one counts until its own index joins the set.
unconnAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
unconnAt sl cs i with sl i
... | shared _   = if memberSource (toℕ i) cs then 0 else 1
... | scripted _ = 0

unconn : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconn sl cs = sum (tabulate (unconnAt sl cs))
