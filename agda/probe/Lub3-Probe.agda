------------------------------------------------------------------
-- THE 3-WAY ⊔ PROJECTION.  `depthShareGo`'s clause is the mirror's only
-- three-callee clause — `a ⊔ (b ⊔ c)` — and the two Subscribe-Face sites
-- that consume it both failed to elaborate: a nested `≤-trans` leaves the
-- INTERMEDIATE bound (`b ⊔ _`) as a meta, and inverting it needs the
-- stdlib's `m≤m⊔n`/`m≤n⊔m`, which are derived through the NaturalChoice
-- `MaxOp⇒MinOp` duality and so present no syntactic `⊔` to unify against.
-- Agda reports `Failed to solve … blocked on _x`.
--
-- § 1 reproduces the failure's SHAPE and § 2 fixes it: three lemmas with
-- the hypothesis LAST and every bound implicit, so each call matches
-- first-order against a type that is already fully known.
------------------------------------------------------------------
module Lub3-Probe where

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)

------------------------------------------------------------------
-- § 1.  THE THREE PROJECTIONS.  Internally these still go through the
-- stdlib lemmas, but here the bounds are plain VARIABLES, so there is
-- nothing to invert and the opaque duality never gets in the way.
------------------------------------------------------------------

-- BOUNDS EXPLICIT, on purpose, and this is the whole finding.  `_⊔_` is a
-- DEFINED RECURSIVE FUNCTION on ℕ, not a constructor, so the unifier
-- cannot solve `_a ⊔ (b ⊔ c) ≟ A ⊔ (B ⊔ C)` for `_a` — it reports
-- `blocked on _a` and gives up.  An implicit-bound version of these three
-- typechecks fine as a DEFINITION (its bounds are variables) and then
-- fails at every CALL, which is what bit Subscribe-Face:3425/3438.
--
-- Naming the bounds turns that INVERSION into a CHECK: Agda merely
-- unfolds the two sides and compares, which always succeeds.  The terms
-- themselves are the same ones the failing sites already wrote — those
-- were never WRONG, only un-inferable.
--
-- The single-level projections (19 of them, all green) survive only
-- because both ends of the `≤-trans` are pinned there, leaving no `⊔` to
-- invert.  Do NOT read their success as licence to omit bounds here.
lub3-l : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → a ≤ d
lub3-l a b c h = ≤-trans (m≤m⊔n a (b ⊔ c)) h

lub3-m : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → b ≤ d
lub3-m a b c h = ≤-trans (m≤m⊔n b c) (≤-trans (m≤n⊔m a (b ⊔ c)) h)

lub3-r : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → c ≤ d
lub3-r a b c h = ≤-trans (m≤n⊔m b c) (≤-trans (m≤n⊔m a (b ⊔ c)) h)

------------------------------------------------------------------
-- § 2.  THE CALL SITES, in the shape Subscribe-Face uses them: the
-- bound `d` is a variable, the three summands are OPAQUE applied terms
-- (standing for `depthShareGo …` / `depthFold …`), and the projection is
-- handed straight into an argument position with NO type annotation —
-- which is precisely the context that failed.
------------------------------------------------------------------

postulate
  A B C : ℕ → ℕ
  Ok    : Set
  useA  : ∀ {d} (k : ℕ) → A k ≤ d → Ok
  useB  : ∀ {d} (k : ℕ) → B k ≤ d → Ok
  useC  : ∀ {d} (k : ℕ) → C k ≤ d → Ok

-- all three off ONE hypothesis, exactly as `shareGo-caps` does — and the
-- summands bound by name in the clause's own `where`, which is where
-- `shareGo-caps` already keeps `st₀`/`cl`/`FP`
site : ∀ {d} (k : ℕ) → A k ⊔ (B k ⊔ C k) ≤ d → Ok
site k dpt = useC k (lub3-r dA dB dC dpt)
  where
  dA = A k
  dB = B k
  dC = C k
  rA : Ok
  rA = useA k (lub3-l dA dB dC dpt)
  rB : Ok
  rB = useB k (lub3-m dA dB dC dpt)

------------------------------------------------------------------
-- § 3.  AND THE SPEND ON TOP OF A PROJECTION — the middle callee is the
-- one `foldPath-caps` consumes, and Stage B needs a `suc` peeled off a
-- projected bound.  Confirms the two compose in either order.
------------------------------------------------------------------

open import Data.Nat using (s≤s)

-- `with` is the WRONG move here: abstracting `⊔-3m dpt` freezes its
-- implicit bounds before they are solved, and the split is rejected with
-- `I'm not sure if there should be a case for s≤s`.  Move (b) of the
-- ruling instead hands the projected bound to a helper that matches `dep`
-- in its OWN left-hand side, where the type is already ground
siteSpend : ∀ (dep k : ℕ) → A k ⊔ (suc (B k) ⊔ C k) ≤ dep → ℕ
siteSpend dep k dpt = go dep (lub3-m (A k) (suc (B k)) (C k) dpt)
  where
  go : ∀ d → suc (B k) ≤ d → ℕ
  go zero    ()
  go (suc dp) (s≤s p) = dp
    where
    -- the callee runs one depth LOWER, off the peeled hypothesis
    q : B k ≤ dp
    q = p
