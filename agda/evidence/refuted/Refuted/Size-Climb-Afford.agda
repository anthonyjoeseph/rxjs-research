-- ══════════════════════════════════════════════════════════════════
-- AND THE CLIMB IS NOT THE REPAIR EITHER: the shape that answers the
-- closed form one stratum up is unaffordable at the second crossing
-- frame, at every cap this development admits.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  A ceiling and a ledger are both closed
-- forms in the cap, the width and the level, and the evaluator's own
-- charge header records that no closed form in those three closes the
-- loop a crossing frame opens.  What answers that shape one stratum up
-- is a RECURSION ON A DEPTH FUEL with every quantity read at the level
-- the walk has CLIMBED to, and this row writes the size walk's ceiling
-- in exactly that shape: fuel outside, rungs threaded, and the charge
-- at each rung read at the level that rung stands at.  The question a
-- discharge then turns on is not whether the shape is statable -- it
-- is, and it is written here -- but whether the walk factor can afford
-- what it climbs to.
--
-- WHERE IT BREAKS.  The walk factor affords a rung count POLYNOMIAL in
-- the cap: a cap squared plus a cap plus a cap squared, each spent at
-- one frame charge, which is what carries the level under the nesting
-- budget.  The climb passes that at its SECOND crossing frame, and by
-- the whole ladder rather than by a factor: THREE rungs of the size
-- ladder already exceed the entire polynomial the factor allows, and
-- the second frame charges its level after a cap's worth of rungs
-- rather than three.  So the gap is a ladder against a polynomial, and
-- widening the polynomial buys one rung of the ladder at most.
--
-- AND THE CHARGE IS THE SMALLEST HONEST ONE, which is what makes this
-- a finding about the SHAPE rather than about a generous reading.  A
-- crossing frame charges what it subscribes -- a burst's worth of
-- observables plus the telescope -- and this climb charges ONE level
-- per frame, with no width factor and no telescope.  That a single
-- frame genuinely reaches the level is not assumed here: it is
-- instantiated at numerals in `Refuted.Walk-Ceil-Ledger`, whose count
-- row lands one payload exactly on the level the walk climbed to.
--
-- WHAT THIS DOES NOT SHOW.  It does not refute the depth-fuel shape
-- itself, which is discharged one face over and is what prices the
-- caps ladder.  What it refutes is that shape spent against THIS
-- factor: the caps face's own ceiling is defined by READING its climb,
-- so the climb is affordable there by construction, while the size
-- walk's level must fit under a nesting budget that is a fixed
-- exponential in a polynomial and reads nothing.  Nor does it reach a
-- climb charging less than a level per crossing frame -- but no such
-- reading is honest, since the observable a crossing subscribes is
-- bounded by nothing smaller.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Size-Climb-Afford where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; 1+n≰n;
  +-comm; +-mono-≤; +-monoʳ-≤; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
  *-identityˡ; *-identityʳ; m≤m+n; m≤n+m)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Evaluator using (iterSize)
open import Verify-Budget-Sufficient.Caps using (iterSize-mono-count)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (frameCh)

----------------------------------------------------------------------
-- THE CEILING IN THE SHAPE THAT ANSWERS A CLOSED FORM -- fuel on the
-- outside, rungs threaded through, and the charge at each frame read
-- at the level that frame stands at rather than at the level the walk
-- entered.  It is the size walk's own reading: a frame's arrival is
-- bounded by the level in hand, which is `iterSize S k S` at rung `k`.
----------------------------------------------------------------------
szCh : ℕ → ℕ → ℕ                     -- cap, rungs climbed so far
szCh S k = iterSize S k S

szClimb : ℕ → ℕ → ℕ → ℕ              -- cap, depth fuel, rungs so far
szClimb S zero    k = k
szClimb S (suc d) k = szClimb S d (k + szCh S k)

----------------------------------------------------------------------
-- WHAT THE WALK FACTOR AFFORDS, in the factor's own two pieces: the
-- ledger range its premise admits, times the per-frame charge every
-- rung of that ledger is spent at.
----------------------------------------------------------------------
walkAfford : ℕ → ℕ
walkAfford S = (S * S + S + S * S) * frameCh S S

SizeClimbAfford : Set
SizeClimbAfford = ∀ (S : ℕ) → 8 ≤ S → szClimb S 2 0 ≤ walkAfford S

module _ (S : ℕ) (8≤S : 8 ≤ S) where

  -- LOAD-BEARING: the whole ledger the factor affords sits below three
  -- rungs of the size ladder, and three rungs are what the second
  -- crossing frame's own entry level has already passed.
  climb-outruns-afford : suc (walkAfford S) ≤ szClimb S 2 0
  climb-outruns-afford =
    ≤-trans (s≤s afford≤6)
            (≤-trans 6<8 (≤-trans 8E4≤iter3
                                  (≤-trans iter3≤iterS
                                           (m≤n+m (iterSize S S S) S))))
    where
    1≤S : 1 ≤ S
    1≤S = ≤-trans (s≤s z≤n) 8≤S
    3≤S : 3 ≤ S
    3≤S = ≤-trans (s≤s (s≤s (s≤s z≤n))) 8≤S
    E2 E3 E4 : ℕ
    E2 = S * S
    E3 = S * E2
    E4 = S * E3
    1≤E2 : 1 ≤ E2
    1≤E2 = ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤S 1≤S)
    1≤E3 : 1 ≤ E3
    1≤E3 = ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤S 1≤E2)
    1≤E4 : 1 ≤ E4
    1≤E4 = ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤S 1≤E3)
    E3≤E4 : E3 ≤ E4
    E3≤E4 = ≤-trans (≤-reflexive (sym (*-identityˡ E3))) (*-monoˡ-≤ E3 1≤S)
    E2≤E4 : E2 ≤ E4
    E2≤E4 =
      ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ E2)))
                       (*-monoˡ-≤ E2 1≤S))
              E3≤E4
    -- the factor's premise, multiplied out against its frame charge
    afford-shape : walkAfford S ≡ 2 * E4 + (3 * E3 + E2)
    afford-shape =
      solve 1 (λ a → (a :* a :+ a :+ a :* a) :* (a :* (con 1 :+ a))
                     := con 2 :* (a :* (a :* (a :* a)))
                        :+ (con 3 :* (a :* (a :* a)) :+ a :* a))
            refl S
    eq6 : 2 * E4 + (3 * E4 + E4) ≡ 6 * E4
    eq6 = solve 1 (λ b → con 2 :* b :+ (con 3 :* b :+ b) := con 6 :* b) refl E4
    afford≤6 : walkAfford S ≤ 6 * E4
    afford≤6 =
      ≤-trans (≤-reflexive afford-shape)
              (≤-trans (+-monoʳ-≤ (2 * E4)
                          (+-mono-≤ (*-monoʳ-≤ 3 E3≤E4) E2≤E4))
                       (≤-reflexive eq6))
    eq8 : 6 * E4 + 2 * E4 ≡ 8 * E4
    eq8 = solve 1 (λ b → con 6 :* b :+ con 2 :* b := con 8 :* b) refl E4
    1≤2E4 : 1 ≤ 2 * E4
    1≤2E4 = ≤-trans 1≤E4 (m≤m+n E4 (E4 + 0))
    6<8 : suc (6 * E4) ≤ 8 * E4
    6<8 = ≤-trans (≤-reflexive (+-comm 1 (6 * E4)))
                  (≤-trans (+-monoʳ-≤ (6 * E4) 1≤2E4) (≤-reflexive eq8))
    -- three rungs of the ladder, multiplied out
    iter3-shape : iterSize S 3 S ≡ (S + 2 * E2 + 4 * E3) + 8 * E4
    iter3-shape =
      solve 1 (λ a → a :* (con 1 :+ con 2
                            :* (a :* (con 1 :+ con 2
                                  :* (a :* (con 1 :+ con 2 :* a)))))
                     := (a :+ con 2 :* (a :* a) :+ con 4 :* (a :* (a :* a)))
                        :+ con 8 :* (a :* (a :* (a :* a))))
            refl S
    8E4≤iter3 : 8 * E4 ≤ iterSize S 3 S
    8E4≤iter3 =
      ≤-trans (m≤n+m (8 * E4) (S + 2 * E2 + 4 * E3))
              (≤-reflexive (sym iter3-shape))
    iter3≤iterS : iterSize S 3 S ≤ iterSize S S S
    iter3≤iterS = iterSize-mono-count S S 1≤S 3≤S

  -- LOAD-BEARING, AND THE OTHER DIRECTION: one crossing frame IS
  -- affordable, so what the row above reports is the second frame and
  -- not an arithmetic that was never satisfiable.
  one-frame-affordable : szClimb S 1 0 ≤ walkAfford S
  one-frame-affordable =
    ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-mono-≤ ledger 1≤frame)
    where
    1≤S : 1 ≤ S
    1≤S = ≤-trans (s≤s z≤n) 8≤S
    ledger : S ≤ S * S + S + S * S
    ledger = ≤-trans (m≤n+m S (S * S)) (m≤m+n (S * S + S) (S * S))
    1≤frame : 1 ≤ frameCh S S
    1≤frame =
      ≤-trans (≤-reflexive (sym (*-identityˡ 1))) (*-mono-≤ 1≤S (s≤s z≤n))

size-climb-afford-absurd : SizeClimbAfford → ⊥
size-climb-afford-absurd pr = go 8 ≤-refl
  where
  go : ∀ (S : ℕ) → 8 ≤ S → ⊥
  go S h = 1+n≰n (≤-trans (climb-outruns-afford S h) (pr S h))
