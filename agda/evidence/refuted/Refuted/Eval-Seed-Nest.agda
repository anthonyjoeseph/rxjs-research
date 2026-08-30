-- ══════════════════════════════════════════════════════════════════
-- AN EVALUATED SEED CAN BE MORE NESTED THAN ITS TERM, and one `caseᵗ`
-- is enough to say so.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  Evaluating a CLOSED term does not deepen it:
-- `nestDᵛ t (evalTm tm) ≤ nestDᵗ tm`.  It is the one inequality the
-- subscribe ceiling's scan clause needs and does not have.  A scan's
-- trade is generous in exactly the right currency -- the subject sheds
-- the seed's nesting and the frame takes only the step function's, so
-- the seed's nesting is spare -- and then the store takes it back,
-- because what a scan installs is the EVALUATED seed.  So the clause
-- closes iff evaluation does not deepen.
--
-- WHY IT LOOKED RIGHT, AND WHY IT IS NOT `applyFn`'s FAILURE AGAIN.
-- The value measure JOINS where the syntactic one SUMS -- a pair takes
-- the max of its components -- so duplication is free on the value side
-- and an empty environment has nothing to duplicate anyway.  What that
-- misses is that a closed term still BINDS: a `caseᵗ` puts its
-- scrutinee's value into a branch, and the branch may name it on both
-- sides of a sum the OBSERVABLE measure takes.  `Refuted.Apply-Fn-Nest`
-- kills the additive form with an explicit payload; this kills it with
-- no payload at all, which is the form `evalTm` is.
--
-- THE WITNESS is the smallest term of that shape: a `caseᵗ` whose
-- scrutinee is one `mergeAllᵉ` deep and whose left branch is a `scanᵉ`
-- naming the bound variable BOTH as its seed and inside its source.
-- The unsubstituted branch weighs one and the scrutinee one, so the
-- term charges two; the value carries the scrutinee's nesting twice
-- over and weighs three.  The gap is the occurrence count, so it grows
-- without bound in a term the charge does not move with at all.
--
-- WHAT DIES is exactly one thing: the route that closes the scan clause
-- out of the trade's own slack.  What survives is the shape
-- `Nest-Subst` already proves -- the seed's nesting is charged once per
-- OCCURRENCE, so the honest bound carries a factor exponential in the
-- term's sync size -- and moving that factor into the ceiling's own
-- measure is the repair this points at rather than one it rules out.
-- The entry can afford it: what the entry compares against is a DOUBLE
-- exponential in the size cap, and the argument that gets there spends
-- only a single one, so a further single-exponential factor sits inside
-- the gap between the two.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Eval-Seed-Nest where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (natᵗ; obs; Tm; evalTm; ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; varᵗ; inlᵗ; caseᵗ; fstᵗ; strmᵗ)
open import Data.Maybe using (nothing)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Refuted.Demand-Programs using (Γ₂)

-- the branch names its bound observable TWICE, once on each side of a
-- sum `nestDᵉ` takes at `scanᵉ`: as the fold's SEED, and inside the
-- source the fold runs over
branchL : Tm Γ₂ [] [] (obs natᵗ ∷ []) (obs (obs natᵗ))
branchL =
  strmᵗ (scanᵉ (fstᵗ (varᵗ (here refl)))
               (varᵗ (here refl))
               (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ []))))

seed : Tm Γ₂ [] [] [] (obs (obs natᵗ))
seed =
  caseᵗ {s = obs natᵗ} {t = obs natᵗ}
    (inlᵗ (strmᵗ (mergeAllᵉ nothing (ofᵉ []))))
    branchL
    (strmᵗ emptyᵉ)

row : ℕ × ℕ
row = nestDᵛ (obs (obs natᵗ)) (evalTm seed)
    , nestDᵗ seed

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
evald≡3 : proj₁ row ≡ 3
evald≡3 = refl

syntactic≡2 : proj₂ row ≡ 2
syntactic≡2 = refl

eval-seed-nest-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `3 ≤ᵇ 2` reduces to `false`, so `T` of it IS the empty type
eval-seed-nest-absurd h = ≤⇒≤ᵇ h
