-- TARGET: depth-subst-guarded
--
-- DOES UNFOLDING ACCUMULATE?  The rows pin
-- `depthE fuel (unfoldμ body) …` against the body's own cap, which is
-- `depth-μ-bound` — a real body now, over the leaf this file targets,
-- so a row here instantiates that leaf at `cl = μᵉ body`.  The
-- statement `depth-μ-bound` REPLACED named the obstacle: `unfoldμ body`
-- is LARGER than `μᵉ body`, so the size IH fails.  That is the same
-- shape the slot chain was refuted for — a left side growing in a
-- variable the right side does not mention, here the number of
-- unfoldings, which is the GAS.  The obstacle is now moot rather than
-- solved: the cap reads NESTING, which `μᵉ` does not move at all, so
-- the two caps the old body had to bridge are one term.
--
-- SO THE ROWS VARY THE GAS AND NOTHING ELSE.  If depth grew with
-- unfolding, two gas values would give two answers and a large enough
-- one would cross a fixed bound.
--
-- WHY IT IS EXPECTED TO HOLD, and this is the part the probe is
-- checking rather than assuming: `μᵉ` puts its variable in the GUARDED
-- context and `varᵉ` reads only the unguarded one, so a μ-var is
-- reachable ONLY under a `deferᵉ` — by construction of the syntax,
-- not by a discipline anyone has to maintain — and `depthE` returns 0
-- on `deferᵉ` without looking inside.  `unfoldμ` substitutes the whole
-- `μᵉ body` into exactly those positions, so what it grows is the part
-- `depthE` never enters.
module Probed.Depth-Mu where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin  using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; cold)
open import Rx.Exp  using (Ctx; Closed; Exp; natᵗ; strmᵗ; ofᵉ; mergeAllᵉ;
  μᵉ; varᵉ; deferᵉ; unfoldμ; sizeᵉ; emptyᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; Sched; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax;
  depthCap)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the store is deliberately EMPTY of shared defs: a `scripted` slot
-- contributes 0, so `storeNestMax` is 0, the below-sum is 0 at every
-- cut, and the right-hand side is the body's own nesting alone.
-- Nothing can hide in it.
ins : Slots Γ₁
ins fz = scripted (cold [] [])

rootProg : Closed Γ₁ natᵗ
rootProg = emptyᵉ

sched₁ : Sched Γ₁
sched₁ = sched-init rootProg ins

st₁ : EvalSt rootProg
st₁ = st-init rootProg

-- ONE recursive layer: the var is reached through a `deferᵉ`, which is
-- the only way the types allow.
body₁ : Exp Γ₁ (natᵗ ∷ []) [] [] natᵗ
body₁ = mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl))) ∷ []))

-- TWO layers of real structure above the guard, so the rows can tell a
-- depth that tracks the body from one that tracks the unfolding.
body₂ : Exp Γ₁ (natᵗ ∷ []) [] [] natᵗ
body₂ = mergeAllᵉ (ofᵉ (strmᵗ
          (mergeAllᵉ (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl))) ∷ []))) ∷ []))

g2 : Gas
g2 = gs (gs g0)

g20 : Gas
g20 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

_ : storeNestMax sched₁ st₁ ≡ 0
_ = refl

_ : sizeᵉ (μᵉ body₁) ≡ 7
_ = refl

_ : sizeᵉ (μᵉ body₂) ≡ 11
_ = refl

-- the leaf's own right-hand side, read off the CAP.  DEGENERATE on the
-- slot half — this program has no shared slot, so the partial sum is 0
-- at every cut — but NOT degenerate on the figure, and that changed
-- when the cap was tightened to read off nesting alone: it used to read
-- 7 and 12 against depths of 1 and 2, which is to say the statement was
-- almost entirely size slack and these rows could not have caught
-- anything.  They now read 1 and 2, EQUAL to the depth rows below, so
-- the leaf holds here with no room at all and any accumulation
-- whatsoever refutes it.  The size figures above are kept because they
-- are what makes that slack legible as a number.
_ : depthCap body₁ (root {Γ = Γ₁} {t = natᵗ}) sched₁ ≡ 1
_ = refl

_ : depthCap body₂ (root {Γ = Γ₁} {t = natᵗ}) sched₁ ≡ 2
_ = refl

-- LOAD-BEARING, and the gas pair is the whole row: these two differ in
-- nothing but the number of unfoldings available.  WHAT WOULD MAKE THEM
-- FAIL: an arc charged inside a `deferᵉ`, which is where `unfoldμ` puts
-- everything it grows.  A difference between them refutes the leaf
-- outright, since the right-hand side does not mention gas.
_ : depthE g2 (unfoldμ body₁) root 0 0 sched₁ st₁ ≡ 1
_ = refl

_ : depthE g20 (unfoldμ body₁) root 0 0 sched₁ st₁ ≡ 1
_ = refl

_ : depthE g2 (unfoldμ body₂) root 0 0 sched₁ st₁ ≡ 2
_ = refl

_ : depthE g20 (unfoldμ body₂) root 0 0 sched₁ st₁ ≡ 2
_ = refl

-- and the μ itself, which is the clause that spends the leaf
_ : depthE g20 (μᵉ body₂) root 0 0 sched₁ st₁ ≡ 2
_ = refl
