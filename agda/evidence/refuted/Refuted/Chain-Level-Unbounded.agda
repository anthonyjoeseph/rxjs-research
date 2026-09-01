-- ══════════════════════════════════════════════════════════════════
-- THE CHAIN WALK'S LEAF IS FALSE FOR A REASON THAT NEEDS NO STATE:
-- it takes the level it is asserted at as a free parameter and
-- CONCLUDES that level is under the cascade's count.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT ASKS FOR.  The predicate it produces threads a
-- level frame by frame, and at every frame of a non-empty path it
-- asserts a Σ over that frame's increment whose FIRST conjunct is a
-- flat `level + increment ≤ count ⊔ size`.  The leaf's two hypotheses
-- are that the scheduler's slots are the ones the cap is read at, and
-- that the state fits the cap AT THAT LEVEL -- and the second gets
-- WEAKER as the level rises, because the frame ladder only ever widens.
-- So nothing anywhere in the hypotheses bounds the level, and the
-- conclusion bounds it.
--
-- HOW THE WITNESS WORKS, AND WHY IT IS NOT A NUMERIC ROW.  Instantiate
-- at any level one above the count itself.  The cap's own arithmetic is
-- sealed and never has to be computed: `capsOK?` at the raised level
-- comes from the initial state's fit by widening, the path is one frame
-- and a root, and the contradiction is that a successor of a number
-- cannot be under it.  So this refutes the statement at EVERY program,
-- not at a program chosen to break it.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing against the predicate being
-- inhabited at levels the fold actually reaches -- the fold's own
-- invariant now carries the whole remaining cascade's delivery count,
-- and every level it hands out is under that.  What is refuted is the
-- leaf standing free of it: the bound is a property of the CALL, so it
-- has to be a hypothesis of the leaf, and the delivery-indexed form is
-- the one the caller can supply.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Level-Unbounded where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; n≮n)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Exp using (Ctx; Closed; natᵗ)
open import Rx.Prim using (Id)
open import Rx.Evaluator using
  (Sched; EvalSt; Arrival; Path; root; _↠_; take-f; arrTy; sched-init; st-init)
open import Rx.Slots using (Slots)

open import Refuted.Demand-Programs using (Γ₂; progU; insF)
open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt; capsH; sizeCount; frameStep; frameStep-0; frameStep-mono-j;
   2≤capsAt-size; _⊑ᶜ_)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; capsOK?-mono)
open import Verify-Budget-Sufficient.Caps-Bridge using (init-capsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using (chainCapsOK)

prog : Closed Γ₂ natᵗ
prog = progU 2 2

slots : Slots Γ₂
slots = insF 1 2 2

cp : Caps
cp = capsAt prog slots 0

-- the very ceiling the leaf's conclusion asserts, and the level one
-- above it -- neither of which has to REDUCE for the row to hold
ceil : ℕ
ceil = sizeCount cp (capsH prog slots 0) ⊔ Caps.cSize cp

lvl : ℕ
lvl = suc ceil

arr : Arrival Γ₂
arr = record
  { tick = 0 ; ordinal = 0 ; source = 0
  ; elemTy = natᵗ ; payload = 0 ; isLast = false }

pth : Path Γ₂ (arrTy arr) natᵗ
pth = take-f 0 ↠ root

widen : cp ⊑ᶜ frameStep lvl cp
widen = subst (_⊑ᶜ frameStep lvl cp) (frameStep-0 cp)
              (frameStep-mono-j cp (2≤capsAt-size prog slots 0) (z≤n {lvl}))

-- the raised level makes the fit EASIER, which is the whole point: the
-- one hypothesis that mentions the level cannot constrain it
fits : capsOK? (frameStep lvl cp) (sched-init prog slots) (st-init prog) ≡ true
fits = capsOK?-mono cp (frameStep lvl cp) (sched-init prog slots) (st-init prog)
         widen (init-capsOK? prog slots 0)

chain-level-unbounded-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (sl : Slots Γ) (id : ℕ) (L : ℕ) (a : Arrival Γ) (nextId : Id)
     (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
     Sched.slots sched ≡ sl →
     capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
     chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L nextId a path sched st) → ⊥
chain-level-unbounded-absurd H =
  n≮n (ceil + inc) (≤-trans bound (m≤m+n ceil inc))
  where
  got = H slots 0 lvl arr 0 pth (sched-init prog slots) (st-init prog) refl fits
  step = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ got)))))
  inc = proj₁ step
  bound = proj₁ (proj₂ step)
