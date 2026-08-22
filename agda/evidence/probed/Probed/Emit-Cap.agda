-- TARGET: emit-cap
--
-- THE STATEMENT IS ONE DAY OLD AND ITS PREDECESSOR IS REFUTED, which is
-- the whole reason this file exists before any of it is ground.  The
-- predecessor asked the same thing over a SUMMING `nestDᵗˢ` and was
-- false at a step function that hands its input to an `ofᵉ` list twice
-- (Probed.Nest-Depth §3).  The measure was repaired; whether the
-- repaired statement is TRUE is a different question, and both its sides
-- compute, so it is a question with a cheap answer.
--
-- WHAT IS INSTANTIATED IS THE LEAF EXACTLY, not a paraphrase: the rows
-- build the subscribe the consumer builds — `mintNode`, the installed
-- `*All` node, `thru-outer` on the path — and read `burstND?` at the
-- REACHED scheduler's slots, which is where the leaf reads it.
--
-- NON-VACUITY IS PINNED BY A `false` ROW AT ONE LESS, and it is the
-- strongest form available here.  `burstND?` is an `all` over an `all`,
-- so it is green on an empty burst and green on a burst of no `value`
-- events; a row saying the SAME predicate FAILS at `C - 1` cannot hold
-- unless the burst is non-empty, carries a value, and that value's own
-- nesting is exactly the bound.  Each `true` row below is paired with
-- one, so no row in this file could have passed by being empty.
------------------------------------------------------------------
module Probed.Emit-Cap where

open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Data.List using ([]; _∷_)
open import Data.Bool using (true; false)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Fn; Val; natᵗ; obs; nat̂; strmᵗ; varᵗ; input; ofᵉ;
  mapᵉ; mergeAllᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; root; _↠_; thru-outer; mergeᵒ; merge-st; mintNode; installNode; subscribeE;
  sched-init; st-init)
open import Verify-Budget-Sufficient.Depth-Compositional
  using (innerNest; burstND?)

g40 : Gas
g40 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      g0)))))))))))))))))))))))))))))))))))))))

------------------------------------------------------------------
-- §1  THE DUPLICATION WITNESS — the program that refuted the
-- predecessor, asked of the statement that replaced it.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

dupF : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

inner₁ : Val Γ₀ (obs natᵗ)
inner₁ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- the EMITTER: `dupF` mapped over a source carrying that payload
srcD : Closed Γ₀ (obs natᵗ)
srcD = mapᵉ dupF (ofᵉ (strmᵗ inner₁ ∷ []))

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ srcD

-- the subscribe the consumer builds, term for term
nidD = proj₁ (mintNode (sched-init progD slots₀))

rD = subscribeE g40 srcD (thru-outer mergeᵒ nidD ↠ root) 0 0
       (proj₂ (mintNode (sched-init progD slots₀)))
       (installNode nidD (merge-st 0 false) (st-init progD))

slD : Slots Γ₀
slD = Sched.slots (proj₁ (proj₂ rD))

dupBound : innerNest slD srcD ≡ 2
dupBound = refl

-- LOAD-BEARING: this is the leaf, at the program that killed its
-- predecessor.  Under a summing list clause the emitted inner measures
-- 3 against this bound of 2 and the row is `false`.
dupRow : burstND? slD (innerNest slD srcD) (proj₁ rD) ≡ true
dupRow = refl

-- NON-VACUITY, and tightness with it: one less and the same predicate
-- fails, so the burst is non-empty, it carries a `value`, and that
-- value's nesting is exactly the emitter's.
dupTight : burstND? slD 1 (proj₁ rD) ≡ false
dupTight = refl

------------------------------------------------------------------
-- §2  THE CONNECT SHAPE — where a nesting-only bound is FALSE.
--
-- At `b = input i` the emitter's own `nestDᵉ` is 0 while what it emits
-- comes out of the slot's def, so the leaf can only be true because
-- `innerNest` is a SUM and `slotsNestBelow`'s step at `suc (toℕ i)`
-- pays.  That is the reason the predicate is not two conjuncts, and
-- these rows are the reason to believe it: a nesting-only reading of
-- §1 would pass and this would not.
------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = obs natᵗ ∷ⱽ obs natᵗ ∷ⱽ []ⱽ

-- a payload two `*All` layers deep, so the def carries real nesting
deep₂ : Closed Γ₂ natᵗ
deep₂ = mergeAllᵉ (ofᵉ (strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ []))
          ∷ []))) ∷ []))

def0 : Closed Γ₂ (obs natᵗ)
def0 = ofᵉ (strmᵗ deep₂ ∷ [])

-- one link onto slot 0, so the below-sum has to reach through it
def1 : Closed Γ₂ (obs natᵗ)
def1 = input fz

slots₂ : Slots Γ₂
slots₂ fz      = shared def0 {ok = tt}
slots₂ (fs fz) = shared def1 {ok = tt}

srcC : Closed Γ₂ (obs natᵗ)
srcC = input (fs fz)

progC : Closed Γ₂ natᵗ
progC = mergeAllᵉ srcC

nidC = proj₁ (mintNode (sched-init progC slots₂))

rC = subscribeE g40 srcC (thru-outer mergeᵒ nidC ↠ root) 0 0
       (proj₂ (mintNode (sched-init progC slots₂)))
       (installNode nidC (merge-st 0 false) (st-init progC))

slC : Slots Γ₂
slC = Sched.slots (proj₁ (proj₂ rC))

-- LOAD-BEARING: the leaf at the shape where its nesting half is 0.
connRow : burstND? slC (innerNest slC srcC) (proj₁ rC) ≡ true
connRow = refl

-- and the same non-vacuity pin.  A nesting-only bound would be 0 here,
-- so this row is also what says the below-sum is the term doing the work.
connBound : innerNest slC srcC ≡ 2
connBound = refl

connTight : burstND? slC 1 (proj₁ rC) ≡ false
connTight = refl
