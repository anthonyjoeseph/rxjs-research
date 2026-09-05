-- THE COUNT A CROSSING FRAME CHARGES, AND IT IS A CHOICE BETWEEN TWO
-- READINGS RATHER THAN A COVERAGE CLAIM.  The arm's constant charge is
-- refuted and the ceiling its replacement would be spent against is
-- refuted too, so what is left open is narrow and decidable: does a
-- count reading what the frame SUBSCRIBES make the frame statement
-- true, at the very programs that killed the constant?  This file is a
-- FORK and not a receipt because its product is that the two candidate
-- counts DISAGREE on the arm's verdict, not that the arm held.
--
-- THE TWO CANDIDATES.  `cnst` is the count as it stands -- one rung,
-- whatever arrives.  `own` is the reading the constant's refutation
-- points at: the arriving observable's own `sizeᵉ`, which is what the
-- subscription runs exactly when the arrival's syntax is what runs --
-- the boundary the coverage note below draws.  They are two functions
-- of one argument, so the disagreement is a value rather than a
-- paragraph.
--
-- FORK: subscribeE-sz-store
--
-- WHY THE ANSWER IS NOT ALREADY KNOWN FROM THE REFUTATION.  A
-- refutation says the constant is too small; it does not say the size
-- is big enough.  The gap is real, because the two grow in different
-- currencies: a duplication chain's emission DOUBLES per rung while
-- its syntax grows by four, so the question is whether `iterSize`'s
-- own doubling, taken at the syntax count, outruns the value's
-- doubling taken at the rung count.
--
-- THE ROWS SAY IT DOES, AT BOTH SHAPES A CROSSING FRAME CAN MEET.  A
-- computing observable -- a duplication chain, where the syntax is
-- small and the emission exponential in it -- and a REIFIED one, where
-- the syntax is the arriving value's own size and the subscription
-- computes nothing at all.  Those are the two mechanisms by which an
-- observable reaches a crossing frame, and the constant loses at the
-- first while the size wins at both.  The second is not decoration:
-- it is the shape the ceiling refutation runs on, so a count that
-- covered only chains would be answering half the question.
--
-- WHAT THE ROWS DO NOT BUY.  They say nothing about the `from-inner`
-- arm, whose program arrives through the store; nothing about the
-- store conclusion this fork names, which no row here runs -- what
-- reaches it is the SEPARATION, since the count both conclusions are
-- denominated in is one object and the arm's value half is now a
-- theorem read at exactly the winner below; nothing about the
-- ceiling, which is refuted against
-- this very count; and nothing about an arrival whose syntax is not
-- what runs.  Both shapes here are read by running exactly what
-- arrived, and an `input i` naming a shared slot is neither: it reads
-- as one whatever stands behind it, which is where the reading these
-- rows prefer is itself refuted (`Refuted.Frame-Step-Size-Slot`).  A
-- green here DISPLACES the cost onto the ceiling rather than paying
-- it.
module Probed.Cross-Count-Fork where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Closed; Val; obs; emptyᵉ; ofᵉ; reify; sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; thru-outer;
  mergeAll-st; installNode; stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Refuted.Frame-Step-Size-Cross using (Γ₁; sl₁; Pow; chain)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE TWO CANDIDATES, at one signature so the disagreement is a value.
-- The argument is the arriving observable's `sizeᵉ`, which is the only
-- reading of it the frame has.
----------------------------------------------------------------------
cnst : ℕ → ℕ
cnst _ = 1

own : ℕ → ℕ
own s = s

-- LOAD-BEARING, and it is this file's product: the two part at the
-- smallest observable a crossing frame can be handed.  `apart` cannot
-- be written when they agree.
separates : Separates cnst own
separates = separates-at 3 (λ ())

----------------------------------------------------------------------
-- SHAPE ONE — A COMPUTING OBSERVABLE.  Twelve duplication rungs: the
-- syntax measures `51` and the emission `8191`, and the cap is tied to
-- the program rather than taken at its floor.
----------------------------------------------------------------------
e₂ : Closed Γ₁ (Pow 12)
e₂ = emptyᵉ

st₂ : EvalSt e₂
st₂ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = Pow 12} nothing 0 [] false)
        (st-init e₂)

vals₂ : List (Val Γ₁ (obs (Pow 12)))
vals₂ = chain 12 ∷ []

out₂ : List (Val Γ₁ (Pow 12))
out₂ = proj₁ (stepFrame {e = e₂} (gasPad 8 g0) 0 0
                (thru-outer mergeAllᵒ 0) root vals₂ false
                (sched-init e₂ sl₁) st₂)

arrival₂ : ℕ
arrival₂ = sizeᵉ (chain 12)

arrival₂≡ : arrival₂ ≡ 51
arrival₂≡ = refl

-- The premises are the arm's own, met at the program's size.
nodes₂ : all (λ kv → boundedNode 51 (proj₂ kv)) (EvalSt.nodes st₂) ≡ true
nodes₂ = refl

prem₂ : valsSz? {Γ = Γ₁} {s = obs (Pow 12)} 51 vals₂ ≡ true
prem₂ = refl

-- LOAD-BEARING: this is the row the refutation already owns, restated
-- as the fork's left side.  It fails.
cnstRow₂ : valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 (cnst arrival₂) 51) out₂
             ≡ false
cnstRow₂ = refl

-- LOAD-BEARING: and the right side holds at the same point, same
-- premises, same state.  It would fail for any count the emission
-- outruns, which is what the row beside it exhibits.
ownRow₂ : valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 (own arrival₂) 51) out₂
            ≡ true
ownRow₂ = refl

----------------------------------------------------------------------
-- SHAPE TWO — A REIFIED OBSERVABLE.  The syntax IS the arriving
-- value's size and the subscription computes nothing, which is the
-- shape a `map-f` upstream produces and the shape the ceiling
-- refutation runs on.  The constant survives here, so this shape
-- separates nothing on its own -- it is here because a count decided
-- on chains alone would be answering half the question.
----------------------------------------------------------------------
pow : (k : ℕ) → Val Γ₁ (Pow k)
pow zero    = 0
pow (suc k) = pow k , pow k

bigObs : Val Γ₁ (obs (Pow 11))
bigObs = ofᵉ (reify {t = Pow 11} (pow 11) ∷ [])

e₃ : Closed Γ₁ (Pow 11)
e₃ = emptyᵉ

st₃ : EvalSt e₃
st₃ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = Pow 11} nothing 0 [] false)
        (st-init e₃)

vals₃ : List (Val Γ₁ (obs (Pow 11)))
vals₃ = bigObs ∷ []

out₃ : List (Val Γ₁ (Pow 11))
out₃ = proj₁ (stepFrame {e = e₃} (gasPad 8 g0) 0 0
                (thru-outer mergeAllᵒ 0) root vals₃ false
                (sched-init e₃ sl₁) st₃)

arrival₃ : ℕ
arrival₃ = sizeᵛ (obs (Pow 11)) bigObs

arrival₃≡ : arrival₃ ≡ 4097
arrival₃≡ = refl

nodes₃ : all (λ kv → boundedNode 4097 (proj₂ kv)) (EvalSt.nodes st₃) ≡ true
nodes₃ = refl

prem₃ : valsSz? {Γ = Γ₁} {s = obs (Pow 11)} 4097 vals₃ ≡ true
prem₃ = refl

-- DEGENERATE on its own -- a reified observable emits the value it was
-- built from, so no count can lose here and the row could not have
-- failed.  It is LOAD-BEARING only jointly: it is what says the size
-- count does not overshoot into falsity at the shape the constant
-- happens to survive.
ownRow₃ : valsSz? {Γ = Γ₁} {s = Pow 11} (iterSize 60 (own arrival₃) 4097) out₃
            ≡ true
ownRow₃ = refl
