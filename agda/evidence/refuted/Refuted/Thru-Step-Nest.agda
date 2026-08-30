-- ══════════════════════════════════════════════════════════════════
-- ONE CONSUME STEP CANNOT BE STATED AT A SINGLE GRANT, and the three
-- `*All` heads fall together because the emission comes out of the
-- subscribe they share.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  An arrival admitted at a `*All` head, whose
-- nesting is inside a grant `G`, delivers values whose nesting is inside
-- THE SAME `G` -- one bound named once, serving as both the hypothesis on
-- what comes in and the conclusion about what goes out.
--
-- WHY IT LOOKED RIGHT.  Every arm of every head either leaves the state
-- alone or runs one `subscribeInner` and writes one node, and the nesting
-- measure is MAX-based: a `*All` boundary charges one `suc`, a pair takes
-- a maximum, and a map charges its two halves by SUM.  Read that way a
-- step looks like it can only re-deliver what it was handed, and the
-- single grant reads as the honest shared currency.
--
-- WHERE IT BREAKS.  A map's step function may NAME ITS PAYLOAD TWICE --
-- once in its own body and once in the source it maps over -- and the
-- measure charges the two halves by sum while the SUBSTITUTION puts the
-- payload's whole nesting in both.  So the arrival reads `constant + d`
-- and what the subscribe delivers reads `2d`, and the constant here is
-- ZERO: the doubling is unaccompanied.  This is the same substitution
-- the caps face already knows doubles a value (`Refuted.Apply-Fn-Nest`),
-- arriving at the step rather than at the frame.
--
-- THE WITNESS is a payload carrying `k` real `mergeAllᵉ` boundaries,
-- handed to a duplicating step function at a merge node WITH ROOM, so
-- the admit arm actually runs.  At `k = 6` the arrival reads SIX and the
-- delivery reads TWELVE, and the ratio is exactly two at every `k` --
-- so the gap grows without limit in a parameter the grant does see, and
-- the row is not a degenerate corner.  Both of the premises the step
-- names besides the grant are pinned true at the witness.
--
-- AND THE PAYLOAD MUST BE CARRIED, NOT FLATTENED, which is the one thing
-- that makes this hard to hit by accident: put a `mergeAllᵉ` under the
-- map and the subscribe drains the depth away before the step function
-- ever sees it, and the delivered reading goes to ZERO.  An arrival built
-- that way clears the statement at every level and reports nothing.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here says the step is unprovable --
-- it says the grant cannot be ONE number.  The subscribe's own delivered
-- bound is already proven in `src` at an INDEXED grant, which inflates
-- the arrival's bound rather than reusing it; what died is the flat form
-- and the reading of the fit off a burst claim at a single `G`.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Step-Nest where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ;
         varᵗ; caseᵗ; inlᵗ; syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Path; _↠_; thru-outer;
         mergeAllᵒ; switchᵒ; exhaustᵒ; installNode; mergeAll-st; switch-st;
         exhaust-st; thruConsume)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nestCapsOK?)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the duplicating step: the payload lands once in the map's own step
-- function -- through a case SCRUTINEE, the one additive slot a `Tm`
-- has -- and once in the source it maps over
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

-- a payload whose reading is exactly `k`
E : ℕ → Val Γ₂ (obs natᵗ)
E zero    = ofᵉ (nat̂ 0 ∷ [])
E (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (E k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- the arrival CARRIES the payload to the step function rather than
-- draining it: a `mergeAllᵉ` under the map subscribes the depth away
arr : ℕ → Val Γ₂ (obs (obs natᵗ))
arr k = mapᵉ dup (ofᵉ (strmᵗ (E k) ∷ []))

κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

-- a merge node WITH ROOM, so the arm that subscribes is the one taken
stM : EvalSt prog
stM = installNode 7 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
                 (st-init prog)

stS : EvalSt prog
stS = installNode 8 (switch-st nothing false) (st-init prog)

stX : EvalSt prog
stX = installNode 9 (exhaust-st false false) (st-init prog)

cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6))
           (pWᵛ 2 slots (obs (obs natᵗ)) (arr 6)) 0

-- NON-VACUITY: a delivered reading over an empty burst measures nothing
burstLen : ℕ
burstLen = length (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6)
             (sched-init prog slots) stM))

burstLen≡1 : burstLen ≡ 1
burstLen≡1 = refl

-- the two premises the step names besides the grant, pinned true where
-- the rows run rather than assumed
prems : Bool × Bool
prems = nestValOK? cap (obs (obs natᵗ)) (arr 6)
      , nestCapsOK? cap (sched-init prog slots) stM

prems≡ : prems ≡ (true , true)
prems≡ = refl

-- the grant, at the SMALLEST value the statement's own third premise
-- permits -- so the hypothesis holds by `refl` and nothing is given away
arrival : ℕ
arrival = nestDᵛ (obs (obs natᵗ)) (arr 6)

deliveredM deliveredS deliveredX : ℕ
deliveredM = nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6)
               (sched-init prog slots) stM))
deliveredS = nestDᵛˢ (proj₁ (thruConsume gasBig switchᵒ 8 κ 0 0 (arr 6)
               (sched-init prog slots) stS))
deliveredX = nestDᵛˢ (proj₁ (thruConsume gasBig exhaustᵒ 9 κ 0 0 (arr 6)
               (sched-init prog slots) stX))

-- THE FIGURES, PINNED.  Spelled out rather than left inline so that any
-- repair moving either measure fails here, naming the number, instead of
-- quietly turning the crossing into an equality.
arrival≡6 : arrival ≡ 6
arrival≡6 = refl

deliveredM≡12 : deliveredM ≡ 12
deliveredM≡12 = refl

deliveredS≡12 : deliveredS ≡ 12
deliveredS≡12 = refl

deliveredX≡12 : deliveredX ≡ 12
deliveredX≡12 = refl

-- `delivered ≤ᵇ arrival` reduces to `false`, so `T` of it IS the empty type
thru-step-merge-absurd : deliveredM ≤ arrival → ⊥
thru-step-merge-absurd h = ≤⇒≤ᵇ h

thru-step-switch-absurd : deliveredS ≤ arrival → ⊥
thru-step-switch-absurd h = ≤⇒≤ᵇ h

thru-step-exhaust-absurd : deliveredX ≤ arrival → ⊥
thru-step-exhaust-absurd h = ≤⇒≤ᵇ h
