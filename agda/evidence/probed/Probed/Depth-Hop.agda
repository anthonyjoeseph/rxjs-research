-- THE DEPTH FACE'S NEW CURRENCY, INSTANTIATED AT THE FOUR PROGRAMS
-- THAT KILLED THE OLD ONE.
-- TARGET: depth-hop
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes `Probed.Depth-Hop` unresolvable from there) and nothing
-- in the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THESE FOUR PROGRAMS AND NOT EASIER ONES.  They are the witnesses
-- that refuted `depth-hop`'s predecessor `depth-compositional` and its
-- cap (Depth-Compositional's header carries the refutation; the
-- refutation files went with the statement they refuted).  § 1 and § 2
-- put a payload variable in a scan's SOURCE and re-wrap the
-- accumulator in the step, so the old cap's product term charged
-- nothing and the depth ran to 4 and 8 against a cap of 3.  § 3 and
-- § 4 are the quadratic gadget: a scan whose step merges its
-- accumulator with a constant emitter, whose emission count is
-- quadratic in the tick count while every term of a syntactic sum is
-- linear — depth 35 at four ticks and 70 at six.  So this is a probe
-- reaching the RISKY region rather than a degenerate one: these four
-- programs ARE the region.
--
-- EVERY ROW IS LOAD-BEARING, and the way it could fail is the point.
-- `hopDᵉ`'s scan clause is `(2 + pmᵗ V 0 f) ^ V * (…)`, an EXPONENTIAL
-- in the refold bound `V`, so a row is a real test only at a `V` small
-- enough that the exponential has not swallowed the question.  The
-- depths are pinned by `refl` beside each domination row, so a row
-- cannot pass by the left-hand side collapsing to 0.
--
-- ⚠ AND THE COVERAGE IS `V ∈ {1, 4}` AT THE ROOT PATH WITH AN EMPTY
-- STORE — and `V = 1` only on the two small programs, since the
-- gadget needs the exponential.  Nothing here says anything about a non-empty path, a slot
-- telescope, or the `input` clause — which is where the predecessor's
-- first two refutations lived — and monotonicity of `hopDᵉ` in `V` is
-- not proven anywhere, so these rows do not transfer to another `V`.
module Probed.Depth-Hop where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; fstᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; root; sched-init; st-init)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (pathNestD)

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

-- the step RE-WRAPS its accumulator: one `*All` layer per delivered payload
gA : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gA = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

-- and the payload variable sits in the scan's SOURCE, so the count the
-- old cap's product term read was the variable's own width — zero
fA : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fA = strmᵗ (scanᵉ gA (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

------------------------------------------------------------------
-- § 1  three payloads — the depth the old cap read 3 against
------------------------------------------------------------------

progA : Closed Γ₀ natᵗ
progA = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ []))))

schedA : Sched Γ₀
schedA = sched-init progA slots₀

stA : EvalSt progA
stA = st-init progA

_ : depthE (gN 20) progA root 0 0 schedA stA ≡ 4
_ = refl

_ : (depthE (gN 20) progA root 0 0 schedA stA
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₀) progA + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progA root 0 0 schedA stA
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progA + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 2  seven payloads — the gap is the PAYLOAD COUNT, so this row is
-- what says no constant repair reaches the old cap: the depth doubles
-- while a syntactic measure of this program does not.
--
-- ⚠ AND THIS PROGRAM IS WHERE THE REFOLD FACTOR IS THE WHOLE MARGIN.
-- Its widening lives in a LITERAL LIST, which `hopDᵉ` charges 0 for at
-- every `V` (`hopDᵗ (nat̂ _) = 0`), so nothing but the scan's
-- `(2 + pmᵗ V 0 f) ^ V` grows when the source goes three literals to
-- seven — while `depthE` doubles to 8.  The `V = 1` row below therefore
-- holds with NO ROOM AT ALL, which is the strongest form a green row
-- comes in and the reason it is worth re-running after anything touches
-- the refold clause.  One step down, at `V = 0`, the factor is 1 and
-- this program REFUTES the bound: that is `Refuted.Depth-Hop`, and it is
-- why the statement conditions `V` at all.
------------------------------------------------------------------

progB : Closed Γ₀ natᵗ
progB = mergeAllᵉ (mergeAllᵉ (mapᵉ fA
          (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])) ∷ []))))

schedB : Sched Γ₀
schedB = sched-init progB slots₀

stB : EvalSt progB
stB = st-init progB

_ : depthE (gN 20) progB root 0 0 schedB stB ≡ 8
_ = refl

_ : (depthE (gN 20) progB root 0 0 schedB stB
       ≤ᵇ hopDᵉ 1 (slotHop 1 slots₀) progB + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

_ : (depthE (gN 20) progB root 0 0 schedB stB
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progB + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

------------------------------------------------------------------
-- § 3 and § 4  THE QUADRATIC GADGET.  The step merges the accumulator
-- with a CONSTANT emitter, so emissions grow by a constant per tick
-- and the `*All` over the scan runs over every accumulator emitted.
-- The step is ADDITIVE and not duplicating on purpose: doubling the
-- accumulator doubles its SYNTAX per tick too, and normalising that
-- costs minutes where this costs seconds.
------------------------------------------------------------------

dupF : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
         ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ [])))

vD : Closed Γ₀ natᵗ
vD = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ vD ∷ []))))

schedD : Sched Γ₀
schedD = sched-init progD slots₀

stD : EvalSt progD
stD = st-init progD

_ : depthE (gN 200) progD root 0 0 schedD stD ≡ 35
_ = refl

_ : (depthE (gN 200) progD root 0 0 schedD stD
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progD + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl

vC : Closed Γ₀ natᵗ
vC = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
       (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ [])))

progC : Closed Γ₀ natᵗ
progC = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ vC ∷ []))))

schedC : Sched Γ₀
schedC = sched-init progC slots₀

stC : EvalSt progC
stC = st-init progC

-- the row the old cap lost by: 70 against a syntactic sum of 56
_ : depthE (gN 200) progC root 0 0 schedC stC ≡ 70
_ = refl

_ : (depthE (gN 200) progC root 0 0 schedC stC
       ≤ᵇ hopDᵉ 4 (slotHop 4 slots₀) progC + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
      ≡ true
_ = refl
