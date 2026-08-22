------------------------------------------------------------------
-- `depthCap` IS FALSE — AND THIS IS THE PARENT, NOT A LEAF.
--
-- `Refuted.Emit-Map` and `Refuted.Emit-Scan` refute two LEAVES of
-- `depth-compositional-go`'s `*All` burst arm: the emitted payload's
-- nesting is not bounded by the emitter's `nestDᵉ`, because the product
-- term `outWᵉ src * nestDᵗ f` reads the count at the UNSUBSTITUTED
-- source, where a bare payload variable is 0.  A refuted leaf leaves
-- open whether the CONCLUSION it was invented to support is still true —
-- a leaf can be false while its parent survives on slack elsewhere in
-- the cap, and `Refuted.Emit-Map`'s own `progTopDepth`/`progTopCap` rows
-- are exactly that case: depth 1 against a cap of 2, with the inflated
-- payload never entered.
--
-- IT DOES NOT SURVIVE.  Put TWO `*All` layers above the map, so the
-- walk descends into the accumulators the substituted scan emits, and
-- the exported conclusion reads FOUR against a cap of THREE.
--
-- AND THE GAP IS THE PAYLOAD COUNT, WHICH IS WHY ONE ROW WOULD NOT HAVE
-- BEEN ENOUGH.  `progB` differs from `progA` only in the width of the
-- literal list the map's source delivers — three payloads against seven —
-- and the depth goes 4 → 8 while the cap stays at 3 in both.  The cap is
-- read off the program's syntax, the depth off the count the RUN
-- delivers, and nothing in the syntax bounds that count: the scan's step
-- re-wraps its accumulator once per payload, so the accumulator's nesting
-- is the payload count, and the payload count is a WIDTH.
--
-- SO THE SIZE TERM `depthCapN` DROPPED WAS LOAD-BEARING, and the
-- argument that dropped it is the refuted one: an emitted inner was
-- held to be arbitrarily LARGER than its emitter but never more deeply
-- NESTED, "because that measure's product term charges one re-wrap per
-- delivered payload precisely to cover this".  It charges nothing,
-- because it charges at the wrong term.  Both rows below are stated
-- against `depthCap`, so they hold whatever `depth-compositional`'s
-- internal decomposition becomes; the exported widening `cap-≤-store`
-- re-admits `sizeᵉ`, and at these two witnesses that slack still
-- covers the gap — which says where the next question is, not that the
-- cap is repairable by keeping it.
------------------------------------------------------------------
module Refuted.Depth-Comp where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ; ofᵉ;
  emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; fstᵗ; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Depth-Compositional using (depthCap; storeNestMax)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)

g20 : Gas
g20 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

-- the step RE-WRAPS its accumulator: one `*All` layer per delivered payload
gA : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gA = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

-- and the payload variable sits in the scan's SOURCE, so the count the
-- product term reads is the variable's own width — zero
fA : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fA = strmᵗ (scanᵉ gA (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

fnA : nestDᵗ slots₀ fA ≡ 1
fnA = refl


------------------------------------------------------------------
-- § 1  three payloads: depth 4, cap 3
------------------------------------------------------------------

wide3 : Closed Γ₀ natᵗ
wide3 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

bA : Closed Γ₀ (obs natᵗ)
bA = ofᵉ (strmᵗ wide3 ∷ [])

-- TWO `*All` layers above the map, so the walk actually DESCENDS into
-- the accumulators the scan emits
progA : Closed Γ₀ natᵗ
progA = mergeAllᵉ (mergeAllᵉ (mapᵉ fA bA))

schedA : Sched Γ₀
schedA = sched-init progA slots₀

stA : EvalSt progA
stA = st-init progA

capA : nestDᵉ slots₀ progA ≡ 3
capA = refl

theCap : depthCap progA (root {Γ = Γ₀} {t = natᵗ}) schedA ≡ 3
theCap = refl

theDepth : depthE g20 progA (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedA stA ≡ 4
theDepth = refl


------------------------------------------------------------------
-- § 2  seven payloads: depth 8, and the SAME cap 3
------------------------------------------------------------------

wide7 : Closed Γ₀ natᵗ
wide7 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])

bB : Closed Γ₀ (obs natᵗ)
bB = ofᵉ (strmᵗ wide7 ∷ [])

progB : Closed Γ₀ natᵗ
progB = mergeAllᵉ (mergeAllᵉ (mapᵉ fA bB))

schedB : Sched Γ₀
schedB = sched-init progB slots₀

stB : EvalSt progB
stB = st-init progB

theCapB : depthCap progB (root {Γ = Γ₀} {t = natᵗ}) schedB ≡ 3
theCapB = refl

theDepthB : depthE g20 progB (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedB stB ≡ 8
theDepthB = refl


------------------------------------------------------------------
-- and the statement itself, taken as a hypothesis so that this file
-- says the STATEMENT is false rather than reporting on whatever
-- decomposition `src` currently proves it through
------------------------------------------------------------------

depth-compositional-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g b κ bid now sched st ≤ depthCap b κ sched) → ⊥
depth-compositional-absurd h with h g20 progA root 0 0 schedA stA
... | s≤s (s≤s (s≤s ()))


------------------------------------------------------------------
-- § 3  AND THE EXPORTED WIDENING DOES NOT SURVIVE EITHER.
--
-- `cap-≤-store` re-admits the size term this cap dropped, so § 1 and
-- § 2 leave open the obvious repair: put `sizeᵉ` back.  It is refuted
-- here, by machine rather than by argument.
--
-- THE KNOB IS THE TICK COUNT AND THE TWO SIDES DIFFER IN DEGREE.  The
-- scan's step merges its accumulator with a CONSTANT emitter, so the
-- accumulator's emission count grows by a constant per tick, and the
-- `*All` over the scan runs over every accumulator it emitted — total
-- emissions QUADRATIC in the tick count.  Every term of the exported
-- bound is linear in it.  Four ticks: depth 35 under a bound of 52.
-- Six ticks: depth 70 over a bound of 56.  The pair is the evidence,
-- not either row — one row above the crossing would leave open whether
-- some re-weighting of the same syntactic sum covers it, and a
-- difference in degree says no re-weighting does.
--
-- The step is ADDITIVE and not duplicating on purpose: doubling the
-- accumulator doubles its SYNTAX per tick too, and normalising that
-- costs minutes where this costs seconds — same crossing, and the rows
-- have to be cheap enough to keep in the gate.
------------------------------------------------------------------

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

dupF : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])) ∷ [])))

base3 : Closed Γ₀ natᵗ
base3 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ [])

-- emits 2^0 + 2^1 + 2^2 + 2^3 values from syntax of constant size
vC : Closed Γ₀ natᵗ
vC = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) base3)

bC : Closed Γ₀ (obs natᵗ)
bC = ofᵉ (strmᵗ vC ∷ [])

progC : Closed Γ₀ natᵗ
progC = mergeAllᵉ (mergeAllᵉ (mapᵉ fA bC))

schedC : Sched Γ₀
schedC = sched-init progC slots₀

stC : EvalSt progC
stC = st-init progC

sizeC : sizeᵉ progC ≡ 46
sizeC = refl

nestC : nestDᵉ slots₀ progC ≡ 10
nestC = refl

-- the EXPORTED right-hand side, measured whole rather than argued from
-- its two zero terms
exportRHS : sizeᵉ progC + nestDᵉ slots₀ progC
              + pathLen (root {Γ = Γ₀} {t = natᵗ}) + storeNestMax schedC stC ≡ 56
exportRHS = refl

depthC : depthE (gN 200) progC (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedC stC ≡ 70
depthC = refl


-- TWO TICKS FEWER, AND THE BOUND WINS THERE.  The emission count is
-- QUADRATIC in the tick count — the step adds a constant emitter per
-- tick, and the merge runs over every accumulator the scan emitted —
-- while every term of the exported bound is LINEAR in it.  So the two
-- sides differ in DEGREE, and the pair of rows is what says so: at
-- four ticks the bound holds with room, at six it is beaten.  A row
-- above the crossing alone would leave open whether some re-weighting
-- of the same syntactic sum could be made to cover it.
base4 : Closed Γ₀ natᵗ
base4 = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

vD : Closed Γ₀ natᵗ
vD = mergeAllᵉ (scanᵉ dupF (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) base4)

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ (mergeAllᵉ (mapᵉ fA (ofᵉ (strmᵗ vD ∷ []))))

schedD : Sched Γ₀
schedD = sched-init progD slots₀

stD : EvalSt progD
stD = st-init progD

exportRHS-D : sizeᵉ progD + nestDᵉ slots₀ progD
                + pathLen (root {Γ = Γ₀} {t = natᵗ}) + storeNestMax schedD stD ≡ 52
exportRHS-D = refl

depthD : depthE (gN 200) progD (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedD stD ≡ 35
depthD = refl
