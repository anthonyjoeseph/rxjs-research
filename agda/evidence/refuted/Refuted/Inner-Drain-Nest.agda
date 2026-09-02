-- ══════════════════════════════════════════════════════════════════
-- THE INNER FRAME CHARGES NOTHING AND THE DRAIN UNDER IT SUBSCRIBES,
-- so the free per-frame bound at `from-inner` is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A `from-inner` frame moves neither its node
-- table nor the values it hands on: `nodesMax st′ ⊔ nestDᵛˢ out ≤
-- nodesMax st ⊔ nestDᵛˢ vals`, a bound with no charge in it at all.  It
-- is the arm that reads as free among the five, and the reason it reads
-- that way is real -- `pathNestD` charges a `from-inner` nothing, so a
-- charge here would have nowhere to come from.
--
-- WHERE IT BREAKS.  A `from-inner` at `fin` with no live registration is
-- exactly where `innerFinish` runs `mergeAllDrain`, and the drain
-- SUBSCRIBES a queued inner.  The values that subscription emits leave
-- through this frame, and the queue is priced by `nestDᵉ` -- which is
-- ADDITIVE at `mapᵉ`, while the substitution the subscription performs
-- is not.  So a queued `mapᵉ` whose step function names its payload
-- twice emits a value deeper than the whole queue is charged, and one
-- element is enough: eighty against forty, and the gap is the payload's
-- own depth, so no constant and no summand fixed by the program repairs
-- it.
--
-- WHAT DIES AND WHAT DOES NOT.  The zero-charge form dies.  Nothing here
-- says the walk cannot be bounded -- it says the bound cannot be free at
-- this frame, so either `pathNestD` grows a term at `from-inner` or the
-- arm takes the drain's charge from somewhere its hypotheses carry.  The
-- gap is the occurrence count of a step function this statement does not
-- mention at all, which is the same repair `Refuted.Apply-Fn-Nest`
-- forced on the map frame: a factor the syntax can see.
--
-- WHAT IS HAND-BUILT, AND WHY IT DOES NOT SOFTEN THE FINDING.  The state
-- is `st-init` plus ONE `installNode`, and the statement quantifies over
-- every `st`, so this refutes it as written -- the same freedom
-- `Refuted.Chain-Step-Nodes` spends on the path.  Nor is the queue an
-- unreachable shape: its one element is a literal an outer `ofᵉ` emits,
-- so a run reaches this table.  What a run does NOT hand over cheaply is
-- an `inst` the registry does not keep alive, and that argument is free
-- in the statement too.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Inner-Drain-Nest where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; emptyᵉ; ofᵉ; mapᵉ; switchAllᵉ;
         varᵗ; nat̂; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; mergeAll-st; Frame; from-inner; mergeAllᵒ; root; _↠_; stepFrame; sched-init;
  st-init; installNode)
open import Verify-Budget-Sufficient.Nest-Store using (frameNestF; nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; frameNestD)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; insT)

----------------------------------------------------------------------
-- THE WITNESS.  `Refuted.Step-Frame-Nest-Dup`'s pair -- a payload forty
-- `*All` layers deep and a step function naming it on both sides of a
-- `mapᵉ` sum -- packaged as the observable a drain would subscribe.
-- The depth is a free parameter, so the gap is unbounded rather than a
-- corner: the queue is charged the payload and the emit carries two.
----------------------------------------------------------------------

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the step function names its payload TWICE, once on each side of the
-- `mapᵉ` sum: as the list the source emits, and as the mapped result
dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dupFn = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

-- the queued inner: one emit, and that emit is the substitution
o : Closed Γ₂ (obs (obs natᵗ))
o = mapᵉ dupFn (ofᵉ (strmᵗ (deepV 40) ∷ []))

e : Closed Γ₂ (obs (obs natᵗ))
e = emptyᵉ

slots : Slots Γ₂
slots = insT 0 0 0

sched₀ : Sched Γ₂
sched₀ = sched-init e slots

-- one lane taken, one inner parked, the outer already done
st₀ : EvalSt e
st₀ = installNode 0 (mergeAll-st nothing 1 (o ∷ []) true) (st-init e)

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

-- the frame is reached carrying nothing of its own: every value in the
-- conclusion comes out of the drain
vals : List (Val Γ₂ (obs (obs natᵗ)))
vals = []

f : Frame Γ₂ (obs (obs natᵗ)) (obs (obs natᵗ))
f = from-inner mergeAllᵒ 0 1

row : ℕ × ℕ
row = let r = stepFrame gas 0 0 f root vals true sched₀ st₀
      in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)
       , nodesMax st₀ ⊔ nestDᵛˢ vals

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
drained≡80 : proj₁ row ≡ 80
drained≡80 = refl

queued≡40 : proj₂ row ≡ 40
queued≡40 = refl

stepFrame-nodes-inner-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `80 ≤ᵇ 40` reduces to `false`, so `T` of it IS the empty type
stepFrame-nodes-inner-absurd h = ≤⇒≤ᵇ h

----------------------------------------------------------------------
-- AND THE ASSEMBLY FALLS TO THE SAME WITNESS, which is the half worth
-- having: `frameNestF` reads a `from-inner` as one and `frameNestD` as
-- zero, so the parent's charge at this frame IS the leaf's bound, at
-- the smallest width it admits.  A leaf refuted under a parent that
-- still typechecks is a repair with nowhere to land.
----------------------------------------------------------------------

parentCharge : ℕ
parentCharge = frameNestF f ^ 1 * (proj₂ row + 1 * frameNestD f)

parent≡40 : parentCharge ≡ 40
parent≡40 = refl

stepFrame-nodes-at-inner-absurd : proj₁ row ≤ parentCharge → ⊥
stepFrame-nodes-at-inner-absurd h = ≤⇒≤ᵇ h

----------------------------------------------------------------------
-- AND THE PROGRAM'S OWN NESTING UNIT DOES NOT PAY FOR IT EITHER, which
-- is the repair this refutation most invites and the one worth closing
-- here.  `foldPath-nodes` already carries a `nestUnit e sl` that the
-- per-frame statement lacks, so the cheap reading is that the arm is
-- merely missing the term its own parent has -- and at the witness
-- above that reading FITS, eighty against a charge of eighty-two.
--
-- It fits by coincidence.  `nestUnit` is a DEPTH, and depth is additive
-- under `mapᵉ`; what the drain's subscription performs is a
-- SUBSTITUTION, whose cost is linear in the number of times the step
-- function names its payload.  A third occurrence moves the emit to a
-- hundred and twenty and leaves the unit at forty-two.  So the gap is
-- unbounded in a quantity `nestUnit` does not measure, and no summand
-- in this currency closes it: what is owed is a FACTOR in the SIZE of
-- the substituted function, which is the shape `applyFn-nest` already
-- charges the map frame and which the store -- not the frame -- is
-- where this one would have to come from.
----------------------------------------------------------------------

-- the same payload, named THREE times instead of two
tripFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
tripFn = strmᵗ (mapᵉ (varᵗ (there (here refl)))
                 (ofᵉ (strmᵗ (mapᵉ (varᵗ (there (here refl)))
                        (ofᵉ (varᵗ (here refl) ∷ []))) ∷ [])))

o₃ : Closed Γ₂ (obs (obs natᵗ))
o₃ = mapᵉ tripFn (ofᵉ (strmᵗ (deepV 40) ∷ []))

st₃ : EvalSt e
st₃ = installNode 0 (mergeAll-st nothing 1 (o₃ ∷ []) true) (st-init e)

row₃ : ℕ × ℕ
row₃ = let r = stepFrame gas 0 0 f root vals true sched₀ st₃
       in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)
        , nodesMax st₃ ⊔ nestDᵛˢ vals

drained₃≡120 : proj₁ row₃ ≡ 120
drained₃≡120 = refl

queued₃≡40 : proj₂ row₃ ≡ 40
queued₃≡40 = refl

-- charged against the program that IS the queued observable, so the
-- unit is as large as this currency can honestly make it
unitCharge : ℕ
unitCharge = proj₂ row₃ + 1 * nestUnit o₃ slots

unitCharge≡82 : unitCharge ≡ 82
unitCharge≡82 = refl

stepFrame-nodes-inner-unit-absurd : proj₁ row₃ ≤ unitCharge → ⊥
stepFrame-nodes-inner-unit-absurd h = ≤⇒≤ᵇ h

----------------------------------------------------------------------
-- AND THE POTENTIAL FACE FALLS TO THE SAME WITNESS, which is what
-- makes this refutation worth keeping rather than superseding.  The
-- currency moved -- from a maximum of depths to a FACTOR times a depth
-- -- and the drain is untouched by the move, because the move happens
-- at the frames that substitute and this frame does not.  `pathΦF`
-- reads a `from-inner` as one and `pathNestD` charges it nothing, so at
-- the root the conclusion is the drained values' own depth read against
-- `U`, with no factor in front of it to absorb anything.
--
-- WHAT MAKES IT UNBOUNDED RATHER THAN A CORNER.  The hypothesis is
-- `all _ []`: the completion walk carries no value, so it holds at
-- EVERY `U`, and the reader may pick `U` as generously as the queue is
-- charged.  Then `deepV k` under the doubling step function drains
-- `2 * k` against it.  Nothing in the statement -- not `vals`, not
-- `path`, not `B` -- moves with `k`, so no constant and no term in
-- these three closes the gap.  The repair is a fact about what the
-- QUEUE may hold, which is a property of the state and belongs on the
-- invariant record rather than in this signature.
----------------------------------------------------------------------

drainedΦ : ℕ
drainedΦ = nestDᵛˢ (proj₁ (stepFrame gas 0 0 f root vals true sched₀ st₀))

drainedΦ≡80 : drainedΦ ≡ 80
drainedΦ≡80 = refl

-- the walk arrives with nothing in hand, so the premise is discharged
-- at a `U` twice what the whole queue is charged
Φ-hyp : valsΦ? 3 40 (f ↠ root) vals ≡ true
Φ-hyp = refl

stepFrame-nest-Φ-inner-absurd :
  valsΦ? 3 40 root
    (proj₁ (stepFrame gas 0 0 f root vals true sched₀ st₀)) ≡ true → ⊥
stepFrame-nest-Φ-inner-absurd ()

-- and the third occurrence moves the drain again while the premise
-- does not move at all, which is the gap being in `k` rather than in a
-- constant
drainedΦ₃ : ℕ
drainedΦ₃ = nestDᵛˢ (proj₁ (stepFrame gas 0 0 f root vals true sched₀ st₃))

drainedΦ₃≡120 : drainedΦ₃ ≡ 120
drainedΦ₃≡120 = refl

stepFrame-nest-Φ-inner-trip-absurd :
  valsΦ? 3 80 root
    (proj₁ (stepFrame gas 0 0 f root vals true sched₀ st₃)) ≡ true → ⊥
stepFrame-nest-Φ-inner-trip-absurd ()
