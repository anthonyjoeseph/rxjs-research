-- ══════════════════════════════════════════════════════════════════
-- THE OUTER CROSSING'S VALUE-READING COUNT IS FALSE TOO, and what
-- defeats it is not the arriving program's size but the fact that
-- `sizeᵉ` does not measure what a subscription RUNS.  An arriving
-- observable may be `input i`, whose syntax is ONE and whose run is
-- the whole of slot `i`'s shared definition.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
-- ══════════════════════════════════════════════════════════════════
--
-- WHAT THE STATEMENT SAYS.  A `thru-outer` frame charges the ladder
-- one rung per unit of `sizeᵛ` summed over the observables that
-- arrived, which at an observable-typed value is that program's own
-- `sizeᵉ`.  That is the reading the constant charge was replaced by,
-- and it is the only reading of the arriving value the frame has.
--
-- WHERE IT BREAKS.  `sizeᵉ (input i) = 1`, by the same one-line clause
-- that prices a variable, and nothing in the statement's premises
-- mentions the slot telescope: the store premise reads the node table
-- and the value premise reads the arriving syntax, so a shared slot is
-- off both axes.  Subscribing `input i` at a `shared` slot connects
-- that slot's definition and runs it, so a duplication chain parked in
-- the slot emits exponentially against a count pinned at one.
--
-- AND THE SECOND ROW SAYS THE AXIS IS MEASURE-SIDE, which is what
-- makes the pair a refutation of the READING rather than of a cap
-- choice.  Both rows tie the cap to the slot definition's own size,
-- which is the most generous tie the premises admit; one more rung
-- behind the slot takes the emission from `8191` to `16383` while the
-- rung it is measured against moves from `5253` to `6105`.  The count
-- between them does not move at all, and cannot: it reads a syntax
-- node that is one whatever stands behind it.
--
-- WHAT SURVIVES.  The frame does run the program, so a count reading
-- what runs is still the shape of the repair -- what these rows kill
-- is the identification of "what runs" with "what arrived".  A reading
-- that resolved the slot would need the telescope, which `szCount` is
-- not handed; a premise bounding `slotsSize` would put the whole
-- telescope on the ladder at every frame.  These rows say nothing
-- about the `from-inner` arm, whose program arrives through the store
-- and is refuted separately, and nothing about either store half.
module Refuted.Frame-Step-Size-Slot where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Maybe using (nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; Tick; Id)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; input; nat̂; varᵗ; pairᵗ; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; NodeId; AllOp;
  thru-outer; mergeAllᵒ; mergeAll-st; installNode;
  stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?; szCount)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
StepFrameSzOuterOwn : Set
StepFrameSzOuterOwn = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S (szCount (thru-outer {Γ = Γ} {u = u} op nid) vals) B)
    (proj₁ (stepFrame sf id now (thru-outer op nid) path vals fin
              sched st)) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `Pw k` is the balanced product of `2 ^ k`
-- naturals, `dupG` writes its payload into both arms, and `chnG k` is
-- `k` of them over a singleton source -- syntax `3 + 4k`, emission
-- `2 ^ suc k - 1`.  It is written over an arbitrary context because
-- the two rows live in two telescopes.
----------------------------------------------------------------------
Pw : ℕ → Ty
Pw zero    = natᵗ
Pw (suc k) = Pw k ×ᵗ Pw k

dupG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (Pw k) (Pw (suc k))
dupG = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

chnG : ∀ {n} {Γ : Ctx n} (k : ℕ) → Closed Γ (Pw k)
chnG zero    = ofᵉ (nat̂ 0 ∷ [])
chnG (suc k) = mapᵉ dupG (chnG k)

----------------------------------------------------------------------
-- WITNESS ONE — twelve rungs behind the slot.  The definition measures
-- `51`, the arriving observable measures `1`, the cap is tied to the
-- definition and one rung buys `5253`, and the run emits `8191`.
----------------------------------------------------------------------
Γ₂ : Ctx 1
Γ₂ = Pw 12 ∷ⱽ []ⱽ

sl₂ : Slots Γ₂
sl₂ fzero = shared (chnG 12)

e₂ : Closed Γ₂ (Pw 12)
e₂ = emptyᵉ

st₂ : EvalSt e₂
st₂ = installNode 0 (mergeAll-st {Γ = Γ₂} {t = Pw 12} nothing 0 [] false)
        (st-init e₂)

vals₂ : List (Val Γ₂ (obs (Pw 12)))
vals₂ = input fzero ∷ []

out₂ : List (Val Γ₂ (Pw 12))
out₂ = proj₁ (stepFrame {e = e₂} (gasPad 64 g0) 0 0
                (thru-outer mergeAllᵒ 0) root vals₂ false
                (sched-init e₂ sl₂) st₂)

-- THE TWO READINGS SIDE BY SIDE: the definition that runs against the
-- syntax the count is allowed to see.
figures₂ : List ℕ
figures₂ = sizeᵉ (chnG {Γ = Γ₂} 12)
         ∷ szCount (thru-outer {Γ = Γ₂} {u = Pw 12} mergeAllᵒ 0) vals₂
         ∷ iterSize 51 1 51 ∷ []

figures₂≡ : figures₂ ≡ 51 ∷ 1 ∷ 5253 ∷ []
figures₂≡ = refl

-- THE PREMISES HOLD, spelled out so the witness cannot be read as one
-- that merely fails to satisfy them.
nodes₂ : all (λ kv → boundedNode 51 (proj₂ kv)) (EvalSt.nodes st₂) ≡ true
nodes₂ = refl

prem₂ : valsSz? {Γ = Γ₂} {s = obs (Pw 12)} 51 vals₂ ≡ true
prem₂ = refl

row₂ : Bool
row₂ = valsSz? {Γ = Γ₂} {s = Pw 12}
         (iterSize 51 (szCount (thru-outer {Γ = Γ₂} {u = Pw 12} mergeAllᵒ 0)
                        vals₂) 51)
         out₂

row₂≡false : row₂ ≡ false
row₂≡false = refl

stepFrame-sz-outer-own-absurd : StepFrameSzOuterOwn → ⊥
stepFrame-sz-outer-own-absurd pr =
  f≡t (trans (sym row₂≡false)
             (pr {e = e₂} (gasPad 64 g0) 0 0 mergeAllᵒ 0 root vals₂ false
                 (sched-init e₂ sl₂) st₂ 51 51 (s≤s (s≤s z≤n)) refl refl))

----------------------------------------------------------------------
-- WITNESS TWO — one more rung behind the slot, cap moved with it.  The
-- definition measures `55` and one rung buys `6105`, against `16383`.
-- The count is `1` here as well, which is the finding.
----------------------------------------------------------------------
Γ₃ : Ctx 1
Γ₃ = Pw 13 ∷ⱽ []ⱽ

sl₃ : Slots Γ₃
sl₃ fzero = shared (chnG 13)

e₃ : Closed Γ₃ (Pw 13)
e₃ = emptyᵉ

st₃ : EvalSt e₃
st₃ = installNode 0 (mergeAll-st {Γ = Γ₃} {t = Pw 13} nothing 0 [] false)
        (st-init e₃)

vals₃ : List (Val Γ₃ (obs (Pw 13)))
vals₃ = input fzero ∷ []

out₃ : List (Val Γ₃ (Pw 13))
out₃ = proj₁ (stepFrame {e = e₃} (gasPad 64 g0) 0 0
                (thru-outer mergeAllᵒ 0) root vals₃ false
                (sched-init e₃ sl₃) st₃)

figures₃ : List ℕ
figures₃ = sizeᵉ (chnG {Γ = Γ₃} 13)
         ∷ szCount (thru-outer {Γ = Γ₃} {u = Pw 13} mergeAllᵒ 0) vals₃
         ∷ iterSize 55 1 55 ∷ []

figures₃≡ : figures₃ ≡ 55 ∷ 1 ∷ 6105 ∷ []
figures₃≡ = refl

nodes₃ : all (λ kv → boundedNode 55 (proj₂ kv)) (EvalSt.nodes st₃) ≡ true
nodes₃ = refl

prem₃ : valsSz? {Γ = Γ₃} {s = obs (Pw 13)} 55 vals₃ ≡ true
prem₃ = refl

row₃ : Bool
row₃ = valsSz? {Γ = Γ₃} {s = Pw 13}
         (iterSize 55 (szCount (thru-outer {Γ = Γ₃} {u = Pw 13} mergeAllᵒ 0)
                        vals₃) 55)
         out₃

row₃≡false : row₃ ≡ false
row₃≡false = refl

stepFrame-sz-outer-own-absurd′ : StepFrameSzOuterOwn → ⊥
stepFrame-sz-outer-own-absurd′ pr =
  f≡t (trans (sym row₃≡false)
             (pr {e = e₃} (gasPad 64 g0) 0 0 mergeAllᵒ 0 root vals₃ false
                 (sched-init e₃ sl₃) st₃ 55 55 (s≤s (s≤s z≤n)) refl refl))
