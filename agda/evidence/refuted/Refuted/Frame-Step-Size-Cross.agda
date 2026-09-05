-- ══════════════════════════════════════════════════════════════════
-- THE TWO CROSSING FRAMES DO NOT COST ONE LEVEL EITHER, and the
-- repair that saved the map arm cannot be carried across: what a
-- crossing frame emits is EXPONENTIAL in what its premises bound,
-- while one `iterSize` rung is quadratic in it.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENTS SAY.  A `thru-outer` frame is handed
-- observables and a `from-inner` frame is handed the values one has
-- delivered; both are priced at ONE rung above the level the arriving
-- values stand at, whatever the subscription underneath them runs.
-- A constant charge had already fallen once at the map arm, in
-- `Frame-Step-Size-Level`, and the repair there was to let the count
-- READ the frame -- a map pays `sizeᵗ fn`, a scan
-- `length vals * suc (sizeᵗ fn)`.  Neither crossing frame could be
-- repaired that way, because its syntax is not what runs: the
-- observable does, and it arrives as a VALUE.
--
-- WHERE THEY BREAK.  A `thru-outer` step runs its arriving
-- observable's whole synchronous chain and hands back what it emitted.
-- Program size grows by FOUR per `mapᵉ (pairᵗ (varᵗ …) (varᵗ …))`,
-- because `sizeᵉ` at a map adds; the emitted value DOUBLES, because
-- `sizeᵛ` at a product adds its two arms and the duplicator writes the
-- payload into both.  So a `k`-fold duplication chain has `sizeᵉ =
-- 3 + 4k` and emits at `2^(suc k) - 1`, against a rung of `S + 2·S·B`.
-- The `from-inner` arm dies at the same values through the drain door:
-- a finishing inner drains its `*All` node's queue, and the queue's
-- own reading -- `boundedNode` at a `mergeAll-st` -- bounds exactly
-- the `sizeᵉ` of what is parked there.
--
-- AND THE SECOND ROW IS THE EXPENSIVE ONE.  The first witness takes
-- `S` at its floor, so it could be read as a statement that merely
-- forgot to tie the cap to the program.  The second ties it as
-- tightly as anything at this arm could: the cap is set to the
-- arriving observable's own size, `S = B = 51`, and the rung is then
-- `5253` against an emission of `8191`.  No polynomial tie repairs
-- this, since the crossing is exponential-against-quadratic; the
-- count is what has to move.
--
-- WHAT SURVIVES, AND IT IS THE SHAPE OF THE REPAIR.  `iterSize S j B`
-- dominates `2 ^ j * B` (`iterSize-2^`), so charging rungs in a
-- quantity that BOUNDS what runs buys back the whole blowup at once --
-- the same move the map arm already made, denominated in the value
-- that runs rather than in the frame that is written.  The two arms
-- reach that quantity differently, and the second witness is what says
-- so: the outer arm's program arrives, so its own syntax is readable,
-- while the inner arm's is parked in the `*All` node and is legible
-- only through the store bound the premise carries.  What
-- these rows do NOT touch is the STORE half: the queue this witness
-- drains is empty afterwards and the chain installs no node, so
-- `stepFrame-sz-store-inner` and `stepFrame-sz-store-outer` are
-- untouched here and neither is evidence for the other.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Size-Cross where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; hot; Tick; Id)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; nat̂; varᵗ; pairᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; NodeId;
  thru-outer; from-inner; AllOp; mergeAllᵒ; mergeAll-st; installNode;
  stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

----------------------------------------------------------------------
-- THE TWO STATEMENTS, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulates would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
StepFrameSzOuter : Set
StepFrameSzOuter = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S 1 B)
    (proj₁ (stepFrame sf id now (thru-outer op nid) path vals fin
              sched st)) ≡ true

StepFrameSzInner : Set
StepFrameSzInner = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S 1 B)
    (proj₁ (stepFrame sf id now (from-inner op allNid inst) path vals fin
              sched st)) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  One slot, never consulted.  `Pow k` is the
-- balanced product of `2 ^ k` naturals, `dup` writes its payload into
-- both arms, and `chain k` is `k` of them over a singleton source.
-- The two measures pull apart here and nowhere else: `sizeᵉ` counts
-- the map, `sizeᵛ` counts the tree the map builds.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

Pow : ℕ → Ty
Pow zero    = natᵗ
Pow (suc k) = Pow k ×ᵗ Pow k

dup : ∀ {k} → Fn Γ₁ [] [] [] (Pow k) (Pow (suc k))
dup = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

chain : (k : ℕ) → Closed Γ₁ (Pow k)
chain zero    = ofᵉ (nat̂ 0 ∷ [])
chain (suc k) = mapᵉ dup (chain k)

-- THE TWO MEASURES, SIDE BY SIDE.  Four per rung against a doubling.
growth : List ℕ
growth = sizeᵉ (chain 0) ∷ sizeᵉ (chain 6) ∷ sizeᵉ (chain 12) ∷ []

growth≡ : growth ≡ 3 ∷ 27 ∷ 51 ∷ []
growth≡ = refl

----------------------------------------------------------------------
-- WITNESS ONE — the cap at its floor.  `S = 2`, six rungs: the
-- arriving observable measures `27`, one rung buys `110`, and what it
-- emits measures `127`.
----------------------------------------------------------------------
e₁ : Closed Γ₁ (Pow 6)
e₁ = emptyᵉ

st₁ : EvalSt e₁
st₁ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = Pow 6} nothing 0 [] false)
        (st-init e₁)

vals₁ : List (Val Γ₁ (obs (Pow 6)))
vals₁ = chain 6 ∷ []

out₁ : List (Val Γ₁ (Pow 6))
out₁ = proj₁ (stepFrame {e = e₁} (gasPad 8 g0) 0 0
                (thru-outer mergeAllᵒ 0) root vals₁ false
                (sched-init e₁ sl₁) st₁)

figures₁ : List ℕ
figures₁ = sizeᵉ (chain 6) ∷ iterSize 2 1 27 ∷ []

figures₁≡ : figures₁ ≡ 27 ∷ 110 ∷ []
figures₁≡ = refl

-- THE PREMISES HOLD, spelled out so the witness cannot be read as one
-- that merely fails to satisfy them.
nodes₁ : all (λ kv → boundedNode 27 (proj₂ kv)) (EvalSt.nodes st₁) ≡ true
nodes₁ = refl

prem₁ : valsSz? {Γ = Γ₁} {s = obs (Pow 6)} 27 vals₁ ≡ true
prem₁ = refl

row₁ : Bool
row₁ = valsSz? {Γ = Γ₁} {s = Pow 6} (iterSize 2 1 27) out₁

row₁≡false : row₁ ≡ false
row₁≡false = refl

----------------------------------------------------------------------
-- WITNESS TWO — the cap tied to the program.  `S = B = 51`, twelve
-- rungs: one rung buys `5253` and the emission measures `8191`.  This
-- is the row that says the count is what has to move.
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

figures₂ : List ℕ
figures₂ = sizeᵉ (chain 12) ∷ iterSize 51 1 51 ∷ []

figures₂≡ : figures₂ ≡ 51 ∷ 5253 ∷ []
figures₂≡ = refl

nodes₂ : all (λ kv → boundedNode 51 (proj₂ kv)) (EvalSt.nodes st₂) ≡ true
nodes₂ = refl

prem₂ : valsSz? {Γ = Γ₁} {s = obs (Pow 12)} 51 vals₂ ≡ true
prem₂ = refl

row₂ : Bool
row₂ = valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 1 51) out₂

row₂≡false : row₂ ≡ false
row₂≡false = refl

stepFrame-sz-outer-absurd : StepFrameSzOuter → ⊥
stepFrame-sz-outer-absurd pr =
  f≡t (trans (sym row₂≡false)
             (pr {e = e₂} (gasPad 8 g0) 0 0 mergeAllᵒ 0 root vals₂ false
                 (sched-init e₂ sl₁) st₂ 51 51 (s≤s (s≤s z≤n)) refl refl))

----------------------------------------------------------------------
-- WITNESS THREE — the same values through the DRAIN door, which is
-- how the `from-inner` arm is reached at all.  A finishing inner
-- whose `*All` node holds a parked observable subscribes it, and the
-- node's own reading is what bounds that observable, so the store
-- premise is the load-bearing one here and the arriving list is
-- empty.  Same `S`, same `B`, same emission.
----------------------------------------------------------------------
stQ : EvalSt e₂
stQ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = Pow 12} nothing 1
                      (chain 12 ∷ []) true)
        (st-init e₂)

nodesQ : all (λ kv → boundedNode 51 (proj₂ kv)) (EvalSt.nodes stQ) ≡ true
nodesQ = refl

premQ : valsSz? {Γ = Γ₁} {s = Pow 12} 51 [] ≡ true
premQ = refl

outQ : List (Val Γ₁ (Pow 12))
outQ = proj₁ (stepFrame {e = e₂} (gasPad 8 g0) 0 0
                (from-inner mergeAllᵒ 0 7) root [] true
                (sched-init e₂ sl₁) stQ)

rowQ : Bool
rowQ = valsSz? {Γ = Γ₁} {s = Pow 12} (iterSize 51 1 51) outQ

rowQ≡false : rowQ ≡ false
rowQ≡false = refl

stepFrame-sz-inner-absurd : StepFrameSzInner → ⊥
stepFrame-sz-inner-absurd pr =
  f≡t (trans (sym rowQ≡false)
             (pr {e = e₂} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root [] true
                 (sched-init e₂ sl₁) stQ 51 51 (s≤s (s≤s z≤n)) refl refl))
