-- ══════════════════════════════════════════════════════════════════
-- AND THE STORE HALVES OF THE CROSSING ARMS DIE THE SAME WAY, which
-- is what makes the count a single decision rather than two.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENTS SAY.  The node table a crossing frame LEAVES is
-- bounded one `iterSize` rung above the table it read, whatever the
-- subscription underneath it installed.  The value halves were killed
-- on what such a frame EMITS; these are the other half of the same
-- denominator, and until they are answered the repair is being
-- decided on half a census.
--
-- WHERE THEY BREAK, AND IT IS ONE HOP FURTHER THAN THE VALUE ARMS.
-- The subscribed program installs its OWN nodes, so the table the
-- premise reads is not the table the conclusion is about.  A `scanᵉ`
-- installs a `scan-st` holding the accumulator, and `boundedNode`
-- reads that accumulator's `sizeᵛ`.  The step function here throws the
-- accumulator away and re-wraps the ARRIVING value as a one-shot
-- observable -- `strmᵗ (ofᵉ (sndᵗ … ∷ []))` -- so what lands in the
-- store is the emission REIFIED, `sizeᵛ` at an `obs` being `sizeᵉ` of
-- the expression it holds and `reify` at a product mirroring the value
-- it came from.  Feed that scan a duplication chain and the stored
-- accumulator is exponential in a program of size sixty-three, against
-- a rung of eight thousand and one.
--
-- SO THE COUNT IS ONE DECISION.  All four arms fail on the same
-- quantity -- the size of what the subscribed program emits -- and it
-- reaches the store only by being written there, so whatever reading
-- covers the emission covers the table by the same argument, and the
-- two halves of an arm cannot be denominated apart.  What these rows
-- do NOT show is that the store needs no charge of its own beyond
-- that: the witness installs one node and a chain of them is not
-- built here.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Size-Cross-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; hot; Tick; Id)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; scanᵉ; nat̂; varᵗ; pairᵗ; sndᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; NodeId; AllOp;
  thru-outer; from-inner; mergeAllᵒ; mergeAll-st; installNode;
  stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

----------------------------------------------------------------------
-- THE TWO STATEMENTS, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulates would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
StepFrameSzStoreOuter : Set
StepFrameSzStoreOuter = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode (iterSize S 1 B) (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (thru-outer op nid)
                                       path vals fin sched st))))))
    ≡ true

StepFrameSzStoreInner : Set
StepFrameSzStoreInner = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode (iterSize S 1 B) (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                                       path vals fin sched st))))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM.  `chain 13` duplicates thirteen times, so its syntax
-- measures fifty-five and it emits at `2 ^ 14 - 1`.  `keep` discards
-- the accumulator and stores the arriving value back as a one-shot
-- observable, which is the one step that converts an EMISSION into a
-- STORE reading.
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

K : ℕ
K = 13

keep : Fn Γ₁ [] [] [] (obs (Pow K) ×ᵗ Pow K) (obs (Pow K))
keep = strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))

inner : Closed Γ₁ (obs (Pow K))
inner = scanᵉ keep (strmᵗ emptyᵉ) (chain K)

-- LOAD-BEARING FIGURES.  The program the premise reads, and the rung
-- one crossing buys once the cap is tied to that very program.
figures : List ℕ
figures = sizeᵉ (chain K) ∷ sizeᵉ inner ∷ iterSize 63 1 63 ∷ []

figures≡ : figures ≡ 55 ∷ 63 ∷ 8001 ∷ []
figures≡ = refl

e₀ : Closed Γ₁ (obs (Pow K))
e₀ = emptyᵉ

----------------------------------------------------------------------
-- WITNESS ONE — the outer arm.  The node the frame reads carries an
-- empty queue, so the entry reading holds at the program's own size;
-- the table it leaves carries the scan the subscription installed.
----------------------------------------------------------------------
st₀ : EvalSt e₀
st₀ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} nothing 0 [] false)
        (st-init e₀)

vals₀ : List (Val Γ₁ (obs (obs (Pow K))))
vals₀ = inner ∷ []

nodes₀ : all (λ kv → boundedNode 63 (proj₂ kv)) (EvalSt.nodes st₀) ≡ true
nodes₀ = refl

prem₀ : valsSz? {Γ = Γ₁} {s = obs (obs (Pow K))} 63 vals₀ ≡ true
prem₀ = refl

post₀ : EvalSt e₀
post₀ = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
                 (thru-outer mergeAllᵒ 0) root vals₀ false
                 (sched-init e₀ sl₁) st₀))))

row₀ : Bool
row₀ = all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv)) (EvalSt.nodes post₀)

row₀≡false : row₀ ≡ false
row₀≡false = refl

stepFrame-sz-store-outer-absurd : StepFrameSzStoreOuter → ⊥
stepFrame-sz-store-outer-absurd pr =
  f≡t (trans (sym row₀≡false)
             (pr {e = e₀} (gasPad 8 g0) 0 0 mergeAllᵒ 0 root vals₀ false
                 (sched-init e₀ sl₁) st₀ 63 63 (s≤s (s≤s z≤n)) refl refl))

----------------------------------------------------------------------
-- WITNESS TWO — the same program through the DRAIN door, which is how
-- the `from-inner` arm is reached.  Here the store premise is the
-- load-bearing one: the queue holds the program, `boundedNode` at a
-- `mergeAll-st` is what bounds it, and the arriving list is empty.
----------------------------------------------------------------------
stQ : EvalSt e₀
stQ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = obs (Pow K)} nothing 1
                      (inner ∷ []) true)
        (st-init e₀)

nodesQ : all (λ kv → boundedNode 63 (proj₂ kv)) (EvalSt.nodes stQ) ≡ true
nodesQ = refl

premQ : valsSz? {Γ = Γ₁} {s = obs (Pow K)} 63 [] ≡ true
premQ = refl

postQ : EvalSt e₀
postQ = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame {e = e₀} (gasPad 8 g0) 0 0
                 (from-inner mergeAllᵒ 0 7) root [] true
                 (sched-init e₀ sl₁) stQ))))

rowQ : Bool
rowQ = all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv)) (EvalSt.nodes postQ)

rowQ≡false : rowQ ≡ false
rowQ≡false = refl

stepFrame-sz-store-inner-absurd : StepFrameSzStoreInner → ⊥
stepFrame-sz-store-inner-absurd pr =
  f≡t (trans (sym rowQ≡false)
             (pr {e = e₀} (gasPad 8 g0) 0 0 mergeAllᵒ 0 7 root [] true
                 (sched-init e₀ sl₁) stQ 63 63 (s≤s (s≤s z≤n)) refl refl))
