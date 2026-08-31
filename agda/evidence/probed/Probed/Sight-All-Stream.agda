-- ══════════════════════════════════════════════════════════════════
-- THE ENTRY FOLD, AT THE FAMILY THAT KILLED ITS PREDECESSOR.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT THE ROWS ARE.  Each is an INHABITANT of the fold itself rather
-- than a boolean mirror of it, so there is no second definition here
-- that could drift from the one the postulate names.  The subscribe is
-- the evaluator's, the stream is what it returns, and the grant is the
-- payload-side tower the statement carries.
--
-- WHY THIS FAMILY.  The payload MAPS and its step function names its
-- argument twice, so one application emits a term about double the
-- payload's own sync size.  That is the growth that outran a charge
-- read at the ARRIVAL, and the rows here ask whether the grant covers
-- the charge that replaced it, which reads the arrival's DEPTH.
--
-- WHAT THE COLUMNS SAY, over four layers of that duplication: the
-- charge reads one, two, three, four while the grant's EXPONENT reads
-- sixteen, twenty-three, thirty, thirty-seven.  One side is linear in
-- the layer and the other is a tower over something linear in it, so
-- the margin is not a scale that a deeper family could close.
--
-- NOT COVERED: the two heads other than `mergeAllᵒ`; any path other
-- than `root`, so the telescope summand is nought at every row here
-- and the wrap is nought with it; a telescope of more than one slot;
-- and an arrival that is a slot REFERENCE, which is the shape the wrap
-- summand exists for and which the consume's own probe carries.
--
-- TARGET: sight-all-stream @29db77
-- ══════════════════════════════════════════════════════════════════
module Probed.Sight-All-Stream where

open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; InstEmit)
open import Rx.Exp
  using (Ctx; Closed; Fn; Val; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ;
         subscribeE; splitEvents; mintNode; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; allFresh; slotWrapSum)
open import Verify-Budget-Sufficient.Depth-Sighted using (StreamFit)

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ᵛ []ᵛ

gas : Gas
gas = gasPad 400 g0

prog : Closed Γₛ (obs natᵗ)
prog = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

flat : Closed Γₛ (obs natᵗ)
flat = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

sl : Slots Γₛ
sl fzero = shared flat {ok = tt}

sched : Sched Γₛ
sched = sched-init prog sl

st : EvalSt prog
st = st-init prog

pad : ℕ → Closed Γₛ natᵗ
pad zero    = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))
pad (suc j) = mergeAllᵉ nothing (ofᵉ (strmᵗ (pad j) ∷ []))

dupO : Fn Γₛ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dupO = strmᵗ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ []))

b : ℕ → Closed Γₛ (obs (obs natᵗ))
b j = mapᵉ dupO (ofᵉ (strmᵗ (pad j) ∷ []))

κ : Path Γₛ (obs natᵗ) (obs natᵗ)
κ = root

nid : _
nid = proj₁ (mintNode sched)

runOf : ℕ → _
runOf j =
  subscribeE gas (b j) (thru-outer mergeAllᵒ nid ↠ κ) 0 0
    (proj₂ (mintNode sched))
    (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

G : ℕ → ℕ
G j = 2 ^ syncSizeᵉ (b j) * (pathNestD κ + suc (nestDᵉ (b j)))
    + 1 * slotWrapSum sl

-- LOAD-BEARING: the whole fold, inhabited, at the duplicating payload
fitDup : StreamFit 1 sl (G 0) κ (proj₁ (runOf 0))
fitDup = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

oDup : ℕ → Val Γₛ (obs (obs natᵗ))
oDup j = ofᵉ (strmᵗ (pad j) ∷ strmᵗ (pad j) ∷ [])

-- ── the sides, so the row is read as a margin and not as a green ────
sides : ℕ
sides = demand 0 + 1000000 * G 0
  where
  demand : ℕ → ℕ
  demand j = pathNestD κ + nestDᵛ (obs (obs natᵗ)) (oDup j) + 1 * slotWrapSum sl

sides≡ : sides ≡ 131072000001
sides≡ = refl

-- ── and the family where the refuted gap COMPOUNDED ────────────────
-- Each layer wraps the payload in another duplicating map, so the
-- arrival's size doubles while the program grows by a fixed number of
-- constructors.  That is the axis the tower could not survive.
dupN : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dupN = strmᵗ (mergeAllᵉ nothing
         (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

srcN : ℕ → Closed Γₛ (obs natᵗ)
srcN zero    = ofᵉ (strmᵗ (pad 0) ∷ [])
srcN (suc k) = mapᵉ dupN (srcN k)

bN : ℕ → Closed Γₛ (obs (obs natᵗ))
bN k = mapᵉ dupO (srcN k)

runN : ℕ → _
runN k =
  subscribeE gas (bN k) (thru-outer mergeAllᵒ nid ↠ κ) 0 0
    (proj₂ (mintNode sched))
    (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

Gn : ℕ → ℕ
Gn k = 2 ^ syncSizeᵉ (bN k) * (pathNestD κ + suc (nestDᵉ (bN k)))
     + 1 * slotWrapSum sl

-- LOAD-BEARING: three layers up, where the arrival's size is a tower
fitN₁ : StreamFit 1 sl (Gn 1) κ (proj₁ (runN 1))
fitN₁ = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

fitN₂ : StreamFit 1 sl (Gn 2) κ (proj₁ (runN 2))
fitN₂ = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

fitN₃ : StreamFit 1 sl (Gn 3) κ (proj₁ (runN 3))
fitN₃ = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

-- and the two columns, read off the RUN rather than off a hand-built
-- term: what the charge asks, against what the grant's exponent is
layers : ℕ
layers = ask 0 + 100 * ask 1 + 10000 * ask 2 + 1000000 * ask 3
  where
  ask : ℕ → ℕ
  ask k with proj₁ (runN k)
  ... | []      = 0
  ... | em ∷ _  with proj₁ (splitEvents {A = Val Γₛ (obs natᵗ)} (InstEmit.events em))
  ...   | []     = 0
  ...   | o ∷ _  = pathNestD κ + nestDᵛ (obs (obs natᵗ)) o + 1 * slotWrapSum sl

layers≡ : layers ≡ 4030201
layers≡ = refl

exps : ℕ
exps = syncSizeᵉ (bN 0) + 100 * syncSizeᵉ (bN 1)
     + 10000 * syncSizeᵉ (bN 2) + 1000000 * syncSizeᵉ (bN 3)

exps≡ : exps ≡ 37302316
exps≡ = refl
