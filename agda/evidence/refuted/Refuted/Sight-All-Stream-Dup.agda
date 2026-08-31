-- ══════════════════════════════════════════════════════════════════
-- A MAP DOUBLES WHAT IT EMITS, AND THE GRANT IS A TOWER IN THE
-- PAYLOAD'S OWN SIZE, so the entry stream's fit is FALSE as stated.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  Subscribing an `*All` head's payload hands
-- back a stream, and every value in it is granted a tower in the
-- PAYLOAD's sync size times the path it arrives under, plus the wrap
-- the telescope carries.  Both terms are read off syntax that exists
-- before the subscription runs.
--
-- WHERE IT BREAKS, AND IT IS THE EXPONENT.  A payload may MAP, and the
-- step function may name its argument twice; then one application
-- emits a term holding two copies of what came in, so the emitted
-- value's sync size is about DOUBLE the payload's while the grant's
-- exponent is the payload's alone.  Both sides are towers of two, so a
-- constant factor between the exponents is not a scale error -- the
-- ratio is itself a tower, and every extra layer of padding doubles
-- it.  The telescope here is FLAT, so the wrap summand that repaired
-- the previous form is nought and the two exponents face each other
-- with nothing in between.
--
-- WHAT THIS DOES NOT KILL.  Nothing about the per-VALUE price: the
-- value fit reads the arrival's own tower, which is exactly the
-- quantity the substitution moved, so it tracks the growth this
-- refutes.  What is dead is reading the entry grant off the payload.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Sight-All-Stream-Dup where

open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; InstEmit)
open import Rx.Exp
  using (Ctx; Closed; Fn; Val; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ; syncSizeᵉ;
  syncSizeᵛ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; Stream; root; _↠_; thru-outer; mergeAllᵒ;
         subscribeE; splitEvents; mintNode; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; allFresh; slotWrapSum)
open import Verify-Budget-Sufficient.Depth-Sighted using (StreamFit)

-- a FLAT slot, so the wrap summand is nought and the two towers face
-- each other with nothing in between
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

-- the emitted observable, padded so its own sync size can be dialled
pad : ℕ → Closed Γₛ natᵗ
pad zero    = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))
pad (suc j) = mergeAllᵉ nothing (ofᵉ (strmᵗ (pad j) ∷ []))

-- the payload MAPS, and its function names its argument TWICE, so one
-- application doubles the sync size of what comes out while the grant
-- reads the payload's own
dupO : Fn Γₛ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dupO = strmᵗ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ []))

b : ℕ → Closed Γₛ (obs (obs natᵗ))
b j = mapᵉ dupO (ofᵉ (strmᵗ (pad j) ∷ []))

κ : Path Γₛ (obs natᵗ) (obs natᵗ)
κ = root

nidOf : ℕ → _
nidOf j = proj₁ (mintNode sched)

runOf : ℕ → _
runOf j =
  subscribeE gas (b j) (thru-outer mergeAllᵒ (nidOf j) ↠ κ) 0 0
    (proj₂ (mintNode sched))
    (installNode (nidOf j) (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

G : ℕ → ℕ
G j = 2 ^ syncSizeᵉ (b j) * (pathNestD κ + suc (nestDᵉ (b j)))
    + 1 * slotWrapSum sl

-- the value the run actually emits, named so the numbers below are
-- read off the evaluator and not off a hand-built term
oDup : ℕ → Val Γₛ (obs (obs natᵗ))
oDup j = ofᵉ (strmᵗ (pad j) ∷ strmᵗ (pad j) ∷ [])

lhs : ℕ → ℕ
lhs j = 2 ^ syncSizeᵛ (obs (obs natᵗ)) (oDup j)
          * (pathNestD κ + nestDᵛ (obs (obs natᵗ)) (oDup j))

-- the readings, packed so one build returns every figure
figs : ℕ
figs = syncSizeᵉ (b 0) + 100 * syncSizeᵛ (obs (obs natᵗ)) (oDup 0)
     + 10000 * nestDᵉ (b 0)
     + 1000000 * nestDᵛ (obs (obs natᵗ)) (oDup 0)
     + 100000000 * slotWrapSum sl

figs≡ : figs ≡ 1011816
figs≡ = refl

sides : ℕ
sides = lhs 0 + 10000000000 * G 0

sides≡ : sides ≡ 1310720000262144
sides≡ = refl

sight-all-stream-dup-absurd : StreamFit 1 sl (G 0) κ (proj₁ (runOf 0)) → ⊥
sight-all-stream-dup-absurd fit = ≤⇒≤ᵇ (proj₂ (proj₁ (proj₁ fit)))

----------------------------------------------------------------------
-- AND NESTING THE DUPLICATION COMPOUNDS, which is what says the repair
-- is not a bigger constant.  Each layer costs the payload a fixed
-- number of constructors and DOUBLES what comes out, so the emitted
-- value's size is exponential in a payload that grows linearly
----------------------------------------------------------------------

-- a duplicating map at the inner type, so the layers stack
dupN : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dupN = strmᵗ (mergeAllᵉ nothing
         (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

srcN : ℕ → Closed Γₛ (obs natᵗ)
srcN zero    = ofᵉ (strmᵗ (pad 0) ∷ [])
srcN (suc k) = mapᵉ dupN (srcN k)

bN : ℕ → Closed Γₛ (obs (obs natᵗ))
bN k = mapᵉ dupO (srcN k)

-- the payload's own size, layer by layer: linear
payload : ℕ
payload = syncSizeᵉ (bN 0) + 1000 * syncSizeᵉ (bN 1)
        + 1000000 * syncSizeᵉ (bN 2) + 1000000000 * syncSizeᵉ (bN 3)

payload≡ : payload ≡ 37030023016
payload≡ = refl

runN : ℕ → _
runN k =
  subscribeE gas (bN k) (thru-outer mergeAllᵒ (nidOf k) ↠ κ) 0 0
    (proj₂ (mintNode sched))
    (installNode (nidOf k) (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

Gn : ℕ → ℕ
Gn k = 2 ^ syncSizeᵉ (bN k) * (pathNestD κ + suc (nestDᵉ (bN k)))
     + 1 * slotWrapSum sl

-- the values the burst actually carries, so the demand below is read
-- off the evaluator rather than off a term written to match it
valsOf : Stream Γₛ (obs (obs natᵗ)) → List (Val Γₛ (obs (obs natᵗ)))
valsOf []       = []
valsOf (em ∷ _) = proj₁ (splitEvents {A = Val Γₛ (obs (obs natᵗ))}
                           (InstEmit.events em))

-- the EXPONENTS, layer by layer: the grant's is linear above, this one
-- doubles
emitted : ℕ
emitted = syncOf 0 + 1000 * syncOf 1 + 1000000 * syncOf 2
        + 1000000000 * syncOf 3
  where
  syncOf : ℕ → ℕ
  syncOf k with valsOf (proj₁ (runN k))
  ... | []    = 0
  ... | o ∷ _ = syncSizeᵛ (obs (obs natᵗ)) o

emitted≡ : emitted ≡ 186090042018
emitted≡ = refl

sight-all-stream-nest-absurd :
  StreamFit 1 sl (Gn 2) κ (proj₁ (runN 2)) → ⊥
sight-all-stream-nest-absurd fit = ≤⇒≤ᵇ (proj₂ (proj₁ (proj₁ fit)))
