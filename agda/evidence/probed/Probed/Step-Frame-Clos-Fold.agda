-- ══════════════════════════════════════════════════════════════════
-- WHAT ONE STEP BUYS AT THE FOLD, whose second factor comes out of the
-- STORE rather than off the arrival.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT THE QUESTION IS.  A `scan-f` frame rebuilds by applying its
-- template to the ACCUMULATOR, once per value it is handed, each
-- application to the result of the last.  So the arm's bill is not the
-- template's reading times one argument's, as at the map: it is the
-- template's reading COMPOUNDED over the burst, and the only thing
-- bounding the accumulator is the store premise.  The rows price that
-- compounding against what a level buys.
--
-- THE TEMPLATE EMBEDS THE ACCUMULATOR TWICE, which is the worst the
-- fold can do at one application and the shape the evaluator's own
-- demand note is written about: one folded value doubles the reading.
-- The accumulator the frame is entered at is REACHED by running the
-- program rather than written down, so the store premise is met at a
-- state the evaluator can actually be in -- and the base cap REFUSES
-- that state, which is why the rows are read one level up.
--
-- WHAT THE ROWS SAY.  At the level the state's own premise forces,
-- eight folded values overflow and one more level admits them; twelve
-- overflow that and a third admits them.  So the report grows by one
-- per four or five values while the charge available at that level is
-- a power of the size cap in the width -- the fold's doubling is
-- LINEAR in the report and the charge is exponential in the width, and
-- that gap is the finding rather than either figure.
--
-- WHAT IS COVERED IS THE CLOSURE CONJUNCT AT A FLOOR CAP, not the
-- entry recurrence: `sizeCount` is sealed, so no row here computes
-- `capsAt`, and what transfers is the RATIO, since the floor is below
-- the recurrence and the step is monotone.  The width cap is read
-- small on purpose, so the charge is a number rather than a shape.
--
-- AND THE HEAD THE ROWS READ IS THE FOLD, and only it.  Nothing is
-- claimed of a template applied to an arrival, of a wrapper's
-- constructor, or of the values an exiting inner drains out of a
-- queue -- the three other arms rebuild differently and each has its
-- own second factor.
--
-- TARGET: step-frame-clos-scan @d428b5
module Probed.Step-Frame-Clos-Fold where

open import Data.Bool using (true; false; T)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; Fn; Tm; natᵗ; obs; _×ᵗ_; ofᵉ; input;
  scanᵉ; mergeAllᵉ; strmᵗ; varᵗ; fstᵗ; nat̂; sizeᵉ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; scan-f; stepFrame;
  subscribeE; sched-init; st-init; fCharge)
open import Rx.Slots using (Slots; shared; slotsSize)
open import Rx.Slot-Clos using (slotClos; slotsClos)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestClosOK?ᵛ; capsOK?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsCaps?)

------------------------------------------------------------------
-- the slot, whose DEFINITION is a parameter: `m` copies of a literal
------------------------------------------------------------------

Γₛ : Ctx 1
Γₛ = natᵗ ∷ []

copies : ℕ → List (Tm Γₛ [] [] [] natᵗ)
copies zero    = []
copies (suc m) = nat̂ 0 ∷ copies m

defn : ℕ → Closed Γₛ natᵗ
defn m = ofᵉ (copies m)

okc : ∀ m → T (inputsBelowᵉ 0 (defn m))
okc zero    = tt
okc (suc m) = okc m

slots : ℕ → Slots Γₛ
slots m fzero = shared (defn m) {ok = okc m}

------------------------------------------------------------------
-- the fold, whose template embeds the ACCUMULATOR twice, so one
-- folded value doubles what the accumulator reads
------------------------------------------------------------------

acc : Tm Γₛ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (obs natᵗ)
acc = fstᵗ (varᵗ (here refl))

fn : Fn Γₛ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
fn = strmᵗ (mergeAllᵉ nothing (ofᵉ (acc ∷ acc ∷ [])))

seed : Tm Γₛ [] [] [] (obs natᵗ)
seed = strmᵗ (input fzero)

nats : ℕ → List (Tm Γₛ [] [] [] natᵗ)
nats zero    = []
nats (suc k) = nat̂ 0 ∷ nats k

prog : ℕ → Closed Γₛ (obs natᵗ)
prog k = scanᵉ fn seed (ofᵉ (nats k))

gas : Gas
gas = gasPad 400 g0

------------------------------------------------------------------
-- the state is REACHED by running the program, never written down
------------------------------------------------------------------

runOf : (k m : ℕ) → _
runOf k m = subscribeE gas (prog k) root 0 0
              (sched-init (prog k) (slots m)) (st-init (prog k))

schedOf : (k m : ℕ) → Sched Γₛ
schedOf k m = proj₁ (proj₂ (runOf k m))

stOf : (k m : ℕ) → EvalSt (prog k)
stOf k m = proj₂ (proj₂ (runOf k m))

κ : Path Γₛ (obs natᵗ) (obs natᵗ)
κ = root

zeros : ℕ → List (Val Γₛ natᵗ)
zeros zero    = []
zeros (suc ℓ) = 0 ∷ zeros ℓ

outs : (k ℓ m : ℕ) → List (Val Γₛ (obs natᵗ))
outs k ℓ m = proj₁ (stepFrame gas 0 0 (scan-f fn 0) κ (zeros ℓ) false
                      (schedOf k m) (stOf k m))

base : ℕ → ℕ
base m = 2 + sizeᵉ (prog 0) + slotsSize (slots m) + slotsClos (slots m)

cap : ℕ → Caps
cap m = caps (base m) 16 4096

sumClos : ℕ → List (Val Γₛ (obs natᵗ)) → ℕ
sumClos m []       = 0
sumClos m (v ∷ vs) = closSizeᵉ (slotClos (slots m)) v + sumClos m vs

col : (k : ℕ) → ℕ
col k = sumClos 4 (outs k 2 4)

readings : ℕ
readings = col 0 + 1000 * col 1 + 1000000 * col 2 + 1000000000 * col 3

readings≡ : readings ≡ 842410194086
readings≡ = refl

caps≡ : base 4 + 100000 * Caps.cSize (frameStep 1 (cap 4))
      + 10000000000 * Caps.cSize (frameStep 2 (cap 4)) ≡ 894040159600028
caps≡ = refl


capOK₃ : capsOK? (cap 4) (schedOf 3 4) (stOf 3 4) ≡ false
capOK₃ = refl

capOK₃′ : capsOK? (frameStep 1 (cap 4)) (schedOf 3 4) (stOf 3 4) ≡ true
capOK₃′ = refl

flat₃ : all (nestClosOK?ᵛ (frameStep 1 (cap 4)) (slots 4) (obs natᵗ)) (outs 3 8 4) ≡ false
flat₃ = refl

step₃ : all (nestClosOK?ᵛ (frameStep 2 (cap 4)) (slots 4) (obs natᵗ)) (outs 3 8 4) ≡ true
step₃ = refl

flat₁₂ : all (nestClosOK?ᵛ (frameStep 2 (cap 4)) (slots 4) (obs natᵗ)) (outs 3 12 4) ≡ false
flat₁₂ = refl

step₁₂ : all (nestClosOK?ᵛ (frameStep 3 (cap 4)) (slots 4) (obs natᵗ)) (outs 3 12 4) ≡ true
step₁₂ = refl

------------------------------------------------------------------
-- THE OTHER PREMISES THE HEAD CARRIES, at the level the state forces
------------------------------------------------------------------

valsOK : valsCaps? (frameStep 1 (cap 4)) (slots 4) (zeros 12) ≡ true
valsOK = refl

pathOK : pathSz? (Caps.cSize (frameStep 1 (cap 4))) (scan-f fn 0 ↠ κ) ≡ true
pathOK = refl

------------------------------------------------------------------
-- AND THE REPORT FITS THE CHARGE WITH ROOM THAT IS NOT CLOSE
------------------------------------------------------------------

chargeOK : (2 ≤ᵇ fCharge (base 4) 16 1) ≡ true
chargeOK = refl
