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
-- charge reads two, three, four, five while the payload's sync size
-- reads sixteen, twenty-three, thirty, thirty-seven -- and that figure
-- is the grant's exponent scaled by the program's own size, so the
-- grant is a tower over something linear in the layer while the charge
-- is linear in it.  The margin is not a scale a deeper family closes.
--
-- THE PATH IS THE ONE THE PAYLOAD IS SUBSCRIBED UNDER, which is the
-- frame the head has just pushed rather than the head's own outer
-- path, so the charge here counts that frame and the rows are the
-- statement as the leaf makes it rather than as its consumer spends
-- it.
--
-- NOT COVERED: the two heads other than `mergeAllᵒ`; any outer path
-- other than `root`, so the telescope summand is nought at every row
-- here; a telescope of more than one slot; a burst width above nought,
-- which the grant is monotone in and so weakens out of these rows; and
-- an arrival that is a slot REFERENCE, which is the shape the wrap
-- summand exists for and which the consume's own probe carries.
--
-- TARGET: subscribeE-fit @d8da3b
-- ══════════════════════════════════════════════════════════════════
module Probed.Sight-All-Stream where

open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; m≤m+n)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; InstEmit)
open import Rx.Exp
  using (Ctx; Closed; Fn; Val; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; syncSizeᵉ; sizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ;
         subscribeE; splitEvents; mintNode; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Cap using (nestB-base)
open import Verify-Budget-Sufficient.Nest-Store
  using (pathNestD; allFresh; slotWrapSum; nestUnit; fitB)
open import Verify-Budget-Sufficient.Sighted-Fit using (StreamFitG; subscribeE-fit)
open import Probed.Apparatus using (Confirms)

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

κ′ : Path Γₛ (obs (obs natᵗ)) (obs natᵗ)
κ′ = thru-outer mergeAllᵒ nid ↠ κ

runOf : ℕ → _
runOf j =
  subscribeE gas (b j) κ′ 0 0
    (proj₂ (mintNode sched))
    (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

-- THE GRANT AS THE STATEMENT NOW READS IT, written out because
-- `nestB` is sealed for the reason every caps family is.  The width is
-- read at ZERO -- the smallest number the grant admits, so the family
-- is monotone out of these rows and a row holding here holds at every
-- legal `descW` bound.  The size base is the run's own, which is what
-- the statement takes rather than a choice made here.
U : ℕ
U = nestUnit prog sl

fac : ℕ → ℕ
fac m = ((2 ^ sizeᵉ prog) ^ suc 0) ^ m

wrapB : ℕ
wrapB = fac (syncSizeᵉ flat) * (nestDᵉ flat + suc (syncSizeᵉ flat) * U)

G : ℕ → ℕ
G j = fac (syncSizeᵉ (b j))
        * ((pathNestD κ′ + nestDᵉ (b j)) + suc (syncSizeᵉ (b j)) * U)
    + 1 * wrapB

-- LOAD-BEARING: the whole fold, inhabited, at the duplicating payload
fitDup : StreamFitG 1 sl (G 0) (pathNestD κ′) (obs (obs natᵗ)) (proj₁ (runOf 0))
fitDup = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

oDup : ℕ → Val Γₛ (obs (obs natᵗ))
oDup j = ofᵉ (strmᵗ (pad j) ∷ strmᵗ (pad j) ∷ [])

-- ── the sides, so the row is read as a margin and not as a green ────
sides : ℕ
sides = demand 0 + 1000000 * G 0
  where
  demand : ℕ → ℕ
  demand j = pathNestD κ′ + nestDᵛ (obs (obs natᵗ)) (oDup j) + 1 * slotWrapSum sl

sides≡ : sides ≡ 1505335087771022414758371393536000002
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
  subscribeE gas (bN k) κ′ 0 0
    (proj₂ (mintNode sched))
    (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st)

Gn : ℕ → ℕ
Gn k = fac (syncSizeᵉ (bN k))
         * ((pathNestD κ′ + nestDᵉ (bN k)) + suc (syncSizeᵉ (bN k)) * U)
     + 1 * wrapB

-- LOAD-BEARING: three layers up, where the arrival's size is a tower
fitN₁ : StreamFitG 1 sl (Gn 1) (pathNestD κ′) (obs (obs natᵗ)) (proj₁ (runN 1))
fitN₁ = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

fitN₂ : StreamFitG 1 sl (Gn 2) (pathNestD κ′) (obs (obs natᵗ)) (proj₁ (runN 2))
fitN₂ = ((tt , ≤ᵇ⇒≤ _ _ tt) , tt) , tt

fitN₃ : StreamFitG 1 sl (Gn 3) (pathNestD κ′) (obs (obs natᵗ)) (proj₁ (runN 3))
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
  ...   | o ∷ _  = pathNestD κ′ + nestDᵛ (obs (obs natᵗ)) o + 1 * slotWrapSum sl

layers≡ : layers ≡ 5040302
layers≡ = refl

exps : ℕ
exps = syncSizeᵉ (bN 0) + 100 * syncSizeᵉ (bN 1)
     + 10000 * syncSizeᵉ (bN 2) + 1000000 * syncSizeᵉ (bN 3)

exps≡ : exps ≡ 37302316
exps≡ = refl

----------------------------------------------------------------------
-- THE TIE, at the same two families the rows above read.  Its type is
-- the statement APPLIED at this file's own point rather than the grant
-- written out by hand, so a restatement of the postulate changes what
-- the row asserts instead of leaving a hand-copy of the old grant
-- standing here green.
--
-- AND ITS BOUND IS TIGHTER THAN THE ONE ABOVE, which is what makes it
-- worth having beside those rows rather than instead of them.  `nestB`
-- is sealed, so the grant cannot be computed here; what CAN be
-- computed is its FLOOR -- the depth argument it is built over -- and
-- the rows below spend only that, widening to the real grant by the
-- family's own base lemma.  So each row asks whether the emitted
-- value's depth stays under the ARRIVAL's, with the wrap summand
-- charged, and it fails the moment a step duplicates past it.  The
-- rows above read the margin against the whole tower; these read it
-- against the tower's first term.
--
-- THE WIDTH IS TAKEN AT NOUGHT, the smallest the grant admits, and
-- both premises are left STANDING and unread -- the width premise is
-- what would have to be discharged to pin `descW`, which is sealed, so
-- reading it would be reporting on the seal rather than on the fit.
----------------------------------------------------------------------

-- the floor route, stated once: the grant's depth argument is a lower
-- bound on the grant, so anything under the depth is under the grant
fitFloor : ∀ (a : Closed Γₛ (obs (obs natᵗ))) (d : ℕ) →
  d ≤ pathNestD κ′ + nestDᵉ a →
  d ≤ fitB prog sl 1 0 (pathNestD κ′ + nestDᵉ a) (syncSizeᵉ a)
fitFloor a d h =
  ≤-trans h
    (≤-trans (nestB-base (sizeᵉ prog) 0 (nestUnit prog sl)
                (pathNestD κ′ + nestDᵉ a) (syncSizeᵉ a))
             (m≤m+n _ _))

tieDup : Confirms
  (subscribeE-fit gas 1 0 (b 0) κ′ 0 0
     (proj₂ (mintNode sched))
     (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st))
tieDup _ _ = ((tt , fitFloor (b 0) _ (≤ᵇ⇒≤ _ _ tt)) , tt) , tt

tieN₃ : Confirms
  (subscribeE-fit gas 1 0 (bN 3) κ′ 0 0
     (proj₂ (mintNode sched))
     (installNode nid (allFresh (obs natᵗ) mergeAllᵒ nothing) st))
tieN₃ _ _ = ((tt , fitFloor (bN 3) _ (≤ᵇ⇒≤ _ _ tt)) , tt) , tt
