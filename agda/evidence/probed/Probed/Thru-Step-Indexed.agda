-- ══════════════════════════════════════════════════════════════════
-- THE CONSUME STEP AT TWO GRANT INDICES, instantiated at the very
-- witness that killed the one-index form -- so the repair is measured
-- against the thing it was made for rather than against fresh programs
-- chosen to suit it.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT IS LOAD-BEARING HERE IS NOT THE DOUBLING.  The delivered figure
-- is twice the arrival, and one step of the key buys a factor of
-- `(2 ^ S) ^ suc W`, which at any cap this statement admits is already
-- far above two -- so every row reading the VALUE conjunct is
-- DEGENERATE on the exponent and could not have failed.  That is worth
-- pinning exactly once, because it is the finding: the axis the
-- one-index form died on cannot reach the indexed one at all.
--
-- AND THE VALUE CONJUNCT IS NOT REACHABLE BY THIS AXIS AT ALL, which
-- the tight rows at the bottom pin as arithmetic rather than as a
-- failed attempt: the cap bounds the arrival and the key's factor is
-- two to that cap, so a step delivering twice its arrival fits at
-- every program.  AND IT IS NOT THE DRAIN EITHER, which is the reading
-- this file used to carry: every arm of `thruConsume` subscribes the
-- arrival or parks it, and no arm reads a queue back, so the parked
-- figure is never a delivery.  The region left is the arrival's own
-- term, where nesting a duplicating substitution to depth `d` doubles
-- once per level against a `syncSizeᵛ` that grows by a constant per
-- level.  The rows below do not reach it.
--
-- TARGET: thruFit-arr-merge @7e2ef1
-- TARGET: thruFit-arr-switch @a5405f
-- TARGET: thruFit-arr-exhaust @a1c296
-- REFUTED: Refuted.Thru-Step-Caps
-- ══════════════════════════════════════════════════════════════════
module Probed.Thru-Step-Indexed where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤ᵇ_; _^_; _*_; _+_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤ᵇ⇒≤; m≤m⊔n; ⊔-mono-≤)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; varᵗ; caseᵗ; inlᵗ; syncSizeᵛ;
         switchAllᵉ; exhaustAllᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵉ)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; thru-outer;
         mergeAllᵒ; switchᵒ; exhaustᵒ; installNode; mergeAll-st; switch-st;
         exhaust-st; thruConsume)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD; arrD-mono; arrDW-key)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; nestCapsOK?; thruFit-arr-merge; thruFit-arr-switch;
         thruFit-arr-exhaust)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Probed.Apparatus using (Confirms)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the duplicating step, verbatim from the witness that refuted the
-- one-index form: the payload lands in the map's step function and in
-- the source it maps over
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

E : ℕ → Val Γ₂ (obs natᵗ)
E zero    = ofᵉ (nat̂ 0 ∷ [])
E (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (E k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

arr : ℕ → Val Γ₂ (obs (obs natᵗ))
arr k = mapᵉ dup (ofᵉ (strmᵗ (E k) ∷ []))

κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

stM stS stX : EvalSt prog
stM = installNode 7 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
                 (st-init prog)
stS = installNode 8 (switch-st nothing false) (st-init prog)
stX = installNode 9 (exhaust-st false false) (st-init prog)

cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 6))
           (pWᵛ 2 slots (obs (obs natᵗ)) (arr 6)) 0

-- the grant, written out because `nestB` is sealed, at `W = 0` -- the
-- smallest the statement can be read at, and below the arr-keyed
-- grant these rows also bear on, whose key the width premise
-- multiplies by `suc W`
G : ℕ → ℕ → ℕ
G B m = (2 ^ Caps.cSize cap) ^ m * (B + suc m * nestUnit prog slots)

-- ── the value conjunct, and why it is degenerate ──────────────────

arrival : ℕ
arrival = nestDᵛ (obs (obs natᵗ)) (arr 6)

deliveredM deliveredS deliveredX : ℕ
deliveredM = nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stM))
deliveredS = nestDᵛˢ (proj₁ (thruConsume gasBig switchᵒ 8 κ 0 0 (arr 6) sched₀ stS))
deliveredX = nestDᵛˢ (proj₁ (thruConsume gasBig exhaustᵒ 9 κ 0 0 (arr 6) sched₀ stX))

-- NON-VACUITY: a delivered reading over an empty burst measures nothing
burstLen : ℕ
burstLen = length (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 6) sched₀ stM))

burstLen≡1 : burstLen ≡ 1
burstLen≡1 = refl

figures : ℕ
figures = arrival + 100 * deliveredM + 10000 * deliveredS + 1000000 * deliveredX

figures≡ : figures ≡ 12121206
figures≡ = refl

-- the hypothesis at the TIGHTEST base the statement's own premise
-- admits: `B` chosen so the incoming grant at key zero is exactly the
-- arrival, so nothing is given away on the way in
Bmin : ℕ
Bmin = arrival

hypAtZero : (arrival ≤ᵇ G Bmin 0) ≡ true
hypAtZero = refl

-- DEGENERATE, and pinned as such: one step of the key clears a doubling
-- with room to spare that no arrival can consume, the factor being a
-- power of the same cap the arrival's own size is bounded by
valAtOne : ((deliveredM ≤ᵇ G Bmin 1) ≡ true)
         × ((deliveredS ≤ᵇ G Bmin 1) ≡ true)
         × ((deliveredX ≤ᵇ G Bmin 1) ≡ true)
valAtOne = refl , refl , refl

-- and the margin, so the degeneracy is a number rather than a claim
marginM : ℕ
marginM = G Bmin 1

marginM≡ : marginM ≡ 21990232555520
marginM≡ = refl

-- ── the value conjunct where the two sides are COMPARABLE ─────────

-- the rows above are degenerate for a reason that is about the CAP and
-- not about the program's depth: the key's factor is a power of
-- `cSize`, `cSize` is read off the arrival's own size, and the step
-- only doubles.  So the way to bring the two sides together is a
-- SHALLOWER arrival, not a deeper program -- which is the cheap
-- direction, since the harness cost is geometric in depth
capT : Caps
capT = caps (syncSizeᵛ (obs (obs natᵗ)) (arr 1))
            (pWᵛ 2 slots (obs (obs natᵗ)) (arr 1)) 0

GT : ℕ → ℕ → ℕ
GT B m = (2 ^ Caps.cSize capT) ^ m * (B + suc m * nestUnit prog slots)

arrivalT deliveredT : ℕ
arrivalT = nestDᵛ (obs (obs natᵗ)) (arr 1)
deliveredT =
  nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr 1) sched₀ stM))

tightFigures : ℕ
tightFigures = arrivalT + 100 * deliveredT + 10000 * Caps.cSize capT
             + 1000000 * nestUnit prog slots

tightFigures≡ : tightFigures ≡ 2210201
tightFigures≡ = refl

-- the conjunct itself at those caps, DEGENERATE like every other row
-- on this axis and kept because it makes the gap a number: two against
-- ten million, at the shallowest arrival there is
valTight : (deliveredT ≤ᵇ GT arrivalT 1) ≡ true
valTight = refl

-- AND THE AXIS CANNOT REFUTE, WHICH IS THE FINDING RATHER THAN THE
-- FAILED ATTEMPT.  The reading above is arrival 1, delivered 2, unit 2
-- and `cSize` TWENTY-ONE -- at the shallowest arrival the harness has.
-- `cSize` is the arrival's `syncSizeᵛ`, which measures the TERM, and a
-- step that duplicates needs a term big enough to do it, so shrinking
-- the arrival's depth does not shrink the cap.
--
-- Worse for the sweep, and this is what closes it: the same `cSize`
-- bounds the arrival, through the very `nestValOK?` premise the
-- statement carries.  So for any step delivering at most twice its
-- arrival, the conjunct at one key reads `2 * arrival ≤ (2 ^ cSize) * _`
-- with `arrival ≤ cSize` -- and `2 * k ≤ 2 ^ k` at every `k`, with
-- equality only at one and two.  No program refutes that, so no sweep
-- over arrivals is worth running: the axis moves the bound side faster
-- than the measure side by construction.
--
-- WHERE THE RISK ACTUALLY LIVES is a step whose delivery is NOT linear
-- in its arrival, and the rows below reach that: nesting the
-- duplicating step compounds the delivery per level while the arrival
-- grows by one.

-- ── THE NESTED DUPLICATOR, which is the axis the receipt names ────

-- `arr` applies the substituting step ONCE; this nests it, so the
-- arrival's delivery compounds per level instead of doubling once
Dn : ℕ → Val Γ₂ (obs (obs natᵗ))
Dn zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
               (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
Dn (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (Dn k) ∷ [])))

capN : ℕ → Caps
capN k = caps (syncSizeᵛ (obs (obs natᵗ)) (Dn k))
              (pWᵛ 2 slots (obs (obs natᵗ)) (Dn k)) 0

GN : ℕ → ℕ → ℕ → ℕ
GN k B m = (2 ^ Caps.cSize (capN k)) ^ m * (B + suc m * nestUnit prog slots)

arrN delN : ℕ → ℕ
arrN k = nestDᵛ (obs (obs natᵗ)) (Dn k)
delN k = nestDᵛˢ (proj₁ (thruConsume gasBig mergeAllᵒ 7 κ 0 0 (Dn k) sched₀ stM))

nestedFigures : ℕ
nestedFigures = arrN 1 + 10 * delN 1 + 100 * arrN 2 + 1000 * delN 2
              + 10000 * arrN 3 + 100000 * delN 3

nestedFigures≡ : nestedFigures ≡ 844322
nestedFigures≡ = refl

premN : Bool × Bool
premN = nestValOK? (capN 3) (obs (obs natᵗ)) (Dn 3)
      , nestCapsOK? (capN 3) sched₀ stM

premN≡ : premN ≡ (true , true)
premN≡ = refl

fitN1 : (delN 1 ≤ᵇ GN 1 (arrN 1) 1) ≡ true
fitN1 = refl

fitN2 : (delN 2 ≤ᵇ GN 2 (arrN 2) 1) ≡ true
fitN2 = refl

fitN3 : (delN 3 ≤ᵇ GN 3 (arrN 3) 1) ≡ true
fitN3 = refl

-- ── THE RESIDUE THE SUBSCRIBING ARM OWES, MEASURED ────────────────

-- what one step of the key actually affords is `2 ^ k` for a `k`
-- STRICTLY under the cap -- that is `nestB-frame`, and it is the only
-- shape a caller reading `m′` at `suc m` can absorb.  So the question
-- the leaf turns on is whether the delivery fits a base-TWO frame
-- charge at the largest such `k`, rather than the grant's own
-- per-level factor.  These rows read it at the nested duplicator,
-- which is the fastest-growing delivery this harness has.
--
-- AND THEY ARE DEGENERATE, WHICH IS THE MEASUREMENT AND NOT AN
-- APOLOGY: the caps read twenty-five, forty and fifty-five over the
-- three levels while the delivery reads two, four and eight, so the
-- bound side gains fifteen doublings per level and the measure side
-- one.  What that says about the candidate is the useful part -- a
-- duplicating step spends fifteen units of sync size to buy one
-- doubling, so the frame charge is nowhere near tight and the
-- statement has room to be true.  What would refute it is a term
-- whose delivery doubles per UNIT of sync size rather than per
-- nesting level, and no head in this language does that
frameFit : ℕ → ℕ
frameFit k = 2 ^ pred (Caps.cSize (capN k)) * (arrN k + nestUnit prog slots)

residueFigures : ℕ
residueFigures = Caps.cSize (capN 1) + 100 * Caps.cSize (capN 2)
               + 10000 * Caps.cSize (capN 3)

residueFigures≡ : residueFigures ≡ 554025
residueFigures≡ = refl

resN1 : (delN 1 ≤ᵇ frameFit 1) ≡ true
resN1 = refl

resN2 : (delN 2 ≤ᵇ frameFit 2) ≡ true
resN2 = refl

resN3 : (delN 3 ≤ᵇ frameFit 3) ≡ true
resN3 = refl

-- ══════════════════════════════════════════════════════════════════
-- AND THE TIE TO THE THREE STATEMENTS, AT THE SHALLOWEST ARRIVAL AND
-- NOT AT THE NESTED ONE THE ROWS ABOVE READ.  Every row above is this
-- file's own arithmetic run over figures the evaluator produced;
-- nothing in it is held to the statements as they read.  The rows
-- below are: Agda generates their types from the postulates, so this
-- file supplies only the point.
--
-- WHY THE POINT IS THE SHALLOW ONE, and it is a coverage boundary
-- rather than a shortfall of effort.  The third conjunct of the fit is
-- quantified over a NODE ID, so it compares two table lookups at a
-- variable.  Where the consumed arrival leaves the table
-- definitionally untouched both sides are the same stuck term and the
-- conjunct is `m ≤ m ⊔ G`; where the arrival SUBSCRIBES -- which every
-- arrival carrying an operator does, and which is exactly what the
-- nested duplicator is for -- the two lookups differ at a concrete id
-- the quantifier cannot reach, and no row can be written at all.  So
-- the deep readings above stay readings, and what is tied is the
-- boundary they are measured from.
--
-- THE ROWS ARE LOAD-BEARING ON THE VALUE CONJUNCT AND DEGENERATE ON
-- THE TWO STORE ONES.  The arrival delivers a nesting of one against a
-- grant that is a power of two in the key, so the first conjunct is a
-- comparison that computes and could have failed; the store pair is
-- `m ≤ m ⊔ G` by construction of the point.  The sealed width factor
-- is never read: `suc W * key` is at least `key` whatever `descW`
-- says, so the computable grant transports by monotonicity.
-- ══════════════════════════════════════════════════════════════════

tsB : Closed Γ₂ (obs (obs natᵗ))
tsB = ofᵉ (strmᵗ (Dn 0) ∷ [])

tsC : Caps
tsC = caps 999 999 999

tsU : ℕ
tsU = nestUnit prog slots

tsBDm tsKeym tsWm : ℕ
tsBDm  = nestDᵉ (mergeAllᵉ nothing tsB)
tsKeym = closSizeᵉ (slotClos slots) (mergeAllᵉ nothing tsB)
tsWm   = descW gasBig (mergeAllᵉ nothing tsB) κ 0 0 sched₀ (st-init prog)

tsGrantM : arrD tsU tsBDm tsKeym ≤ arrD tsU tsBDm (suc tsWm * tsKeym)
tsGrantM = arrD-mono tsU tsBDm tsKeym (suc tsWm * tsKeym)
             (arrDW-key tsWm tsKeym)

tsRowM : Confirms
  (thruFit-arr-merge tsC slots tsBDm tsWm gasBig
     nothing tsB κ 0 0 sched₀ (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tsRowM =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tsGrantM
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tsGrantM)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt

tsBDs tsKeys tsWs : ℕ
tsBDs  = nestDᵉ (switchAllᵉ tsB)
tsKeys = closSizeᵉ (slotClos slots) (switchAllᵉ tsB)
tsWs   = descW gasBig (switchAllᵉ tsB) κ 0 0 sched₀ (st-init prog)

tsGrantS : arrD tsU tsBDs tsKeys ≤ arrD tsU tsBDs (suc tsWs * tsKeys)
tsGrantS = arrD-mono tsU tsBDs tsKeys (suc tsWs * tsKeys)
             (arrDW-key tsWs tsKeys)

tsRowS : Confirms
  (thruFit-arr-switch tsC slots tsBDs tsWs gasBig
     tsB κ 0 0 sched₀ (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tsRowS =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tsGrantS
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tsGrantS)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt

tsBDx tsKeyx tsWx : ℕ
tsBDx  = nestDᵉ (exhaustAllᵉ tsB)
tsKeyx = closSizeᵉ (slotClos slots) (exhaustAllᵉ tsB)
tsWx   = descW gasBig (exhaustAllᵉ tsB) κ 0 0 sched₀ (st-init prog)

tsGrantX : arrD tsU tsBDx tsKeyx ≤ arrD tsU tsBDx (suc tsWx * tsKeyx)
tsGrantX = arrD-mono tsU tsBDx tsKeyx (suc tsWx * tsKeyx)
             (arrDW-key tsWx tsKeyx)

tsRowX : Confirms
  (thruFit-arr-exhaust tsC slots tsBDx tsWx gasBig
     tsB κ 0 0 sched₀ (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tsRowX =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tsGrantX
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tsGrantX)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt
