-- ══════════════════════════════════════════════════════════════════
-- THE ARR KEY AT A SUBSTITUTING SLOT, which is the one region the
-- indexed receipt names as not covered: there the key is read THROUGH
-- the telescope rather than off the arriving term, and a slot
-- reference measures one whatever it names.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT IS LOAD-BEARING, and it is the axis that killed the cap-keyed
-- sibling rather than a fresh one: the same arrival, the same slot and
-- the same delivery, read at THIS key instead of at a cap the
-- reference pins.  A slot reference has size one and depth zero, so
-- the cap-keyed grant stood still at four while the definition behind
-- the slot doubled per layer -- eight at three layers, and the gap
-- unbounded.  The key here is `closSizeᵉ` through `slotClos`, which
-- resolves the telescope, so it reads fifty-six at the same witness
-- and the grant is a power of two in it.  The rows are the value
-- conjunct at each of four layers, at the smallest width the statement
-- admits, `suc W` being a factor ON the key.
--
-- AND THEY ARE DEGENERATE, WHICH IS THE MEASUREMENT.  The key gains
-- about fifteen per layer and the delivery doubles, so the bound side
-- gains fifteen doublings where the measure side gains one, and every
-- deeper witness widens the margin.  That is the finding: the axis the
-- cap-keyed form died on cannot reach this one at all, because the
-- quantity it moved is now read through the substitution it moves.
--
-- NOT COVERED: a telescope whose written size does NOT grow with the
-- depth it substitutes -- the key is a term size, so a definition that
-- deepens without lengthening would hold it still; no head in this
-- language does that, and none is instantiated here.  Nor the two
-- STORE conjuncts, which are read against `nodesMax st ⊔ G` at the
-- same grant and so are weaker than the value one already read.
--
-- TARGET: thruFit-arr-merge @7e2ef1
-- TARGET: thruFit-arr-switch @a5405f
-- TARGET: thruFit-arr-exhaust @a1c296
-- ══════════════════════════════════════════════════════════════════
module Probed.Thru-Arr-Slot where

open import Data.Bool using (true; false; T)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; input; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ; switchᵒ;
         exhaustᵒ; mergeAll-st; switch-st; exhaust-st; thruConsume;
         installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gas : Gas
gas = gasPad 400 g0

prog : Closed Γₛ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

sched : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Sched Γₛ
sched d ok = sched-init prog (sl d ok)

κ : Path Γₛ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

stM : EvalSt prog
stM = installNode 0 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) (st-init prog)

stS : EvalSt prog
stS = installNode 0 (switch-st nothing false) (st-init prog)

stX : EvalSt prog
stX = installNode 0 (exhaust-st false false) (st-init prog)

arrTerm : Val Γₛ (obs (obs natᵗ))
arrTerm = input fzero

delM delS delX : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
delM d ok =
  nestDᵛˢ (proj₁ (thruConsume gas mergeAllᵒ 0 κ 0 0 arrTerm (sched d ok) stM))
delS d ok =
  nestDᵛˢ (proj₁ (thruConsume gas switchᵒ 0 κ 0 0 arrTerm (sched d ok) stS))
delX d ok =
  nestDᵛˢ (proj₁ (thruConsume gas exhaustᵒ 0 κ 0 0 arrTerm (sched d ok) stX))

-- NON-VACUITY: a delivered reading over an empty burst measures nothing
burst : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
burst d ok =
  length (proj₁ (thruConsume gas mergeAllᵒ 0 κ 0 0 arrTerm (sched d ok) stM))

burst≡ : burst (dDup 0) tt + 10 * burst (dDup 1) tt
       + 100 * burst (dDup 2) tt + 1000 * burst (dDup 3) tt ≡ 1111
burst≡ = refl

-- the key, read THROUGH the telescope: the reference measures one, the
-- definition behind it does not, and this is what reads it
key : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
key d ok = suc 0 * closSizeᵉ (slotClos (sl d ok)) arrTerm

-- the arr grant at the smallest width the statement admits, with the
-- depth base at the arrival's own -- zero, a reference carrying none
G : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
G d ok = arrD (nestUnit prog (sl d ok)) (nestDᵉ arrTerm) (key d ok)

keys≡ : key (dDup 0) tt + 100 * key (dDup 1) tt
      + 10000 * key (dDup 2) tt + 1000000 * key (dDup 3) tt ≡ 56412611
keys≡ = refl

delivered≡ : delM (dDup 0) tt + 10 * delM (dDup 1) tt
           + 100 * delM (dDup 2) tt + 1000 * delM (dDup 3) tt ≡ 8421
delivered≡ = refl

unit≡ : nestUnit prog (sl (dDup 0) tt) + 10 * nestUnit prog (sl (dDup 3) tt) ≡ 52
unit≡ = refl

-- the value conjunct, at four layers and all three operators
fitM : ((delM (dDup 0) tt ≤ᵇ G (dDup 0) tt) ≡ true)
     × ((delM (dDup 1) tt ≤ᵇ G (dDup 1) tt) ≡ true)
     × ((delM (dDup 2) tt ≤ᵇ G (dDup 2) tt) ≡ true)
     × ((delM (dDup 3) tt ≤ᵇ G (dDup 3) tt) ≡ true)
fitM = refl , refl , refl , refl

fitS : ((delS (dDup 1) tt ≤ᵇ G (dDup 1) tt) ≡ true)
     × ((delS (dDup 3) tt ≤ᵇ G (dDup 3) tt) ≡ true)
fitS = refl , refl

fitX : ((delX (dDup 1) tt ≤ᵇ G (dDup 1) tt) ≡ true)
     × ((delX (dDup 3) tt ≤ᵇ G (dDup 3) tt) ≡ true)
fitX = refl , refl

-- the margin as a number, so the degeneracy is measured and not claimed
margin₃≡ : G (dDup 3) tt ≡ 180143985094819840
margin₃≡ = refl
