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
-- AND THE TIE SITS AT A SHALLOWER POINT THAN THE ROWS ABOVE, which is
-- a property of the STATEMENT rather than of what is interesting here.
-- Its third conjunct quantifies over every `NodeId`, and the two
-- lookups it compares agree definitionally only where the consumed
-- arrival mints no node -- any arrival whose term carries an operator
-- does mint, and both sides then go stuck at a concrete id the
-- quantifier cannot reach.  So the tie takes a plain `of` whose
-- emitted value is itself an observable: nothing is minted, yet the
-- delivery still carries positive nesting, so the VALUE conjunct is a
-- comparison that computes and could have failed.  `tieArr≡` reads it
-- out -- one emit, one arrival, delivered nesting one.
--
-- AND THE SEALED WIDTH IS NEVER READ, because it sits on the LARGE
-- side of the grant.  `descW` is `abstract`, so `suc W * key` reduces
-- at no input; but `arrDW-key` gives `key ≤ suc W * key` whatever `W`
-- is, so `arrD-mono` transports the computable grant to the
-- statement's own.  The mirror of the small-side case, where a seal
-- blocks the row outright.
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
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤ᵇ⇒≤; m≤m⊔n; ⊔-mono-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; input; inputsBelowᵉ;
         switchAllᵉ; exhaustAllᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ; switchᵒ;
         exhaustᵒ; mergeAll-st; switch-st; exhaust-st; thruConsume;
         installNode; sched-init; st-init;
         NodeId; mintNode; subscribeE; splitBurst; thruWalk)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD; arrD-mono; arrDW-key)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; thruFit-arr-merge; thruFit-arr-switch; thruFit-arr-exhaust)
open import Probed.Apparatus using (Confirms)

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

TIEc : Caps
TIEc = caps 999 999 999

tieSl : Slots Γₛ
tieSl = sl (dDup 0) tt

tieSch : Sched Γₛ
tieSch = sched-init prog tieSl

-- the body is chosen so the ONE arrival it hands the walk is the slot
-- reference the rows above measure, so the row's first conjunct is the
-- same delivered reading `delM` reports at the deepest layer
tieB : Closed Γₛ (obs (obs natᵗ))
tieB = ofᵉ (strmᵗ arrTerm ∷ [])

tieW : ℕ
tieW = descW gas (mergeAllᵉ nothing tieB) κ 0 0 tieSch (st-init prog)

tieKey : ℕ
tieKey = closSizeᵉ (slotClos tieSl) (mergeAllᵉ nothing tieB)

tieNid : NodeId
tieNid = proj₁ (mintNode tieSch)

tieSt : EvalSt prog
tieSt = installNode tieNid (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
          (st-init prog)

-- the arrivals the tie's own subscribe hands the walk, and the walk's
-- delivered nesting over exactly them -- which is the LHS of the row's
-- first conjunct, read as a number rather than asserted
tieArr : ℕ × ℕ × ℕ
tieArr =
  let str = proj₁ (subscribeE gas tieB (thru-outer mergeAllᵒ tieNid ↠ κ) 0 0
                     (proj₂ (mintNode tieSch)) tieSt)
      os  = proj₁ (splitBurst {A = Val Γₛ natᵗ} str)
  in length str , length os
   , nestDᵛˢ (proj₁ (thruWalk gas mergeAllᵒ tieNid κ 0 0 os
                       (proj₂ (mintNode tieSch)) tieSt))

-- the grant WITHOUT the sealed width factor, which is the largest
-- bound this file can compute: `descW` is `abstract`, so `suc W * key`
-- reduces at no input, and the row reaches it by monotonicity instead
tieU tieBD : ℕ
tieU  = nestUnit prog tieSl
tieBD = nestDᵉ (mergeAllᵉ nothing tieB)

tieG₁ : ℕ
tieG₁ = arrD tieU tieBD tieKey

tieArr≡ : tieArr ≡ (1 , 1 , 1)
tieArr≡ = refl

-- the sealed width factor is reached by MONOTONICITY and never read:
-- `suc W * key` is at least `key` whatever `W` is, so the computable
-- grant transports to the statement's own without `descW` reducing
tieGrant : tieG₁ ≤ arrD tieU tieBD (suc tieW * tieKey)
tieGrant = arrD-mono tieU tieBD tieKey (suc tieW * tieKey)
             (arrDW-key tieW tieKey)

tieRowM : Confirms
  (thruFit-arr-merge TIEc tieSl tieBD tieW gas
     nothing tieB κ 0 0 tieSch (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tieRowM =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tieGrant
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tieGrant)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt

-- AND THE SAME POINT AT THE OTHER TWO HEADS.  The arrival, the slot and
-- the cap do not move; only the operator the outer path names does, so
-- the three rows separate exactly what the three statements separate.
tieBDs tieKeys tieWs : ℕ
tieBDs  = nestDᵉ (switchAllᵉ tieB)
tieKeys = closSizeᵉ (slotClos tieSl) (switchAllᵉ tieB)
tieWs   = descW gas (switchAllᵉ tieB) κ 0 0 tieSch (st-init prog)

tieGrantS : arrD tieU tieBDs tieKeys ≤ arrD tieU tieBDs (suc tieWs * tieKeys)
tieGrantS = arrD-mono tieU tieBDs tieKeys (suc tieWs * tieKeys)
              (arrDW-key tieWs tieKeys)

tieRowS : Confirms
  (thruFit-arr-switch TIEc tieSl tieBDs tieWs gas
     tieB κ 0 0 tieSch (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tieRowS =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tieGrantS
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tieGrantS)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt

tieBDx tieKeyx tieWx : ℕ
tieBDx  = nestDᵉ (exhaustAllᵉ tieB)
tieKeyx = closSizeᵉ (slotClos tieSl) (exhaustAllᵉ tieB)
tieWx   = descW gas (exhaustAllᵉ tieB) κ 0 0 tieSch (st-init prog)

tieGrantX : arrD tieU tieBDx tieKeyx ≤ arrD tieU tieBDx (suc tieWx * tieKeyx)
tieGrantX = arrD-mono tieU tieBDx tieKeyx (suc tieWx * tieKeyx)
              (arrDW-key tieWx tieKeyx)

tieRowX : Confirms
  (thruFit-arr-exhaust TIEc tieSl tieBDx tieWx gas
     tieB κ 0 0 tieSch (st-init prog)
     refl refl refl refl ≤-refl ≤-refl)
tieRowX =
  ( ≤-trans (≤ᵇ⇒≤ _ _ tt) tieGrantX
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) (⊔-mono-≤ ≤-refl tieGrantX)
  , (λ j → m≤m⊔n _ _)
  , tt ) , tt
