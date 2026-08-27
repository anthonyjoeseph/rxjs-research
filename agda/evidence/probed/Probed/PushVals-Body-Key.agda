-- ══════════════════════════════════════════════════════════════════
-- THE WRAP'S PUSH AT THE BODY'S KEY, which is the index the three
-- `pushVals-*` leaves are read at and the one no earlier row reached.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHY A SEPARATE MODULE RATHER THAN MORE ROWS ELSEWHERE.  Every other
-- receipt on these leaves measures the ASSEMBLED head and keys the
-- grant at `syncSizeᵉ` of it.  What the leaf asserts is one level
-- below: the descent is into the BODY, and the key handed to
-- `pushValsOK` is the body's own `syncSizeᵉ`, exactly one smaller.
-- `nestB` is strictly increasing in that argument, so the earlier
-- rows were green against a grant strictly LARGER than this one and
-- their verdict does not transfer -- a single index, and the whole
-- difference between a covered statement and an uncovered one.
--
-- THE SHRINK IS NOT SMALL, which is why it was worth instantiating
-- rather than waving through: dropping the key by one divides the
-- grant by `(2 ^ S) ^ suc W` and removes a whole `nestUnit` from its
-- base, and at these caps `S` is in the twenties.
--
-- WHAT IS LOAD-BEARING.  Both premises the leaves name are pinned by
-- `refl` rather than assumed, and every burst is pinned non-empty, so
-- no conjunct here is satisfied by having nothing in it.  The rows
-- rise through a family until the delivered figure moves, which is
-- what makes a fit that closed only on slack show up as a crossover.
--
-- AND THE DUPLICATOR DOES NOT COMPOUND AT THIS SHAPE, which is the
-- finding rather than a disappointment: the same `dup` family reads
-- one, two, four, eight when its head is subscribed at the ROOT and
-- reads one, two, three, four here.  A descent into the BODY runs
-- under the wrap's own frame, and the frame SUBSCRIBES each
-- observable the body emits instead of handing it on, so the layer
-- the doubling would have been carried in is consumed on the way
-- out.  The consequence for coverage is precise: at the leaf's own
-- shape the delivered figure is linear in the level for both
-- families, so nothing reached from here can outrun a grant whose
-- factor is a power -- and a duplication rate that DOES survive a
-- frame is the region still open.
--
-- TARGET: pushVals-merge
-- TARGET: pushVals-switch
-- TARGET: pushVals-exhaust
-- ══════════════════════════════════════════════════════════════════
module Probed.PushVals-Body-Key where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; switchAllᵉ;
         exhaustAllᵉ; nat̂; strmᵗ; varᵗ; caseᵗ; inlᵗ; syncSizeᵛ; syncSizeᵉ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init; EvalSt; Sched;
         Path; _↠_; thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; mintNode;
         installNode; mergeAll-st; switch-st; exhaust-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nestCapsOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

st₀ : EvalSt prog
st₀ = st-init prog

nid : ℕ
nid = proj₁ (mintNode sched₀)

-- the path the leaves state the descent under: the wrap's own frame,
-- then the root
κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

-- ── the two families ──────────────────────────────────────────────

-- the tower: delivered nesting is the layer count
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the substituting step: the payload lands in the map's step function
-- and in the source it maps over, so one application doubles
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

D : ℕ → Closed Γ₂ (obs natᵗ)
D zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
D (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (D k) ∷ [])))

-- the BODY the leaf descends into, at each family
bTow bDup : ℕ → Closed Γ₂ (obs (obs natᵗ))
bTow k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])
bDup k = ofᵉ (strmᵗ (D k) ∷ [])

-- ── the leaf's own shape ──────────────────────────────────────────

tight : Closed Γ₂ (obs natᵗ) → Caps
tight h = caps (syncSizeᵛ (obs (obs natᵗ)) h)
               (pWᵛ 2 slots (obs (obs natᵗ)) h) 0

resM : Closed Γ₂ (obs (obs natᵗ)) → _
resM b = subscribeE gasBig b (thru-outer mergeAllᵒ nid ↠ κ) 0 0
           (proj₂ (mintNode sched₀))
           (installNode nid (mergeAll-st {t = obs natᵗ} nothing 0 [] false) st₀)

resS : Closed Γ₂ (obs (obs natᵗ)) → _
resS b = subscribeE gasBig b (thru-outer switchᵒ nid ↠ κ) 0 0
           (proj₂ (mintNode sched₀))
           (installNode nid (switch-st nothing false) st₀)

resX : Closed Γ₂ (obs (obs natᵗ)) → _
resX b = subscribeE gasBig b (thru-outer exhaustᵒ nid ↠ κ) 0 0
           (proj₂ (mintNode sched₀))
           (installNode nid (exhaust-st false false) st₀)

-- THE KEY, and it is the body's -- one below every earlier row's
mKey : Closed Γ₂ (obs (obs natᵗ)) → ℕ
mKey b = syncSizeᵉ b

-- the grant at `W = 0`, `nestB` written out because it is sealed
G : Closed Γ₂ (obs natᵗ) → Closed Γ₂ (obs (obs natᵗ)) → ℕ
G h b =
  let S = Caps.cSize (tight h)
      m = mKey b
  in (2 ^ S) ^ m * (nestDᵉ h + suc m * nestUnit prog slots)

lhsM lhsS lhsX : Closed Γ₂ (obs (obs natᵗ)) → ℕ
lhsM b = nodesMax (proj₂ (proj₂ (resM b)))
           ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ (resM b))))
lhsS b = nodesMax (proj₂ (proj₂ (resS b)))
           ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ (resS b))))
lhsX b = nodesMax (proj₂ (proj₂ (resX b)))
           ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ (resX b))))

-- ── the premises, pinned rather than assumed ──────────────────────

prem : Closed Γ₂ (obs natᵗ) → Bool × Bool
prem h = nestValOK? (tight h) (obs (obs natᵗ)) h
       , nestCapsOK? (tight h) sched₀ st₀

premTow : prem (mergeAllᵉ nothing (bTow 2)) ≡ (true , true)
premTow = refl

premDup : prem (mergeAllᵉ nothing (bDup 3)) ≡ (true , true)
premDup = refl

-- ── NON-VACUITY: every descent hands back values ──────────────────

lenM : Closed Γ₂ (obs (obs natᵗ)) → ℕ
lenM b = length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ (resM b))))

lensBK : ℕ × ℕ
lensBK = lenM (bTow 2) , lenM (bDup 3)

lensBK≡ : lensBK ≡ (2 , 1)
lensBK≡ = refl

-- ── THE COMPOUNDING, measured at the body key ─────────────────────

deliveredTow : ℕ × ℕ × ℕ
deliveredTow = lhsM (bTow 0) , lhsM (bTow 1) , lhsM (bTow 2)

deliveredDup : ℕ × ℕ × ℕ × ℕ
deliveredDup = lhsM (bDup 0) , lhsM (bDup 1) , lhsM (bDup 2) , lhsM (bDup 3)

deliveredTow≡ : deliveredTow ≡ (0 , 1 , 2)
deliveredTow≡ = refl

deliveredDup≡ : deliveredDup ≡ (1 , 2 , 3 , 4)
deliveredDup≡ = refl

-- ── the race, at the index the leaves are actually read at ────────

fitTow0 : (lhsM (bTow 0) ≤ᵇ G (mergeAllᵉ nothing (bTow 0)) (bTow 0)) ≡ true
fitTow0 = refl

fitTow1 : (lhsM (bTow 1) ≤ᵇ G (mergeAllᵉ nothing (bTow 1)) (bTow 1)) ≡ true
fitTow1 = refl

fitTow2 : (lhsM (bTow 2) ≤ᵇ G (mergeAllᵉ nothing (bTow 2)) (bTow 2)) ≡ true
fitTow2 = refl

fitDup1 : (lhsM (bDup 1) ≤ᵇ G (mergeAllᵉ nothing (bDup 1)) (bDup 1)) ≡ true
fitDup1 = refl

fitDup2 : (lhsM (bDup 2) ≤ᵇ G (mergeAllᵉ nothing (bDup 2)) (bDup 2)) ≡ true
fitDup2 = refl

fitDup3 : (lhsM (bDup 3) ≤ᵇ G (mergeAllᵉ nothing (bDup 3)) (bDup 3)) ≡ true
fitDup3 = refl

-- the other two heads at the same key
fitS : (lhsS (bTow 2) ≤ᵇ G (switchAllᵉ (bTow 2)) (bTow 2)) ≡ true
fitS = refl

fitX : (lhsX (bTow 2) ≤ᵇ G (exhaustAllᵉ (bTow 2)) (bTow 2)) ≡ true
fitX = refl

-- ── THE RATE THAT SURVIVES THE FRAME ──────────────────────────────

-- the same substituting step one type up, so what the body EMITS is
-- the doubled term rather than a term that merely contains one: the
-- frame subscribes an emitted `obs natᵗ`, and the measure reads the
-- value before it does
dup₂ : Fn Γ₂ [] [] [] (obs (obs natᵗ)) (obs (obs natᵗ))
dup₂ = strmᵗ (mapᵉ
         (caseᵗ (inlᵗ (varᵗ (there (here refl))))
                (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
                (varᵗ (here refl)))
         (ofᵉ (varᵗ (here refl) ∷ [])))

D₂ : ℕ → Closed Γ₂ (obs (obs natᵗ))
D₂ zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
               (ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])) ∷ []))) ∷ [])
D₂ (suc k) = mapᵉ dup₂ (mergeAllᵉ nothing (ofᵉ (strmᵗ (D₂ k) ∷ [])))

deliveredD₂ : ℕ × ℕ × ℕ × ℕ
deliveredD₂ = lhsM (D₂ 0) , lhsM (D₂ 1) , lhsM (D₂ 2) , lhsM (D₂ 3)

deliveredD₂≡ : deliveredD₂ ≡ (1 , 2 , 4 , 8)
deliveredD₂≡ = refl

premD₂ : prem (mergeAllᵉ nothing (D₂ 3)) ≡ (true , true)
premD₂ = refl

lenD₂ : ℕ
lenD₂ = lenM (D₂ 3)

lenD₂≡ : lenD₂ ≡ 1
lenD₂≡ = refl

fitD₂1 : (lhsM (D₂ 1) ≤ᵇ G (mergeAllᵉ nothing (D₂ 1)) (D₂ 1)) ≡ true
fitD₂1 = refl

fitD₂2 : (lhsM (D₂ 2) ≤ᵇ G (mergeAllᵉ nothing (D₂ 2)) (D₂ 2)) ≡ true
fitD₂2 = refl

fitD₂3 : (lhsM (D₂ 3) ≤ᵇ G (mergeAllᵉ nothing (D₂ 3)) (D₂ 3)) ≡ true
fitD₂3 = refl
