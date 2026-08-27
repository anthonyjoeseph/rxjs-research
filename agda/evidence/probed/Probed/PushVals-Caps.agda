-- THE BUNDLE THE BURST CARRIES, which is the half of the burst claim
-- nothing had ever instantiated.  Every earlier probe of this family
-- pins `nestCapsOK?` at the state the head is ENTERED at -- that is the
-- statement's premise.  What these leaves assert is the bundle at every
-- frame the descent LEAVES, which is a different state and a different
-- claim, and the two were being read as one because they were conjuncts
-- of a single predicate.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: pushVals-merge-caps @41ce21
-- TARGET: pushVals-switch-caps @794562
-- TARGET: pushVals-exhaust-caps @c4cd9e
module Probed.PushVals-Caps where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_; length)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; nat̂; strmᵗ; deferᵉ;
  syncSizeᵛ; mapᵉ; input; Fn; varᵗ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (subscribeE; root; sched-init; st-init; mintNode; installNode; thru-outer; _↠_; mergeAllᵒ;
  switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; Sched; EvalSt; Stream)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestCapsOK?; pushValsCapsOK)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷
                 strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

-- THE THREE HEADS, at the caps the neighbouring wrap probe uses: the
-- cap at the value's own sync size and the width at its own frame
-- width, which is the tightest reading the premises admit.
tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

rM : ℕ → ℕ → Closed Γ₂ (obs natᵗ)
rM lim k = mergeAllᵉ (just lim) (wrapped k)

qS : ℕ → Closed Γ₂ (obs natᵗ)
qS k = switchAllᵉ (wrapped k)

qX : ℕ → Closed Γ₂ (obs natᵗ)
qX k = exhaustAllᵉ (wrapped k)

-- MEASUREMENT PASS: the burst the descent hands back, and the split
-- each of its instants carries, so the tuple's arity is read rather
-- than guessed.
resM : (lim k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rM lim k)
resM lim k =
  subscribeE gasBig (wrapped k)
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rM lim k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rM lim k) slots)))
    (installNode (proj₁ (mintNode (sched-init (rM lim k) slots)))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rM lim k)))

resS : (k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (qS k)
resS k =
  subscribeE gasBig (wrapped k)
    (thru-outer switchᵒ (proj₁ (mintNode (sched-init (qS k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (qS k) slots)))
    (installNode (proj₁ (mintNode (sched-init (qS k) slots)))
       (switch-st nothing false) (st-init (qS k)))

resX : (k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (qX k)
resX k =
  subscribeE gasBig (wrapped k)
    (thru-outer exhaustᵒ (proj₁ (mintNode (sched-init (qX k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (qX k) slots)))
    (installNode (proj₁ (mintNode (sched-init (qX k) slots)))
       (exhaust-st false false) (st-init (qX k)))

burstLens : ℕ × ℕ × ℕ
burstLens = length (proj₁ (resM 1 1)) , length (proj₁ (resS 1)) , length (proj₁ (resX 1))

burstLens≡ : burstLens ≡ (1 , 1 , 1)
burstLens≡ = refl

-- THE CONCLUSION, at the state the descent LEAVES, which is what
-- distinguishes these rows from every earlier probe of this family.
capsM : (lim k : ℕ) → Set
capsM lim k =
  pushValsCapsOK (tight {obs (obs natᵗ)} (rM lim k)) slots gasBig mergeAllᵒ
    (proj₁ (mintNode (sched-init (rM lim k) slots))) root 0 0
    (proj₁ (resM lim k)) (proj₁ (proj₂ (resM lim k))) (proj₂ (proj₂ (resM lim k)))

le : ∀ {x y} → True (x ≤? y) → x ≤ y
le = toWitness

capsM-1 : capsM 1 1
capsM-1 = refl , refl , refl
        , ((le tt , λ { lim act q od refl → le tt }) , (le tt , λ { lim act q od refl → le tt }) , tt)
        , tt

capsS : (k : ℕ) → Set
capsS k =
  pushValsCapsOK (tight {obs (obs natᵗ)} (qS k)) slots gasBig switchᵒ
    (proj₁ (mintNode (sched-init (qS k) slots))) root 0 0
    (proj₁ (resS k)) (proj₁ (proj₂ (resS k))) (proj₂ (proj₂ (resS k)))

capsS-1 : capsS 1
capsS-1 = refl , refl , refl
        , ((le tt , λ { lim act q od () }) , (le tt , λ { lim act q od () }) , tt)
        , tt

capsX : (k : ℕ) → Set
capsX k =
  pushValsCapsOK (tight {obs (obs natᵗ)} (qX k)) slots gasBig exhaustᵒ
    (proj₁ (mintNode (sched-init (qX k) slots))) root 0 0
    (proj₁ (resX k)) (proj₁ (proj₂ (resX k))) (proj₂ (proj₂ (resX k)))

capsX-1 : capsX 1
capsX-1 = refl , refl , refl
        , ((le tt , λ { lim act q od () }) , (le tt , λ { lim act q od () }) , tt)
        , tt

-- THE HEAD'S OWN PREMISES, pinned rather than assumed, so the rows
-- above are not evidence about a region the head grants nothing at.
heads : Bool × Bool × Bool
heads = nestValOK? (tight {obs (obs natᵗ)} (rM 1 1)) (obs (obs natᵗ)) (rM 1 1)
      , nestValOK? (tight {obs (obs natᵗ)} (qS 1)) (obs (obs natᵗ)) (qS 1)
      , nestValOK? (tight {obs (obs natᵗ)} (qX 1)) (obs (obs natᵗ)) (qX 1)

heads≡ : heads ≡ (true , true , true)
heads≡ = refl

entry : Bool × Bool × Bool
entry = nestCapsOK? (tight {obs (obs natᵗ)} (rM 1 1)) (sched-init (rM 1 1) slots) (st-init (rM 1 1))
      , nestCapsOK? (tight {obs (obs natᵗ)} (qS 1)) (sched-init (qS 1) slots) (st-init (qS 1))
      , nestCapsOK? (tight {obs (obs natᵗ)} (qX 1)) (sched-init (qX 1) slots) (st-init (qX 1))

entry≡ : entry ≡ (true , true , true)
entry≡ = refl

-- and a second nesting level, and a limit the arrivals do not fit
-- under, since the queue-room conjunct is the one a limit moves
capsM-2 : capsM 1 2
capsM-2 = refl , refl , refl
        , ((le tt , λ { lim act q od refl → le tt }) , (le tt , λ { lim act q od refl → le tt }) , tt)
        , tt

capsM-0 : capsM 0 1
capsM-0 = refl , refl , refl
        , ((le tt , λ { lim act q od refl → le tt }) , (le tt , λ { lim act q od refl → le tt }) , tt)
        , tt

capsS-2 : capsS 2
capsS-2 = refl , refl , refl
        , ((le tt , λ { lim act q od () }) , (le tt , λ { lim act q od () }) , tt)
        , tt

capsX-2 : capsX 2
capsX-2 = refl , refl , refl
        , ((le tt , λ { lim act q od () }) , (le tt , λ { lim act q od () }) , tt)
        , tt

-- WHICH CONJUNCTS COULD HAVE FAILED, and the answer is not all of
-- them.  Read at a cap granting nothing, the invariant at the very
-- state the descent LEAVES still reads true at all three heads -- so
-- that conjunct is REACHED here and cannot fail here, and a row above
-- is evidence for the other four.  The census below says why: the
-- left state carries one node and an empty registry and live set, so
-- four of the invariant's five conjuncts are quantified over nothing
-- and the fifth is a width reading on an empty queue.
starved : Caps
starved = caps 0 0 0

left-starved : Bool × Bool × Bool
left-starved =
    nestCapsOK? starved (proj₁ (proj₂ (resM 1 1))) (proj₂ (proj₂ (resM 1 1)))
  , nestCapsOK? starved (proj₁ (proj₂ (resS 1))) (proj₂ (proj₂ (resS 1)))
  , nestCapsOK? starved (proj₁ (proj₂ (resX 1))) (proj₂ (proj₂ (resX 1)))

left-starved≡ : left-starved ≡ (true , true , true)
left-starved≡ = refl

census : ℕ × ℕ × ℕ
census = length (EvalSt.registry (proj₂ (proj₂ (resM 1 1))))
       , length (Sched.live (proj₁ (proj₂ (resM 1 1))))
       , length (EvalSt.nodes (proj₂ (proj₂ (resM 1 1))))

census≡ : census ≡ (0 , 0 , 1)
census≡ = refl

-- THE COVERAGE BOUNDARY, and it is a fact about the STATEMENT rather
-- than about this harness: the list these predicates recurse over is
-- the SUBSCRIBE FRAME's own burst, and every program shape reachable
-- here hands back exactly ONE instant -- a two-armed synchronous
-- source, a `deferᵉ` gate whose second arm fires a tick later, and a
-- scripted slot delivering j values over j ticks, at j = 1, 2, 3.  So
-- the recursive tail of `pushValsCapsOK` is `⊤` at every row above,
-- and nothing here is evidence about a walk of length two.
slotsA : ℕ → Slots Γ₂
slotsA j = insT 0 0 j

lift1 : Fn Γ₂ [] [] [] natᵗ (obs (obs natᵗ))
lift1 = strmᵗ (ofᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])) ∷ []))

asyncBody : Closed Γ₂ (obs (obs natᵗ))
asyncBody = mapᵉ lift1 (input (fsuc fzero))

gateBody : Closed Γ₂ (obs (obs natᵗ))
gateBody = mergeAllᵉ nothing
  (ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷ [])) ∷
        strmᵗ (deferᵉ (ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷ []))) ∷ []))

rG : ℕ → Closed Γ₂ (obs natᵗ)
rG lim = mergeAllᵉ (just lim) gateBody

resG : (lim : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rG lim)
resG lim =
  subscribeE gasBig gateBody
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rG lim) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rG lim) slots)))
    (installNode (proj₁ (mintNode (sched-init (rG lim) slots)))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rG lim)))

rA : ℕ → Closed Γ₂ (obs natᵗ)
rA lim = mergeAllᵉ (just lim) asyncBody

resA : (j lim : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rA lim)
resA j lim =
  subscribeE gasBig asyncBody
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rA lim) (slotsA j)))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rA lim) (slotsA j))))
    (installNode (proj₁ (mintNode (sched-init (rA lim) (slotsA j))))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rA lim)))

burstOne : ℕ × ℕ × ℕ × ℕ
burstOne = length (proj₁ (resG 1))
         , length (proj₁ (resA 1 1)) , length (proj₁ (resA 2 1)) , length (proj₁ (resA 3 1))

burstOne≡ : burstOne ≡ (1 , 1 , 1 , 1)
burstOne≡ = refl
