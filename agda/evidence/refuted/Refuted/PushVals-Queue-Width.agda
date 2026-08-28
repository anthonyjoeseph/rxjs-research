-- ══════════════════════════════════════════════════════════════════
-- THE BURST'S QUEUE READING IS FALSE AT A WIDTH OF ZERO, and nothing
-- in the statement's premises rules that width out.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  At every state the outer's burst walk
-- passes, a merge node parked at the wrap holds strictly fewer entries
-- than the width field grants, so one more arrival still fits.
--
-- WHERE IT BREAKS.  The conclusion asks for `suc (length q) ≤ cWid`,
-- which is `1 ≤ cWid` already at the EMPTY queue the wrap installs --
-- so the statement asserts the width field is positive.  Every premise
-- it carries reads the SIZE field or the slots: the value and closure
-- keys are size bounds, the invariant is satisfied by a table the
-- descent has not written, and the measure premise is an inequality in
-- the burst's own currency.  None of them mentions the width, so the
-- width may be zero and the very first reading is absurd.
--
-- THE WITNESS is the neighbouring probe's merge program at a cap whose
-- size is taken off the head, as that probe takes it, and whose width
-- is set to zero.  The contradiction lands at the FIRST instant and at
-- the node the wrap itself installed, so no walk and no arrival is
-- doing the work -- which is why the repair is a premise and not a
-- cleverer proof.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about the bounded-limit
-- case, where a queue that has actually grown may exceed a positive
-- width; that is the content the statement still owes once the width
-- is known to be positive.
-- ══════════════════════════════════════════════════════════════════
module Refuted.PushVals-Queue-Width where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; InstEmit)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; switchAllᵉ; mergeAllᵉ; nat̂; strmᵗ;
         syncSizeᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (splitEvents; root; sched-init; st-init; subscribeE; mintNode; EvalSt; Sched;
         Stream; _↠_; thru-outer; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestCapsOK?; nestClosOK?; pushValsQOK)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : Val Γ₂ (obs (obs (obs natᵗ)))
wrapped = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷
               strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷ [])

head : Closed Γ₂ (obs natᵗ)
head = mergeAllᵉ (just 1) wrapped

-- the size field is the head's own, as the probe beside this takes it;
-- the WIDTH is zero, which no premise forbids
cap : Caps
cap = caps (syncSizeᵛ (obs (obs natᵗ)) head) 0 0

sched₀ : Sched Γ₂
sched₀ = sched-init head slots

nid : ℕ
nid = proj₁ (mintNode sched₀)

st₁ : EvalSt head
st₁ = installNode nid (mergeAll-st {t = obs natᵗ} (just 1) 0 [] false)
                  (st-init head)

res : Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt head
res = subscribeE gasBig wrapped (thru-outer mergeAllᵒ nid ↠ root) 0 0
        (proj₂ (mintNode sched₀)) st₁

W : ℕ
W = descW gasBig head root 0 0 sched₀ (st-init head)

-- the premises, pinned true where the row runs rather than assumed
prems : Bool × Bool × Bool
prems = nestCapsOK? cap sched₀ (st-init head)
      , nestValOK? cap (obs (obs natᵗ)) head
      , nestClosOK? cap slots head

prems≡ : prems ≡ (true , true , true)
prems≡ = refl

Stmt : Set
Stmt =
  Sched.slots sched₀ ≡ slots →
  nestCapsOK? cap sched₀ (st-init head) ≡ true →
  nestValOK? cap (obs (obs natᵗ)) head ≡ true →
  nestClosOK? cap slots head ≡ true →
  descW gasBig head root 0 0 sched₀ (st-init head) ≤ W →
  pushValsQOK cap gasBig mergeAllᵒ nid root 0 0
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

queue-absurd : Stmt → ⊥
queue-absurd h with h refl refl refl refl ≤-refl
... | (q , _) , _ with q (just 1) 0 [] false refl
...   | ()

-- WHICH FIELD, since the repair is a premise on exactly one of them
figs : ℕ × ℕ
figs = Caps.cWid cap , 0

figs≡ : figs ≡ (0 , 0)
figs≡ = refl

widRead : List Bool
widRead = go (proj₁ res)
  where
  go : Stream Γ₂ (obs (obs natᵗ)) → List Bool
  go [] = []
  go (em ∷ ems) =
    all (valCaps? cap slots (obs (obs natᵗ)))
        (proj₁ (splitEvents {A = Val Γ₂ (obs natᵗ)} (InstEmit.events em)))
    ∷ go ems

widRead≡ : widRead ≡ (false ∷ [])
widRead≡ = refl
