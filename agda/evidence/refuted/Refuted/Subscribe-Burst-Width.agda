-- ══════════════════════════════════════════════════════════════════
-- THE DESCENT'S ARRIVAL BURST IS FALSE ON ITS WIDTH HALF, and the
-- arrival level cannot repair it: the level moves the SIZE axis and
-- leaves the width field exactly where it was.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  At any subscription and any path, every
-- value the descent hands back fits the arrival cap -- both halves of
-- it, the written size and the frame width.
--
-- WHERE IT BREAKS.  Every premise reads the SIZE field or the node
-- table: the value and closure keys are size bounds, and the invariant
-- is one boolean over node widths that a table the descent has not
-- written satisfies at every width.  So the width field may be zero,
-- and a source that hands back an observable payload is then absurd at
-- the FIRST instant -- an `ofᵉ` delivers `length ts`, so the emitted
-- inner's own reading is at least one.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about the ADMISSIBILITY
-- half of the same burst, which reads the size axis alone and which
-- the arrival level therefore does move; it says nothing about what a
-- positive width owes, which is the content the statement still
-- carries once a width key is threaded; and the row at the foot pins
-- that the walk stated over the node table SURVIVES this witness, so
-- the crossing is the arrival bound's alone.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Burst-Width where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; switchAllᵉ; mergeAllᵉ; nat̂; strmᵗ;
         syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; mintNode; EvalSt; Sched;
         Stream; _↠_; thru-outer; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; arrCapAt)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestValOK?; burstCaps?)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestCapsOK?; nestClosOK?)
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

sched₁ : Sched Γ₂
sched₁ = proj₂ (mintNode sched₀)

st₁ : EvalSt head
st₁ = installNode nid (mergeAll-st {t = obs natᵗ} (just 1) 0 [] false)
                  (st-init head)

res : Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt head
res = subscribeE gasBig wrapped (thru-outer mergeAllᵒ nid ↠ root) 0 0
        sched₁ st₁

W : ℕ
W = descW gasBig wrapped (thru-outer mergeAllᵒ nid ↠ root) 0 0 sched₁ st₁

-- the premises, pinned true where the row runs rather than assumed
prems : Bool × Bool × Bool
prems = nestCapsOK? cap sched₁ st₁
      , nestValOK? cap (obs (obs (obs natᵗ))) wrapped
      , nestClosOK? cap slots wrapped

prems≡ : prems ≡ (true , true , true)
prems≡ = refl

Stmt : Set
Stmt =
  Sched.slots sched₁ ≡ slots →
  nestCapsOK? cap sched₁ st₁ ≡ true →
  nestValOK? cap (obs (obs (obs natᵗ))) wrapped ≡ true →
  nestClosOK? cap slots wrapped ≡ true →
  descW gasBig wrapped (thru-outer mergeAllᵒ nid ↠ root) 0 0 sched₁ st₁ ≤ W →
  burstCaps? (arrCapAt (Caps.cSize cap) cap) slots (proj₁ res) ≡ true

burst-width-absurd : Stmt → ⊥
burst-width-absurd h with h refl refl refl refl ≤-refl
... | ()

-- THE TWO FIGURES THE CROSSING IS BETWEEN, spelled out so a repair
-- that moves either of them fails here rather than quietly agreeing:
-- the arrival cap's width, and the reading of the first payload the
-- source hands back.
figs : ℕ × ℕ
figs = Caps.cWid (arrCapAt (Caps.cSize cap) cap)
     , pWᵛ 2 slots (obs (obs natᵗ)) (ofᵉ (strmᵗ (deepV 1) ∷ []))

figs≡ : figs ≡ (0 , 1)
figs≡ = refl

-- AND THE WALK ABOVE IT DOES NOT INHERIT THE CROSSING, which is a
-- boundary worth pinning rather than an omission: the arm's node
-- reading survives this width because the merge node's queue is empty
-- where the descent leaves it, so what the width-zero cap kills is the
-- ARRIVAL bound alone and not the invariant stated over the table.
Rw : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt head
Rw = subscribeE gasBig head root 0 0 sched₀ (st-init head)

walkRead : Bool
walkRead = nestCapsOK? cap (proj₁ (proj₂ Rw)) (proj₂ (proj₂ Rw))

walkRead≡ : walkRead ≡ true
walkRead≡ = refl
