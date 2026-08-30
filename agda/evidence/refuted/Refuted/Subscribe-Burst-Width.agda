-- ══════════════════════════════════════════════════════════════════
-- THE DESCENT'S ARRIVAL BURST IS FALSE ON ITS WIDTH HALF, AND THE
-- SLOT-TABLE KEY DOES NOT REPAIR IT.  Neither does the arrival level:
-- the level moves the SIZE axis and leaves the width field exactly
-- where it was.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAYS.  At any subscription and any path, every
-- value the descent hands back fits the arrival cap -- both halves of
-- it, the written size and the frame width -- given the state
-- invariant in full and the bundle of slot-table keys the proven face
-- carries.
--
-- WHERE IT BREAKS, AND WHY THE KEYS CANNOT REACH IT.  Every premise
-- reads the SIZE field, the node table, or the SLOTS.  The arrivals
-- are none of those: they are the source's own payload, and a source
-- that PARKS its inners carries them out of the descent unread.  So
-- the crossing is put in the payload rather than in the width field --
-- a parked inner delivering three values against a table that pins the
-- width at two -- and the source's arity is then a free parameter that
-- no key over the cap and the table can close.  The registry field is
-- positive and the size field is generous here for the same reason:
-- what a premise bundle CAN forbid is made true, so that what is left
-- is the crossing and not an unstatable row.
--
-- AND THE SAME SOURCE KILLS THE WALK ONE HOP UP, at the same cap and
-- the same table.  The arm's own node carries the parked pair, so the
-- state the descent leaves is outside the invariant it entered under
-- -- which is the leaf's crossing arriving in a proven body's
-- conclusion rather than in a leaf's.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about the ADMISSIBILITY
-- half of the same burst, which reads the size axis alone and which
-- the arrival level therefore does move; it says nothing about what a
-- width key on the ARRIVAL owes, which is the content the statement
-- still carries once such a key is threaded -- and the reason that key
-- cannot be threaded flat is a dead route at the leaf, not a fact this
-- file establishes.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Burst-Width where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; switchAllᵉ; mergeAllᵉ; nat̂; strmᵗ; deferᵉ)
open import Rx.Frame-Width using (pWᵛ; dWᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; mintNode; EvalSt; Sched;
         Stream; _↠_; thru-outer; mergeAllᵒ; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; arrCapAt)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestValOK?; burstCaps?; capsOK?; slotsCaps?)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestCapsOK?; nestClosOK?; FaceOK; faceOK)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

inner1 : Val Γ₂ (obs natᵗ)
inner1 = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- three values behind a defer, so the pair the head parks is what the
-- reading crosses on
inner3 : Val Γ₂ (obs (obs natᵗ))
inner3 = ofᵉ (strmᵗ inner1 ∷ strmᵗ inner1 ∷ strmᵗ inner1 ∷ [])

parked : Val Γ₂ (obs (obs (obs natᵗ)))
parked = ofᵉ (strmᵗ (deferᵉ inner3) ∷
              strmᵗ (deferᵉ inner3) ∷ [])

head : Closed Γ₂ (obs natᵗ)
head = mergeAllᵉ (just 1) parked

-- SIZE AND REGISTRY GENEROUS, WIDTH AT WHAT THE TABLE ITSELF PINS.
-- Both are what the premise bundle can forbid, so both are satisfied
-- here; the width is two because the slot key admits nothing under it,
-- which is what makes a zero-width row unstatable rather than false.
cap : Caps
cap = caps 256 2 1

sched₀ : Sched Γ₂
sched₀ = sched-init head slots

nid : ℕ
nid = proj₁ (mintNode sched₀)

sched₁ : Sched Γ₂
sched₁ = proj₂ (mintNode sched₀)

st₁ : EvalSt head
st₁ = installNode nid (mergeAll-st {t = obs natᵗ} (just 1) 0 [] false)
                  (st-init head)

face : FaceOK cap slots
face = faceOK (≤ᵇ⇒≤ 2 256 tt) ≤-refl refl
              (≤ᵇ⇒≤ (slotsSize slots) 256 tt)

res : Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt head
res = subscribeE gasBig parked (thru-outer mergeAllᵒ nid ↠ root) 0 0
        sched₁ st₁

W : ℕ
W = descW gasBig parked (thru-outer mergeAllᵒ nid ↠ root) 0 0 sched₁ st₁

-- the premises, pinned true where the row runs rather than assumed
prems : Bool × Bool × Bool × Bool
prems = slotsCaps? (Caps.cSize cap) (Caps.cWid cap) slots
      , capsOK? cap sched₁ st₁
      , nestValOK? cap (obs (obs (obs natᵗ))) parked
      , nestClosOK? cap slots parked

prems≡ : prems ≡ (true , true , true , true)
prems≡ = refl

Stmt : Set
Stmt =
  FaceOK cap slots →
  Sched.slots sched₁ ≡ slots →
  capsOK? cap sched₁ st₁ ≡ true →
  nestValOK? cap (obs (obs (obs natᵗ))) parked ≡ true →
  nestClosOK? cap slots parked ≡ true →
  descW gasBig parked (thru-outer mergeAllᵒ nid ↠ root) 0 0 sched₁ st₁ ≤ W →
  burstCaps? (arrCapAt (Caps.cSize cap) cap) slots (proj₁ res) ≡ true

burst-width-absurd : Stmt → ⊥
burst-width-absurd h with h face refl refl refl refl ≤-refl
... | ()

-- THE TWO FIGURES THE CROSSING IS BETWEEN, spelled out so a repair
-- that moves either of them fails here rather than quietly agreeing:
-- the arrival cap's width, and the reading of the first payload the
-- source hands back.
figs : ℕ × ℕ
figs = Caps.cWid (arrCapAt (Caps.cSize cap) cap)
     , pWᵛ 2 slots (obs (obs natᵗ)) inner3

figs≡ : figs ≡ (2 , 3)
figs≡ = refl

-- AND THE WALK ONE HOP UP GOES WITH IT.  The limit holds the second
-- inner, so the node the arm installed carries the parked pair out of
-- the descent and the state the walk hands back is outside the
-- invariant it entered under -- at the same cap, the same table and
-- the same source.
RP : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt head
RP = subscribeE gasBig head root 0 0 sched₀ (st-init head)

WP : ℕ
WP = descW gasBig head root 0 0 sched₀ (st-init head)

premsP : Bool × Bool × Bool
premsP = capsOK? cap sched₀ (st-init head)
       , nestValOK? cap (obs (obs natᵗ)) head
       , nestClosOK? cap slots head

premsP≡ : premsP ≡ (true , true , true)
premsP≡ = refl

StmtWalk : Set
StmtWalk =
  FaceOK cap slots →
  Sched.slots sched₀ ≡ slots →
  capsOK? cap sched₀ (st-init head) ≡ true →
  nestValOK? cap (obs (obs natᵗ)) head ≡ true →
  nestClosOK? cap slots head ≡ true →
  descW gasBig head root 0 0 sched₀ (st-init head) ≤ WP →
  nestCapsOK? cap (proj₁ (proj₂ RP)) (proj₂ (proj₂ RP)) ≡ true

walk-absurd : StmtWalk → ⊥
walk-absurd h with h face refl refl refl refl ≤-refl
... | ()

-- THE KEY THAT SEPARATES IT.  The crossing payload is a PARKED body,
-- so its `outWᵛ` is zero and every unit of its width sits on the dW
-- side.  The source therefore reads THREE on the parked measure at the
-- table it is subscribed under, against a cap granting two -- so a
-- `dWᵉ … ≤ cWid` premise excludes this witness exactly, which is what
-- licenses conditioning the leaf on it rather than weakening it.
keyFig : ℕ
keyFig = dWᵉ 2 slots parked

keyFig≡ : keyFig ≡ 3
keyFig≡ = refl
