-- ══════════════════════════════════════════════════════════════════
-- THE LIVE FOLD, RE-INSTANTIATED IN THE CURRENCY THAT REPLACED THE
-- ONE THAT DIED, AT THE VERY WITNESS THAT KILLED IT.
--
-- TARGET: chainStep-nest-live @65a0d8
--
-- WHY THESE ROWS AND NOT A SWEEP.  `Refuted.Chain-Step-Live-Nest`
-- refuted the premise-free form against a `deferᵉ` arrival whose body
-- is three `switchAllᵉ` layers deep: the grown fold read the body's
-- depth exactly and the old right side did not move with it.  The
-- statement now charges `pathNestF path * sizeᵛ` of the ARRIVAL, and
-- `sizeᵛ` descends into a deferred body where the depth measure reads
-- zero -- so the adversarial family is the one place the repair is
-- actually bet, and a row anywhere else is not evidence about it.
--
-- WHAT IS LOAD-BEARING.  Every row here CAN fail: the left side is the
-- evaluator's own grown fold, the right is computed from the arrival
-- and the path, and the two are pinned separately before the ordering
-- is taken, so a repair that moves either side fails naming a number
-- rather than quietly turning the crossing into an equality.  The
-- unbounded-gap rows are the point: at three layers and at five, the
-- left side moves with the body and the charge moves with it.
--
-- THE ATTACK, and it is the reason the file is not just the two
-- positive rows.  The right side has NO store term -- it is the
-- incoming live fold, the slots, and the arrival's own charge.  So a
-- `chainStep` that mints a live out of something PARKED IN A NODE
-- would exceed it while the arrival stayed small, and the merge drain
-- is known reachable: a limited `mergeAllᵉ` whose first inner never
-- finishes inside the subscribe frame leaves the second genuinely
-- pending.  The rows deliver into exactly that node with a shallow
-- arrival, so a drain that subscribes the parked inner has nothing on
-- the right to pay for it.
-- ══════════════════════════════════════════════════════════════════
module Probed.Chain-Step-Live-Nest where

open import Data.Bool using (false; true; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.List using ([]; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _⊔_; _*_; _+_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Val; natᵗ; obs; nat̂; ofᵉ; strmᵗ; deferᵉ; switchAllᵉ;
         mergeAllᵉ; sizeᵛ; Exp)
open import Rx.Prim using (Gas; g0; gs)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root;
         chainStep; Arrival; Path; _↠_; thru-outer; mergeAllᵒ;
         map-f; installNode; mergeAll-st)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; pathNestF; nodeNest)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps
  using (chainStep-nest-live)
open import Refuted.Demand-Programs using (Γ₂; insT)

open import Probed.Apparatus using (Confirms)

slots : Slots Γ₂
slots = insT 0 0 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE gas prog root 0 0 (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

-- ── the refuting family, re-run in the new currency ───────────────

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

arr : ℕ → Arrival Γ₂
arr k = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = obs natᵗ
               ; payload = deferᵉ (deepV k) ; isLast = false }

path : Path Γ₂ (obs natᵗ) natᵗ
path = thru-outer mergeAllᵒ 0 ↠ root

-- the node the chain delivers into: an empty limited merge
emptyNode : EvalSt prog
emptyNode = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (proj₂ sub)

grown : ℕ → ℕ
grown k = liveMax (proj₁ (proj₂ (chainStep 1 (arr k) path (proj₁ sub) emptyNode)))

charge : ℕ → ℕ
charge k = liveMax (proj₁ sub) ⊔ slotsNestSum (Sched.slots (proj₁ sub))
             ⊔ pathNestF path * sizeᵛ (obs natᵗ) (deferᵉ (deepV k))

-- BOTH SIDES PINNED SEPARATELY, at the depth that refuted the old form
-- and at the depth its second row took it to
sides : ℕ
sides = grown 3 + 10 * charge 3 + 1000 * grown 5 + 10000 * charge 5

sides≡ : sides ≡ 245163
sides≡ = refl

fits : (grown 3 ≤ᵇ charge 3) ∧ (grown 5 ≤ᵇ charge 5) ≡ true
fits = refl

-- ── the attack: a live minted from a PARKED inner, not the arrival ──

-- an inner that cannot finish inside the subscribe frame, so a limit
-- of one stays spent and whatever follows it is genuinely pending
liveInner : Val Γ₂ (obs natᵗ)
liveInner = deferᵉ (ofᵉ (nat̂ 0 ∷ []))

held : ℕ → Val Γ₂ (obs (obs natᵗ))
held k = ofᵉ (strmᵗ liveInner ∷ strmᵗ (deepV k) ∷ [])

parked : ℕ → Closed Γ₂ natᵗ
parked k = mergeAllᵉ (just 1) (held k)

-- deliver a SHALLOW arrival into the node that holds the deep pending
shallow : Arrival Γ₂
shallow = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = obs natᵗ
                 ; payload = deepV 0 ; isLast = false }

parkedSt : (k : ℕ) → EvalSt (parked k)
parkedSt k = proj₂ (proj₂ (subscribeE gas (parked k) root 0 0
                            (sched-init (parked k) slots) (st-init (parked k))))

parkedSc : (k : ℕ) → Sched Γ₂
parkedSc k = proj₁ (proj₂ (subscribeE gas (parked k) root 0 0
                            (sched-init (parked k) slots) (st-init (parked k))))

aGrown : ℕ → ℕ
aGrown k = liveMax (proj₁ (proj₂ (chainStep 1 shallow path (parkedSc k) (parkedSt k))))

aCharge : ℕ → ℕ
aCharge k = liveMax (parkedSc k) ⊔ slotsNestSum (Sched.slots (parkedSc k))
              ⊔ pathNestF path * sizeᵛ (obs natᵗ) (deepV 0)

-- THE ARMING READING, without which the two rows above are a story
-- about a node that was never deep: this is the pending list's own
-- nesting, taken from the same state the step is run against
armed : ℕ → ℕ
armed k = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
                (EvalSt.nodes (parkedSt k))

attack : ℕ
attack = aGrown 2 + 10 * aCharge 2 + 1000 * armed 2
           + 10000 * aGrown 4 + 100000 * aCharge 4 + 1000000 * armed 4

attack≡ : attack ≡ 4302030
attack≡ = refl

aFits : (aGrown 2 ≤ᵇ aCharge 2) ∧ (aGrown 4 ≤ᵇ aCharge 4) ≡ true
aFits = refl

-- ── the second frame, where the factor does NOT dilute ─────────────

-- `frameNestF` is one at every frame but `map-f`/`scan-f`, so a path
-- of two merge frames leaves the charge exactly where the one-frame
-- rows left it while giving the step a second mint site to run
-- through.  That is the tight direction, and the reason a longer path
-- is not simply a weaker claim.
deep2 : ℕ → Val Γ₂ (obs (obs natᵗ))
deep2 k = deferᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

arr2 : ℕ → Arrival Γ₂
arr2 k = record { tick = 0 ; ordinal = 0 ; source = 1
                ; elemTy = obs (obs natᵗ) ; payload = deep2 k ; isLast = false }

path2 : Path Γ₂ (obs (obs natᵗ)) natᵗ
path2 = thru-outer mergeAllᵒ 1 ↠ (thru-outer mergeAllᵒ 0 ↠ root)

twoNodes : EvalSt prog
twoNodes = installNode 1 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) emptyNode

gGrown : ℕ → ℕ
gGrown k = liveMax (proj₁ (proj₂ (chainStep 1 (arr2 k) path2 (proj₁ sub) twoNodes)))

gCharge : ℕ → ℕ
gCharge k = liveMax (proj₁ sub) ⊔ slotsNestSum (Sched.slots (proj₁ sub))
              ⊔ pathNestF path2 * sizeᵛ (obs (obs natᵗ)) (deep2 k)

two : ℕ
two = gGrown 3 + 100 * gCharge 3 + 10000 * gGrown 5 + 1000000 * gCharge 5

two≡ : two ≡ 27051903
two≡ = refl

twoFits : (gGrown 3 ≤ᵇ gCharge 3) ∧ (gGrown 5 ≤ᵇ gCharge 5) ≡ true
twoFits = refl

-- ── the one frame whose factor exceeds one, and the only one that
-- ── transforms the value on the way through

-- a `map-f` can hand the frame something the ARRIVAL never carried, so
-- this is where a charge read off the arrival ought to break if it is
-- going to.  The function is constant and deep, the arrival is
-- shallow, and what is supposed to pay for the difference is the
-- factor -- `2 ^ sizeᵗ` of the function itself.  The constant is
-- DEFERRED, without which the frame subscribes something that
-- finishes inside the step and the row cannot fail at all: a plain
-- deep observable leaves the grown fold at zero.
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE zero    = ofᵉ (nat̂ 0 ∷ [])
deepE (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepE k) ∷ []))

path3 : ℕ → Path Γ₂ (obs natᵗ) natᵗ
path3 k = map-f (strmᵗ (deferᵉ (deepE k))) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

mGrown : ℕ → ℕ
mGrown k = liveMax (proj₁ (proj₂ (chainStep 1 shallow (path3 k) (proj₁ sub) emptyNode)))

mCharge : ℕ → ℕ
mCharge k = liveMax (proj₁ sub) ⊔ slotsNestSum (Sched.slots (proj₁ sub))
              ⊔ pathNestF (path3 k) * sizeᵛ (obs natᵗ) (deepV 0)

mapped : ℕ
mapped = mGrown 2 + 1000 * mGrown 4

mapped≡ : mapped ≡ 4002
mapped≡ = refl

mapFits : (mGrown 2 ≤ᵇ mCharge 2) ∧ (mGrown 4 ≤ᵇ mCharge 4) ≡ true
mapFits = refl

-- ── the tie: the statement's own ordering, at one point per family ──

-- The rows above are the READING -- both sides recomputed here out of
-- `liveMax`, `slotsNestSum` and `pathNestF`, and compared by `≤ᵇ`.
-- That comparison is a restatement, and a restatement is exactly what
-- can drift weaker without anything going red.  The four rows below
-- are the statement itself instantiated: Agda writes each type from
-- `chainStep-nest-live` as it reads, so the probe supplies only the
-- point, and the Boolean above is spent as the decision procedure that
-- discharges it rather than as the claim.
--
-- ONE POINT PER FAMILY, at the depth each family's own reading calls
-- its tight one -- the refuting arrival, the parked node the charge
-- has no store term for, the second merge frame where the factor does
-- not dilute, and the `map-f` that hands the step a value the arrival
-- never carried.  The remaining depths move a quantity the tie already
-- reaches, and each additional row is a whole run of the evaluator.
liveRow : Confirms
  (chainStep-nest-live {e = prog} 1 (arr 3) path (proj₁ sub) emptyNode)
liveRow = ≤ᵇ⇒≤ _ _ tt

attackRow : Confirms
  (chainStep-nest-live {e = parked 2} 1 shallow path (parkedSc 2) (parkedSt 2))
attackRow = ≤ᵇ⇒≤ _ _ tt

twoRow : Confirms
  (chainStep-nest-live {e = prog} 1 (arr2 3) path2 (proj₁ sub) twoNodes)
twoRow = ≤ᵇ⇒≤ _ _ tt

mapRow : Confirms
  (chainStep-nest-live {e = prog} 1 shallow (path3 2) (proj₁ sub) emptyNode)
mapRow = ≤ᵇ⇒≤ _ _ tt
