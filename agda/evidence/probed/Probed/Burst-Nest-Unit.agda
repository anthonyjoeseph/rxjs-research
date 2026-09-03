-- THE SUBSCRIBE FRAME'S NESTING RECEIPT, INSTANTIATED -- and the point
-- is that it did not need the seal opened.  The grant at instant one is
-- `nestFacAt` times the rest, and `nestFacAt` is written over
-- `nestBurstAt`, which the seal exports no equation for; so the cap
-- cannot be transcribed into numerals and a direct row is impossible.
-- What the seal DOES export is a floor: the cap at instant zero is the
-- program's own unit, and the step lemma carries that under the cap at
-- instant one with the factor unexamined.  So a row pinning the store's
-- nesting under `nestUnit` -- entirely unsealed, entirely computable --
-- lifts through the exported introduction to the target's OWN
-- conclusion, at these programs, as a checked proof rather than a
-- numeral.
--
-- DEGENERATE ON THE FACTOR, and deliberately so: no row here can fail
-- by `nestFacAt` being too small, because none of them reads it.  What
-- they can fail by is the store outgrowing the unit inside a single
-- subscribe frame, which is the whole question at this instant, and
-- which the wrap corpus below makes the descent actually work for.
--
-- The rows read the store's MAXIMUM, so each of the three components
-- the floor is now assembled from is bounded by them one at a time.
-- TARGET: burst-nest-live @b72e32
-- TARGET: burst-nest-nodes @807fb0
-- TARGET: burst-nest-regs @5abe19
module Probed.Burst-Nest-Unit where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m+n; ≤ᵇ⇒≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Decide using (T-to)
open import Probed.Apparatus using (Confirms)

open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ; deferᵉ; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (subscribeE; root; sched-init; st-init; budgetAt; Sched; EvalSt)
open import Rx.Nest-Depth using ()

open import Verify-Budget-Sufficient.Nest-Store
  using (storeNestMax; nestUnit; nestCapAt; nestCapAt-0; nestCap-mono; nestOK?; nestOK?-intro;
         storeNest-live≤; storeNest-nodes≤; storeNest-regs≤; nestIncAt)
open import Verify-Budget-Sufficient.Caps-Bridge
  using (burst-nest-live; burst-nest-nodes; burst-nest-regs)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

pM : ℕ → Closed Γ₂ (obs natᵗ)
pM k = mergeAllᵉ (just 1) (wrapped k)

pS : ℕ → Closed Γ₂ (obs natᵗ)
pS k = switchAllᵉ (wrapped k)

pX : ℕ → Closed Γ₂ (obs natᵗ)
pX k = exhaustAllᵉ (wrapped k)

-- THE FLOOR, spelled once: the unit sits under the instant-one cap
-- whatever the factor is, because the factor is at least one and the
-- increment is a summand.
unit≤cap : ∀ {t} (e : Closed Γ₂ t) →
  nestUnit e slots ≤ nestCapAt e slots 1
unit≤cap e =
  ≤-trans (≤-reflexive (sym (nestCapAt-0 e slots)))
          (≤-trans (m≤m+n _ _) (nestCap-mono e slots 0))

-- what the descent actually leaves behind, at the gas the target uses
schedOf : ∀ {t} (e : Closed Γ₂ t) → Sched Γ₂
schedOf e = proj₁ (proj₂ (subscribeE (budgetAt e slots 0) e root 0 0
                                     (sched-init e slots) (st-init e)))

stOf : ∀ {t} (e : Closed Γ₂ t) → EvalSt e
stOf e = proj₂ (proj₂ (subscribeE (budgetAt e slots 0) e root 0 0
                                  (sched-init e slots) (st-init e)))

storeOf : ∀ {t} (e : Closed Γ₂ t) → ℕ
storeOf e = storeNestMax (schedOf e) (stOf e)

-- LOAD-BEARING: the store's nesting against the program's own unit.  A
-- program whose frame installs something deeper than its unit fails
-- here, and that is a near miss worth reporting rather than a
-- refutation, since the factor above would still have to be spent.
storeM≡ : ℕ
storeM≡ = storeOf (pM 2)

storeS≡ : ℕ
storeS≡ = storeOf (pS 2)

storeX≡ : ℕ
storeX≡ = storeOf (pX 2)

unitM : ℕ
unitM = nestUnit (pM 2) slots

-- packed base-1000 so one build returns every figure: Agda aborts a
-- module at its first mismatch, so a tuple of pins leaks one number per
-- build and a sum leaks all of them at once
figures : ℕ
figures = storeM≡ + 1000 * storeS≡ + 1000000 * storeX≡ + 1000000000 * unitM

-- the store reads one at every head and the unit is five, so the floor
-- clears with room -- and the room is what says the factor is not being
-- leaned on
figures≡ : figures ≡ 5001001001
figures≡ = refl

-- AND THE LIFT, which is the whole point of the floor: each row above
-- is a `≤ᵇ` at numerals, and the exported introduction turns it into
-- the target's own conclusion at that program.
fit : ∀ {t} (e : Closed Γ₂ t) → Set
fit e = (storeOf e ≤ᵇ nestUnit e slots) ≡ true

ok : ∀ {t} (e : Closed Γ₂ t) → fit e →
  nestOK? e slots 1 (schedOf e) (stOf e) ≡ true
ok e h =
  nestOK?-intro e slots 1 (schedOf e) (stOf e)
    (≤-trans (≤ᵇ⇒≤ (storeOf e) (nestUnit e slots) (T-to h)) (unit≤cap e))

okM : nestOK? (pM 2) slots 1 (schedOf (pM 2)) (stOf (pM 2)) ≡ true
okM = ok (pM 2) refl

okS : nestOK? (pS 2) slots 1 (schedOf (pS 2)) (stOf (pS 2)) ≡ true
okS = ok (pS 2) refl

okX : nestOK? (pX 2) slots 1 (schedOf (pX 2)) (stOf (pX 2)) ≡ true
okX = ok (pX 2) refl

-- AND THE THREE TARGETS THEMSELVES, WHICH IS WHAT THE FLOOR WAS FOR.
-- Each conclusion is denominated in `nestIncAt`, built over a size the
-- tower seals -- so no side of it reduces and there is no numeral to
-- pin.  What the seal cannot hide is that the increment is a SUMMAND:
-- the store's own reading is computable, each component is under it by
-- a proven converse, and the unit sits under the unit plus anything.
-- So the rows reach the statements as they read, at this program, as
-- proofs rather than readings -- which is the shape a sealed
-- denomination leaves available and the only one it leaves.
underInc : ∀ {t} (e : Closed Γ₂ t) → fit e →
  storeOf e ≤ nestUnit e slots + nestIncAt e slots 0
underInc e h =
  ≤-trans (≤ᵇ⇒≤ (storeOf e) (nestUnit e slots) (T-to h))
          (m≤m+n (nestUnit e slots) (nestIncAt e slots 0))

liveM : Confirms (burst-nest-live (pM 2) slots)
liveM = ≤-trans (storeNest-live≤ (schedOf (pM 2)) (stOf (pM 2)))
                (underInc (pM 2) refl)

nodesM : Confirms (burst-nest-nodes (pM 2) slots)
nodesM = ≤-trans (storeNest-nodes≤ (schedOf (pM 2)) (stOf (pM 2)))
                 (underInc (pM 2) refl)

regsM : Confirms (burst-nest-regs (pM 2) slots)
regsM = ≤-trans (storeNest-regs≤ (schedOf (pM 2)) (stOf (pM 2)))
                (underInc (pM 2) refl)

-- ── the region the floor cannot reach ──────────────────────────────

-- `nestUnit` is `suc (nestDᵉ e + slotsNestSum sl)`, and `nestDᵉ` is
-- the measure that reads zero through a `deferᵉ`.  So a program headed
-- by a defer has a unit of one however deep the body is, while
-- subscribing it mints a live source carrying that body -- the
-- blindness that refuted the live fold, arriving at the FLOOR this
-- file lifts through rather than at a walk.
pD : ℕ → Closed Γ₂ natᵗ
pD k = deferᵉ (deepV k)

deferFigs : ℕ
deferFigs = storeOf (pD 2) + 1000 * nestUnit (pD 2) slots
          + 1000000 * storeOf (pD 4) + 1000000000 * nestUnit (pD 4) slots

deferFigs≡ : deferFigs ≡ 2004002002
deferFigs≡ = refl

-- AND THE FLOOR THAT DOES REACH IT IS NOT INSTANTIABLE, which is why
-- the crossing above is the whole product of these rows.  The repair
-- is `nestCapAt-1-floor`: the instant-one cap dominates the unit PLUS
-- `capsAt`'s own size, and the size reads `sizeᵉ`, which descends into
-- a deferred body.  It is a theorem and not a row -- `capsAt`'s size
-- is sealed through `capsBase`, so its right-hand side does not reduce
-- at any program and no `≤ᵇ` can be taken against it.

-- ── the floor's OTHER summand, which is the sighted one ────────────

-- The conclusion itself cannot be instantiated: the increment is
-- built over `Caps.cSize (capsAt …)`, sealed through `capsBase`, and
-- that is a boundary rather than a gap.  But `capsAt-base-size⁺` and
-- `size≤nestIncAt` are PROVEN and compose into a lower bound on the
-- increment built from `sizeᵉ`, which is sighted exactly where
-- `nestUnit` is blind -- so putting that bound in the increment's
-- place gives a STRICTLY STRONGER claim that does compute.  A green row here is evidence for
-- the postulate; a red one would be a finding about the strong form
-- and not by itself a refutation.
floorOf : ∀ {t} (e : Closed Γ₂ t) → ℕ
floorOf e = nestUnit e slots + (3 + sizeᵉ e + slotsSize slots)

-- the defer-headed family that refuted the unit alone, re-asked here
strongFigs : ℕ
strongFigs = storeOf (pD 4) + 1000 * floorOf (pD 4)
           + 1000000 * storeOf (pD 9) + 1000000000 * floorOf (pD 9)

strongFigs≡ : strongFigs ≡ 56009036004
strongFigs≡ = refl

-- the store rises one per level and the floor four, so the two do not
-- converge; asked again well past where the unit form died
strongFits : ((storeOf (pD 4) ≤ᵇ floorOf (pD 4)) ≡ true)
           × ((storeOf (pD 9) ≤ᵇ floorOf (pD 9)) ≡ true)
           × ((storeOf (pD 20) ≤ᵇ floorOf (pD 20)) ≡ true)
strongFits = refl , refl , refl

-- and the heads the unit form was originally read at, under the
-- strong floor rather than the blind one
strongHeads : ((storeOf (pM 2) ≤ᵇ floorOf (pM 2)) ≡ true)
            × ((storeOf (pS 2) ≤ᵇ floorOf (pS 2)) ≡ true)
            × ((storeOf (pX 2) ≤ᵇ floorOf (pX 2)) ≡ true)
strongHeads = refl , refl , refl

-- AND THE SLOT AXIS, which is the one axis every row above holds at
-- zero and the only remaining one that is TWO-SIDED: slots enter the
-- floor through `slotsSize` and `slotsNestSum`, but they also install
-- state the left side reads, so raising them is not automatically a
-- weakening the way a pure bound-side parameter would be.
richSlots : Slots Γ₂
richSlots = insT 3 2 2

richFloor : ∀ {t} (e : Closed Γ₂ t) → ℕ
richFloor e = nestUnit e richSlots + (3 + sizeᵉ e + slotsSize richSlots)

richStore : ∀ {t} (e : Closed Γ₂ t) → ℕ
richStore e =
  let r = subscribeE (budgetAt e richSlots 0) e root 0 0
                     (sched-init e richSlots) (st-init e)
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

richFigs : ℕ
richFigs = richStore (pD 4) + 1000 * richFloor (pD 4)
         + 1000000 * richStore (pM 2) + 1000000000 * richFloor (pM 2)

richFigs≡ : richFigs ≡ 71004055004
richFigs≡ = refl

-- the axis is LIVE and not decoration: the merge head's store reads
-- one at empty slots and four at these, so the left side moved
richFits : ((richStore (pD 4) ≤ᵇ richFloor (pD 4)) ≡ true)
         × ((richStore (pD 9) ≤ᵇ richFloor (pD 9)) ≡ true)
         × ((richStore (pM 2) ≤ᵇ richFloor (pM 2)) ≡ true)
         × ((richStore (pS 2) ≤ᵇ richFloor (pS 2)) ≡ true)
         × ((richStore (pX 2) ≤ᵇ richFloor (pX 2)) ≡ true)
richFits = refl , refl , refl , refl , refl
