-- THE DRAIN ARM, REACHED AT LAST, AND BY A DOOR THE RUNNING FAMILIES
-- DO NOT HAVE.  `subscribeInner-nest-live` is spent by a drain walking
-- a *All node's QUEUE, and no program family in this tree fills
-- one: an unlimited outer never refuses room, and every inner these
-- families build completes inside its own subscribe burst, so the
-- active count is back at zero before the next arrival is read.  The
-- statement quantifies over an ARBITRARY `st` and `sched`, so a state
-- carrying a parked queue is an instance by construction -- which is
-- the door, and it costs a node install rather than a new program.
--
-- TARGET: subscribeInner-live-size @2242ea

-- WHAT THE ROWS MEASURE IS THE ASYMMETRY THE ARM TURNS ON.  The gate
-- truncates: a queue entry `deferᵉ b` reads as nesting ZERO wherever
-- the node is read, so `nodeNestAt` -- the one state reading the fit's
-- own `G` conjunct is built from -- is blind to the body it is
-- holding.  Draining it SUBSCRIBES it, and that clause mints a live
-- source whose single pending payload IS that body at `obs t`, where
-- `nestDᵛ` reads `nestDᵉ` and the truncation does not apply.  So the
-- live max after the drain is the queued body's own depth exactly,
-- against a pre-state offering zero from every side: an empty incoming
-- live list, a scripted slot telescope summing to zero, and the blind
-- node.  Rows at depth zero through four pin that the after-reading
-- tracks the body one for one while all three before-readings stay
-- flat.

-- THE CONSEQUENCE, AND IT IS THE FINDING: NOTHING BUILT FROM A
-- NESTING READING OF THE STATE CAN PAY HERE.  The two state quantities
-- a grant at this arm is assembled over -- the node's own reading and
-- the incoming values' -- are BOTH zero here, the first because the
-- queue is gated and the second because a drain carries no arrivals.
-- The depth therefore has to arrive by the cap-size route, whose base
-- reads a size that sees THROUGH the gate.  That is a claim about
-- which premise is load-bearing at this arm, and it is what a
-- discharge has to spend.

-- NOT COVERED: the switch and exhaust ops, whose finish arms write a
-- node and drain nothing; a non-empty registry, which routes the reaction to its absorbing arm
-- before the finish is reached at all; and the hypotheses, left
-- standing on every tie -- so a row here is evidence about the
-- CONCLUSION, unconditionally true where it is green and a lead rather
-- than a refutation where it is not.
module Probed.Frame-Drain-Live where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Rx.Prim using (g0; gs; hot)
open import Rx.Exp using (Ctx; Closed; natᵗ; emptyᵉ; mergeAllᵉ; ofᵉ; deferᵉ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; Sched; from-inner; root; stepFrame; sched-init; st-init; mergeAllᵒ; mergeAll-st;
  installNode)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Nest-Store using (liveNest; slotsNestSum)
open import Verify-Budget-Sufficient.Nest-Walk using (nodeNestAt; FaceOK; faceOK)
open import Verify-Budget-Sufficient.Live-Nest-Walk using (subscribeInner-live-size)
open import Probed.Apparatus using (Confirms)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₀ : Closed Γ₁ natᵗ
e₀ = emptyᵉ

-- one `*All` layer per rung, so `nestDᵉ (deep k) ≡ k`
deep : ℕ → Closed Γ₁ natᵗ
deep zero    = emptyᵉ
deep (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

-- a limit-one node holding ONE parked inner and one active lane, so
-- the finish drops the count to zero and the drain finds room
stQ : ℕ → EvalSt e₀
stQ k = installNode 0
  (mergeAll-st {Γ = Γ₁} {t = natᵗ} (just 1) 1 (deferᵉ (deep k) ∷ []) false)
  (st-init e₀)

sc₀ : Sched Γ₁
sc₀ = sched-init e₀ sl₁

drained : ℕ → Sched Γ₁
drained k = proj₁ (proj₂ (proj₂ (proj₂
  (stepFrame {e = e₀} (gs (gs g0)) 0 0 (from-inner mergeAllᵒ 0 7)
             root [] true sc₀ (stQ k)))))

liveMax : Sched Γ₁ → ℕ
liveMax sc = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sc)

-- (queued body's own depth , node's reading of it , live max after)
figures : ℕ → List ℕ
figures k = nestDᵉ (deep k) ∷ nodeNestAt 0 (stQ k) ∷ liveMax (drained k) ∷ []

-- THE PRE-STATE OFFERS NOTHING FROM ANY SIDE.  Both are DEGENERATE on
-- their own -- neither could have come out otherwise once the slots
-- are scripted and the live list is `mkHot` of an empty script -- and
-- they are here because the arm's whole content is what the AFTER
-- reading has to be compared against.
beforeLive : liveMax sc₀ ≡ 0
beforeLive = refl

beforeSlots : slotsNestSum sl₁ ≡ 0
beforeSlots = refl

-- LOAD-BEARING, and the row that could have failed: the drain reaches
-- `subscribeE` on the parked `deferᵉ`, and the minted live source's
-- pending payload is read at `obs natᵗ`.  A gate that truncated on the
-- live side too would put a zero in the third slot.
figures0 : figures 0 ≡ 0 ∷ 0 ∷ 0 ∷ []
figures0 = refl

figures1 : figures 1 ≡ 1 ∷ 0 ∷ 1 ∷ []
figures1 = refl

figures2 : figures 2 ≡ 2 ∷ 0 ∷ 2 ∷ []
figures2 = refl

figures3 : figures 3 ≡ 3 ∷ 0 ∷ 3 ∷ []
figures3 = refl

figures4 : figures 4 ≡ 4 ∷ 0 ∷ 4 ∷ []
figures4 = refl

----------------------------------------------------------------------
-- THE TIE, AT THE SUBSCRIBE ITSELF RATHER THAN AT THE FRAME AROUND
-- IT.  The rows above reach the mint through `stepFrame`, which is how
-- a run gets there; the statement is about `subscribeInner` directly,
-- so the tie applies it at the same parked body, the same empty live
-- list and the same scripted telescope.
--
-- AND THE CAP IS TAKEN AT THE LADDER'S OWN DEPTH, which is what makes
-- the row falsifiable rather than a large number chosen to fit.  The
-- two left summands of the conclusion's join are zero here -- an empty
-- incoming live list and a telescope summing to zero, both pinned
-- above -- so the row reduces to `after ≤ k` exactly at a cap of `k`,
-- and any mint reading one unit more than the body it subscribes fails
-- it.  That is the asymmetry this file exists for, and stating the
-- bound in the cap rather than in a budget is what the statement now
-- says: it is the size side that has to reach through the gate.
--
-- NOT COVERED: the ten premises, left standing and unread -- so the
-- row is evidence about the CONCLUSION, unconditionally true where it
-- is green.  The rungs are two rather than five because the face
-- bundle needs a cap of at least two and the ladder's own depth is the
-- cap, so depths zero and one have no legal instance here.
----------------------------------------------------------------------

cQ : ℕ → Caps
cQ k = caps k 4 1

faceQ2 : FaceOK (cQ 2) sl₁
faceQ2 = faceOK (≤ᵇ⇒≤ _ _ tt) (≤ᵇ⇒≤ _ _ tt) refl (≤ᵇ⇒≤ _ _ tt)

faceQ4 : FaceOK (cQ 4) sl₁
faceQ4 = faceOK (≤ᵇ⇒≤ _ _ tt) (≤ᵇ⇒≤ _ _ tt) refl (≤ᵇ⇒≤ _ _ tt)

tieLive2 : Confirms
  (subscribeInner-live-size (cQ 2) sl₁ 2 2 0
     (gs g0) mergeAllᵒ 0 root 0 0 (deep 2) sc₀ (stQ 2) ⦃ faceQ2 ⦄)
tieLive2 _ _ _ _ _ _ _ _ _ _ = ≤ᵇ⇒≤ _ _ tt

tieLive4 : Confirms
  (subscribeInner-live-size (cQ 4) sl₁ 4 4 0
     (gs g0) mergeAllᵒ 0 root 0 0 (deep 4) sc₀ (stQ 4) ⦃ faceQ4 ⦄)
tieLive4 _ _ _ _ _ _ _ _ _ _ = ≤ᵇ⇒≤ _ _ tt
