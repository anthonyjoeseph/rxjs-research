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
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Rx.Prim using (Gas; g0; gs; hot)
open import Rx.Exp using (Ctx; Closed; obs; natᵗ; emptyᵉ; mergeAllᵉ; ofᵉ; deferᵉ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; Sched; Path; _↠_; from-inner; thru-outer; root; stepFrame;
  subscribeInner; sched-init; st-init; mergeAllᵒ; mergeAll-st; installNode; NodeId; take-f)
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

----------------------------------------------------------------------
-- THE TWO AXES THE LADDER LEAVES AT THEIR FLOOR, and both turn out to
-- be answerable rather than uncovered.
--
-- THE LEVEL IS BOUND-SIDE AND MONOTONE, so `Lv = 0` is the TIGHTEST
-- point rather than the cheapest.  It does not occur under the
-- subscribe at all: its occurrences are in the premises and in the
-- bound's own cap size, which climbs with the level by
-- `frameStep-mono-j`.  A sweep over it could not have failed, so no
-- row is spent on it.
--
-- AND THE PATH IS MEASURED INERT, which is the half no type decides.
-- `κ` IS measure-side -- it occurs under the subscribe and nowhere in
-- the bound -- so a row over it genuinely could fail.  It does not: a
-- two-frame path reads exactly what `root` reads at both rungs,
-- because a subscribe INSTALLS and does not deliver.  The mint is the
-- entry's own body, and the frames only record where its later values
-- will go.
----------------------------------------------------------------------

gasOf : ℕ → Gas
gasOf zero    = g0
gasOf (suc k) = gs (gasOf k)

κT : Path Γ₁ natᵗ natᵗ
κT = take-f 9 ↠ (take-f 8 ↠ root)

-- the path's own merge outer, installed with room
outerNid : NodeId
outerNid = 3

stO : EvalSt e₀
stO = installNode outerNid
  (mergeAll-st {Γ = Γ₁} {t = natᵗ} nothing 0 [] false)
  (st-init e₀)

mintAt : ∀ {u} → ℕ → Path Γ₁ u natᵗ → Closed Γ₁ u → ℕ
mintAt k κ o = liveMax (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
  (subscribeInner (gasOf (k + 6)) mergeAllᵒ 0 κ 0 0 o sc₀ stO))))))

-- (root , two frames) at one rung, then at another
pathFigures : ℕ → List ℕ
pathFigures k = mintAt k root (deferᵉ (deep k))
              ∷ mintAt k κT   (deferᵉ (deep k)) ∷ []

-- LOAD-BEARING: the frames are between the subscribed entry and the
-- root, so a mint that read anything of the path would move the second
-- number off the first.
pathFigures1 : pathFigures 1 ≡ 1 ∷ 1 ∷ []
pathFigures1 = refl

pathFigures4 : pathFigures 4 ≡ 4 ∷ 4 ∷ []
pathFigures4 = refl

-- AND A PATH FRAME THAT WOULD MINT ON ITS OWN ACCOUNT NEVER FIRES
-- HERE, which is why the rows above are not merely a statement about
-- `take-f`.  The entry is a stream of STREAMS and the frame under it
-- is a merge outer with room, so a DELIVERY through this path would
-- subscribe the emitted observable and mint its depth.  Subscribing
-- reads zero at both rungs instead.
oo : ℕ → Closed Γ₁ (obs natᵗ)
oo k = ofᵉ (strmᵗ (deferᵉ (deep k)) ∷ [])

κO : Path Γ₁ (obs natᵗ) natᵗ
κO = thru-outer mergeAllᵒ outerNid ↠ root

outerIdle : mintAt 1 κO (oo 1) ⊔ mintAt 4 κO (oo 4) ≡ 0
outerIdle = refl

-- and the statement itself at a non-root path, at the rung whose cap
-- is the ladder's own depth, so the margin here is zero too
tieLivePath : Confirms
  (subscribeInner-live-size (cQ 4) sl₁ 4 4 0
     (gasOf 10) mergeAllᵒ 0 κT 0 0 (deferᵉ (deep 4)) sc₀ stO ⦃ faceQ4 ⦄)
tieLivePath _ _ _ _ _ _ _ _ _ _ = ≤ᵇ⇒≤ _ _ tt
