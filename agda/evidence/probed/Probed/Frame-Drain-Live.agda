-- THE DRAIN ARM, REACHED AT LAST, AND BY A DOOR THE RUNNING FAMILIES
-- DO NOT HAVE.  `mergeAllDrain-nest-live` subscribes out
-- of a *All node's QUEUE, and no program family in this tree fills
-- one: an unlimited outer never refuses room, and every inner these
-- families build completes inside its own subscribe burst, so the
-- active count is back at zero before the next arrival is read.  The
-- statement quantifies over an ARBITRARY `st` and `sched`, so a state
-- carrying a parked queue is an instance by construction -- which is
-- the door, and it costs a node install rather than a new program.
--
-- TARGET: mergeAllDrain-nest-live @ab1809

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

-- THE CONSEQUENCE FOR THE FIT, AND IT IS THE FINDING: `U` IS THE ONLY
-- THING THAT CAN PAY HERE, AND IT CANNOT REACH THE DEPTH THROUGH `G`.
-- `InnerΦFit` bounds `U` through a `G` above `nodeNestAt allNid st ⊔
-- nestDᵛˢ vals`, and at this arm both summands are zero -- the queue is
-- gated and the drain carries no incoming values.  The depth therefore
-- has to arrive through the cap-size route, whose base reads a size
-- that sees THROUGH the gate, and not through any nesting reading of
-- the state.  That is a claim about which conjunct is load-bearing at
-- this arm, and it is what a discharge has to spend.

-- NOT COVERED: the switch and exhaust ops, whose finish arms write a
-- node and drain nothing; a queue deeper than one entry, where the
-- drain's own recursion is read rather than a single subscription; a
-- non-empty registry, which routes the reaction to its absorbing arm
-- before the finish is reached at all; and the hypotheses, which are a
-- Σ carrying a universally quantified numeric conjunct and are not
-- dischargeable by computation -- so a row here is evidence about the
-- CONCLUSION, unconditionally true where it is green and a lead rather
-- than a refutation where it is not.
module Probed.Frame-Drain-Live where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Rx.Prim using (g0; gs; hot)
open import Rx.Exp using (Ctx; Closed; natᵗ; emptyᵉ; mergeAllᵉ; ofᵉ; deferᵉ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; Sched; from-inner; root; stepFrame; sched-init; st-init; mergeAllᵒ; mergeAll-st;
  installNode)
open import Verify-Budget-Sufficient.Nest-Store using (liveNest; slotsNestSum)
open import Verify-Budget-Sufficient.Nest-Walk using (nodeNestAt)

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
