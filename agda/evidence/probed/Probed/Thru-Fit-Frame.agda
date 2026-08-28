-- ══════════════════════════════════════════════════════════════════
-- THE FRAME GRANT'S `+ W` TERM AGAINST THE `+ nestU S U` TERM THE
-- MACHINERY ELSEWHERE SPENDS.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: thruConsume-fit @779fee
--
-- WHAT IS BEING TESTED.  The grant in `thruConsume-fit` is
--   nestFac (cSize c) W * (M + W)
-- and the frame spends it at M = nodesMax st ⊔ nestDᵛˢ vals, which is
-- the M every row here takes,
-- while the `nestB-at` bound the machinery elsewhere spends carries
-- `+ nestU S U` instead, where `nestU S U = (suc S) * U` and
-- `U = nestUnit e sl`.  For small W and large cSize S, the gap
-- `nestU S U - W = S * U + U - W` can be large.  The question is
-- whether the actual per-step delivery from ONE `thruConsume` call
-- ever exceeds the grant.
--
-- WHAT THE ROWS ACTUALLY REACH, and it is less than the axis asked
-- for.  Every row is DEGENERATE, and two of the three conjuncts are
-- degenerate in the strongest sense: `figA≡` and its siblings pin the
-- nodes-side LHS at ZERO on all five rows, so conjuncts (2) and (3)
-- read `0 ≤ᵇ _` and could not have failed whatever the grant was.
-- Only conjunct (1) carries a number, and it is 2 against a grant
-- whose factor `((2 ^ S) ^ 2) ^ S` runs to millions of digits at the
-- tightest cap this family admits.  So the file measures that the
-- grant HOLDS here, not that this axis can press it.
--
-- WHY THE AXIS CANNOT PRESS IT.  Raising `nestU S U` does not move
-- the grant at all -- `nestU` does not occur in it -- so the sweep
-- changes only the program, and what it changes there is the
-- arrival's own depth.  A refutation needs a step that delivers MORE
-- nesting than its arrival carried, by more than the `+ W` addend;
-- the `dup` family never does, and building one is what a later
-- attempt on this statement has to do.  That the delivery is bounded
-- by `nodesMax st ⊔ nestDᵛˢ vals` in general is a CONJECTURE these
-- rows are consistent with and not a result -- were it established,
-- the statement would follow in a line.
--
-- WHAT IS NOT COVERED.  Only the three programs for which
-- thruConsume produces a non-empty burst are reached; the sealed
-- `nestFac` is replaced by its open recurrence `nestFacᶜ` (which
-- `nestFac-def` equates to the sealed one).  Conjunct (3) is pinned
-- pointwise at the node ids of the installed nodes (7 for mergeAll,
-- 8 for switch, 9 for exhaust) rather than universally quantified.
-- ══════════════════════════════════════════════════════════════════
module Probed.Thru-Fit-Frame where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ;
         varᵗ; caseᵗ; inlᵗ; syncSizeᵛ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; thru-outer;
         mergeAllᵒ; switchᵒ; exhaustᵒ; installNode; mergeAll-st; switch-st;
         exhaust-st; thruConsume)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; nodesMax; nodeNestAt; nestClosOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

-- ── harness setup (shared with Probed.Thru-Step-Indexed) ─────────

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

-- the duplicating step function, verbatim from the witness that
-- killed the one-index form
dup : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

E : ℕ → Val Γ₂ (obs natᵗ)
E zero    = ofᵉ (nat̂ 0 ∷ [])
E (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (E k) ∷ []))

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- the arrival: an obs (obs natᵗ) at depth k
arr : ℕ → Val Γ₂ (obs (obs natᵗ))
arr k = mapᵉ dup (ofᵉ (strmᵗ (E k) ∷ []))

κ : Path Γ₂ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

sched₀ : Sched Γ₂
sched₀ = sched-init prog slots

-- installed states, one per operator
stM stS stX : EvalSt prog
stM = installNode 7 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) (st-init prog)
stS = installNode 8 (switch-st nothing false) (st-init prog)
stX = installNode 9 (exhaust-st false false) (st-init prog)

-- ── cap, tightest one valCaps? admits for each arr depth ─────────

-- For arr k (no deferᵉ), syncSizeᵉ = sizeᵉ, so
-- sizeᵛ (obs (obs natᵗ)) (arr k) = syncSizeᵛ (obs (obs natᵗ)) (arr k).
-- Therefore valCaps? holds exactly at this cap.
capF : ℕ → Caps
capF k = caps (syncSizeᵛ (obs (obs natᵗ)) (arr k))
              (pWᵛ 2 slots (obs (obs natᵗ)) (arr k))
              0

-- ── sealed nestFac, written from its own recurrence ──────────────

-- `nestFac-def : nestFac S W ≡ ((2 ^ S) ^ suc W) ^ S` equates this
-- to the sealed family in Nest-Cap.  Rows are stated against this
-- open form rather than through the seal.
nestFacᶜ : ℕ → ℕ → ℕ
nestFacᶜ S W = ((2 ^ S) ^ suc W) ^ S

-- `nestU S U = suc S * U` (also sealed); the gap this file attacks
nestUᶜ : ℕ → ℕ → ℕ
nestUᶜ S U = suc S * U

-- ── the grant at an explicit W (independent of capF.cWid) ────────

G : ℕ → ℕ → ℕ → ℕ   -- S  W  B
G S W B = nestFacᶜ S W * (B + W)

-- ── base quantity: nodesMax st ⊔ nestDᵛˢ [arr k] ─────────────────

BM : ℕ → ℕ
BM k = nodesMax stM ⊔ nestDᵛˢ (arr k ∷ [])

-- ── rc helpers ───────────────────────────────────────────────────

rcM rcS rcX : ℕ → _
rcM k = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr k) sched₀ stM
rcS k = thruConsume gasBig switchᵒ  8 κ 0 0 (arr k) sched₀ stS
rcX k = thruConsume gasBig exhaustᵒ 9 κ 0 0 (arr k) sched₀ stX

-- ── nestUnit pin, and the gap it describes ────────────────────────

-- nestUnit prog slots = suc (nestDᵉ prog + slotsNestSum slots).
-- Pinned by refl so the gap is a number, not a claim.
unitPin : nestUnit prog slots ≡ 2
unitPin = refl

-- The gap nestUᶜ S 1 - W at W = 1: for cSize S large, nestU = S+1 >> 1.
-- This pin shows the magnitude at the tightest cap (arr 1).
gapFig : ℕ × ℕ   -- (nestUᶜ S 1, W = 1)
gapFig = nestUᶜ (Caps.cSize (capF 1)) 1 , 1

gapFig≡ : gapFig ≡ (22 , 1)
gapFig≡ = refl

-- ── premises (held by refl) ───────────────────────────────────────

premM1 : capsOK? (capF 1) sched₀ stM ≡ true
premM1 = refl

premV1 : valCaps? (capF 1) slots (obs (obs natᵗ)) (arr 1) ≡ true
premV1 = refl

premM3 : capsOK? (capF 3) sched₀ stM ≡ true
premM3 = refl

premV3 : valCaps? (capF 3) slots (obs (obs natᵗ)) (arr 3) ≡ true
premV3 = refl

premS1 : capsOK? (capF 1) sched₀ stS ≡ true
premS1 = refl

premX1 : capsOK? (capF 1) sched₀ stX ≡ true
premX1 = refl

-- the resolved-size premise, which the arrivals here meet at the same
-- cap: no `arr` names a slot, so the size read through the telescope
-- is the size read off the term
premC1 : slotsSize slots ≤ Caps.cSize (capF 1)
premC1 = ≤ᵇ⇒≤ _ _ tt

premK1 : all (nestClosOK? (capF 1) slots) (arr 1 ∷ []) ≡ true
premK1 = refl

premC3 : slotsSize slots ≤ Caps.cSize (capF 3)
premC3 = ≤ᵇ⇒≤ _ _ tt

premK3 : all (nestClosOK? (capF 3) slots) (arr 3 ∷ []) ≡ true
premK3 = refl

-- ── combined figure pins (delivery LHS for all three conjuncts) ──

-- ROW A: W = 1, arr 1, mergeAll.
-- DEGENERATE: the grant factor nestFacᶜ S 1 = ((2^S)^2)^S at
-- S = Caps.cSize (capF 1) towers over the delivery.  The additive
-- gap nestUᶜ S 1 - 1 = S is large but irrelevant: no step whose
-- arrival has depth B can deliver more than B per conjunct.
-- Kept because the W = 1 / large S combination is the tightest this
-- axis reaches, and the gap figure above says how tight.
-- figA pins the three conjuncts' LHS (delivery values); G is not
-- shown because nestFacᶜ 21 1 has millions of digits.
figA : ℕ × ℕ × ℕ
figA = nestDᵛˢ (proj₁ (rcM 1))
     , nodesMax (proj₂ (proj₂ (proj₂ (rcM 1))))
     , nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 1))))

figA≡ : figA ≡ (2 , 0 , 0)
figA≡ = refl

-- conjunct (1): nestDᵛˢ emitted ≤ G
fitA1 : (nestDᵛˢ (proj₁ (rcM 1))
          ≤ᵇ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitA1 = refl

-- conjunct (2): nodesMax new state ≤ nodesMax stM ⊔ G
fitA2 : (nodesMax (proj₂ (proj₂ (proj₂ (rcM 1))))
          ≤ᵇ nodesMax stM ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitA2 = refl

-- conjunct (3): nodeNestAt 7 new state ≤ nodeNestAt 7 stM ⊔ G
-- pinned at j = 7, the installed mergeAll node
fitA3 : (nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 1))))
          ≤ᵇ nodeNestAt 7 stM ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitA3 = refl

-- ROW B: W = 1, arr 3, mergeAll.
-- DEGENERATE: deeper arrival, same tightness argument.  Kept so the
-- file covers more than the shallowest input.
figB : ℕ × ℕ × ℕ
figB = nestDᵛˢ (proj₁ (rcM 3))
     , nodesMax (proj₂ (proj₂ (proj₂ (rcM 3))))
     , nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 3))))

figB≡ : figB ≡ (6 , 0 , 0)
figB≡ = refl

fitB1 : (nestDᵛˢ (proj₁ (rcM 3))
          ≤ᵇ G (Caps.cSize (capF 3)) 1 (BM 3)) ≡ true
fitB1 = refl

fitB2 : (nodesMax (proj₂ (proj₂ (proj₂ (rcM 3))))
          ≤ᵇ nodesMax stM ⊔ G (Caps.cSize (capF 3)) 1 (BM 3)) ≡ true
fitB2 = refl

fitB3 : (nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 3))))
          ≤ᵇ nodeNestAt 7 stM ⊔ G (Caps.cSize (capF 3)) 1 (BM 3)) ≡ true
fitB3 = refl

-- ROW C: W = 10, arr 1, mergeAll.
-- DEGENERATE on the contrast axis: larger W gives a much larger grant.
-- Kept so the file names the W-large end of the axis alongside the
-- W-small end, making the gradient a number rather than a claim.
-- Same delivery as row A (rcM 1); only W changes, not the behavior.
figC : ℕ × ℕ × ℕ
figC = nestDᵛˢ (proj₁ (rcM 1))
     , nodesMax (proj₂ (proj₂ (proj₂ (rcM 1))))
     , nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 1))))

figC≡ : figC ≡ (2 , 0 , 0)
figC≡ = refl

fitC1 : (nestDᵛˢ (proj₁ (rcM 1))
          ≤ᵇ G (Caps.cSize (capF 1)) 10 (BM 1)) ≡ true
fitC1 = refl

fitC2 : (nodesMax (proj₂ (proj₂ (proj₂ (rcM 1))))
          ≤ᵇ nodesMax stM ⊔ G (Caps.cSize (capF 1)) 10 (BM 1)) ≡ true
fitC2 = refl

fitC3 : (nodeNestAt 7 (proj₂ (proj₂ (proj₂ (rcM 1))))
          ≤ᵇ nodeNestAt 7 stM ⊔ G (Caps.cSize (capF 1)) 10 (BM 1)) ≡ true
fitC3 = refl

-- ROW D: W = 1, arr 1, switch.
-- DEGENERATE: same finding applies at the switch operator.
figD : ℕ × ℕ × ℕ
figD = nestDᵛˢ (proj₁ (rcS 1))
     , nodesMax (proj₂ (proj₂ (proj₂ (rcS 1))))
     , nodeNestAt 8 (proj₂ (proj₂ (proj₂ (rcS 1))))

figD≡ : figD ≡ (2 , 0 , 0)
figD≡ = refl

fitD1 : (nestDᵛˢ (proj₁ (rcS 1))
          ≤ᵇ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitD1 = refl

fitD2 : (nodesMax (proj₂ (proj₂ (proj₂ (rcS 1))))
          ≤ᵇ nodesMax stS ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitD2 = refl

fitD3 : (nodeNestAt 8 (proj₂ (proj₂ (proj₂ (rcS 1))))
          ≤ᵇ nodeNestAt 8 stS ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitD3 = refl

-- ROW E: W = 1, arr 1, exhaust.
-- DEGENERATE: same finding applies at the exhaust operator.
figE : ℕ × ℕ × ℕ
figE = nestDᵛˢ (proj₁ (rcX 1))
     , nodesMax (proj₂ (proj₂ (proj₂ (rcX 1))))
     , nodeNestAt 9 (proj₂ (proj₂ (proj₂ (rcX 1))))

figE≡ : figE ≡ (2 , 0 , 0)
figE≡ = refl

fitE1 : (nestDᵛˢ (proj₁ (rcX 1))
          ≤ᵇ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitE1 = refl

fitE2 : (nodesMax (proj₂ (proj₂ (proj₂ (rcX 1))))
          ≤ᵇ nodesMax stX ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitE2 = refl

fitE3 : (nodeNestAt 9 (proj₂ (proj₂ (proj₂ (rcX 1))))
          ≤ᵇ nodeNestAt 9 stX ⊔ G (Caps.cSize (capF 1)) 1 (BM 1)) ≡ true
fitE3 = refl

-- ── the ITERATED region: a list, not a singleton ─────────────────

-- Every row above consumes ONE value, and the grant is computed from
-- the state that value arrives at.  `thruFitOK` walks a LIST and
-- re-uses the SAME `G` at every step, so the second consume is read
-- at the state the first LEFT while the grant is still frozen at the
-- first's.  That is the one axis here that moves the measure side
-- without moving the bound side, and it is what these rows take.

-- the chained states: consume, then consume again at the exit
ch1M : ℕ → _
ch1M k = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr k)
           (proj₁ (proj₂ (proj₂ (rcM k)))) (proj₂ (proj₂ (proj₂ (rcM k))))

ch2M : ℕ → _
ch2M k = thruConsume gasBig mergeAllᵒ 7 κ 0 0 (arr k)
           (proj₁ (proj₂ (proj₂ (ch1M k)))) (proj₂ (proj₂ (proj₂ (ch1M k))))

-- the grant's base term at the list, NOT at the last value
BM2 : ℕ → ℕ
BM2 k = nodesMax stM ⊔ nestDᵛˢ (arr k ∷ arr k ∷ [])

BM4 : ℕ → ℕ
BM4 k = nodesMax stM ⊔ nestDᵛˢ (arr k ∷ arr k ∷ arr k ∷ arr k ∷ [])

premK2-3 : all (nestClosOK? (capF 3) slots) (arr 3 ∷ arr 3 ∷ []) ≡ true
premK2-3 = refl

-- ROW F: W = 2, two copies of arr 3, mergeAll.  LOAD-BEARING on the
-- second step's conjunct (1): `figF` reads the SECOND consume's
-- delivery, taken at the state the first left, against a grant whose
-- base term `BM2 3` was read before either ran.  It fails if a
-- consume delivers more when the state under it has already been
-- raised -- which is the shape the single-value rows cannot see.
figF : ℕ × ℕ × ℕ
figF = nestDᵛˢ (proj₁ (ch1M 3))
     , nodesMax (proj₂ (proj₂ (proj₂ (ch1M 3))))
     , nodeNestAt 7 (proj₂ (proj₂ (proj₂ (ch1M 3))))

fitF1 : (nestDᵛˢ (proj₁ (ch1M 3))
          ≤ᵇ G (Caps.cSize (capF 3)) 2 (BM2 3)) ≡ true
fitF1 = refl

fitF2 : (nodesMax (proj₂ (proj₂ (proj₂ (ch1M 3))))
          ≤ᵇ nodesMax stM ⊔ G (Caps.cSize (capF 3)) 2 (BM2 3)) ≡ true
fitF2 = refl

fitF3 : (nodeNestAt 7 (proj₂ (proj₂ (proj₂ (ch1M 3))))
          ≤ᵇ nodeNestAt 7 stM ⊔ G (Caps.cSize (capF 3)) 2 (BM2 3)) ≡ true
fitF3 = refl

-- ROW G: the third consume in the same chain, W = 4.  Same axis one
-- step further out, so a drift that only shows after two raisings is
-- reached too.
figG : ℕ × ℕ × ℕ
figG = nestDᵛˢ (proj₁ (ch2M 3))
     , nodesMax (proj₂ (proj₂ (proj₂ (ch2M 3))))
     , nodeNestAt 7 (proj₂ (proj₂ (proj₂ (ch2M 3))))

fitG1 : (nestDᵛˢ (proj₁ (ch2M 3))
          ≤ᵇ G (Caps.cSize (capF 3)) 4 (BM4 3)) ≡ true
fitG1 = refl

fitG2 : (nodesMax (proj₂ (proj₂ (proj₂ (ch2M 3))))
          ≤ᵇ nodesMax stM ⊔ G (Caps.cSize (capF 3)) 4 (BM4 3)) ≡ true
fitG2 = refl

fitG3 : (nodeNestAt 7 (proj₂ (proj₂ (proj₂ (ch2M 3))))
          ≤ᵇ nodeNestAt 7 stM ⊔ G (Caps.cSize (capF 3)) 4 (BM4 3)) ≡ true
fitG3 = refl

figF≡ : figF ≡ (6 , 0 , 0)
figF≡ = refl

figG≡ : figG ≡ (6 , 0 , 0)
figG≡ = refl
