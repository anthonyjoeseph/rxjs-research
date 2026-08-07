-- INNERFINISH-CONCAT-FACE ASSEMBLY PROBE (2026-08-07).
--
-- Goal: discharge P3, `innerFinish-concat-face-core` at
-- Caps-Face.agda:6377.
--
-- CLASSIFICATION: LANDING → Verify-Budget-Sufficient/Caps-Face.agda
--
-- ─────────────────────────────────────────────────────────────────
-- FINDING: THE POSTULATE CARRIES TWO MISSING HYPOTHESES
-- ─────────────────────────────────────────────────────────────────
--
-- The proof path through `innerFinish-caps` (Subscribe-Face) is the
-- only available route for the concat+yes drain case.  That function
-- requires:
--
--   (H1) slotsSize sl ≤ Caps.cSize c
--        — for `obsList→mList-strict` and `concatDrain-caps`
--
--   (H2) depthFin g concatᵒ allNid inst κ id now vals sched st
--            (lookupNode allNid (EvalSt.nodes st)) ≤ d
--        — because `innerFinish-caps`'s concat+yes branch does
--          `with dep | dpt′` and the `| zero | ()` arm makes it
--          unreachable at dep = 0 (depthFin = suc(depthDrain) ≥ 1).
--          Its budget conjunct lands in `fLvlD S W dep j`, and
--          widening to `fLvlD S W d j` requires dep ≤ d.
--
-- Neither hypothesis is in the face chain today
-- (stepFrame-face → innerReact-face → innerFinish-face →
--  innerFinish-concat-face → innerFinish-concat-face-core).
-- Both ARE available at the top (`caps-tick`):
--
--   • H1: from capsAt-base-size (Caps.cSize (capsAt e sl id)
--         = 2 + sizeᵉ e + slotsSize sl ≥ slotsSize sl).
--   • H2: a depth-fuel ruling: depthFin ... ≤ capsH e sl id.
--         This is the structural complement of innerFinish-caps's
--         own depth parameter and needs to be threaded from caps-tick.
--
-- ─────────────────────────────────────────────────────────────────
-- ASSEMBLY STRUCTURE
-- ─────────────────────────────────────────────────────────────────
--
-- `innerFinish-concat-face-core` reduces to a case split on
-- lookupNode.  Six arms of the dispatch:
--   • nothing, scan-st, take-st, merge-st, switch-st, exhaust-st
--     → `innerFinish-face-keep` (j′ = 0, any d)
--   • concat-st with type mismatch  → `innerFinish-face-keep`
--   • concat-st with type match     → the drain case (new sub-postulate)
--
-- The new sub-postulate `innerFinish-concat-drain-face` carries H1
-- and H2 and is provable via `innerFinish-caps`:
--
--   innerFinish-concat-drain-face c d j g allNid inst κ id now vals
--       sl sched st 2≤S 1≤R slEq slC inv pC lC vC H1 H2
--     = let IFc = innerFinish-caps c d (frameBud c j) j g concatᵒ
--                   ... 2≤S 1≤R slEq slC H1 inv pC lC vC ≤-refl H2
--       in proj₁ IFc
--        , fLvlD-mono (proj₂ (proj₂ (proj₂ (proj₂ IFc)))) (by H2)
--        , proj₁ (proj₂ IFc) , proj₁ (proj₂ (proj₂ IFc))
--   (modulo field names in innerFinish-caps's return Σ)
--
-- PROBE APPROACH: import Caps-Face (cached, ~6 s) and
-- Subscribe-Face (cached).  Build the assembly here; leave
-- `innerFinish-concat-drain-face` as a postulate.
-- ─────────────────────────────────────────────────────────────────
module InnerFinish-Concat-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; +-identityʳ)
open import Data.List using (List; []; _∷_; all)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; Tick; Id; InstEmit; InstEvent)
open import Rx.Exp  using (Ty; Ctx; Closed; _≟ᵗ_)
open import Rx.Evaluator
  using (NodeId; NodeState; scan-st; take-st; merge-st; concat-st;
         switch-st; exhaust-st; lookupNode;
         Slots; Sched; EvalSt; Path; Val; Stream;
         AllOp; concatᵒ; slotsSize;
         fLvlD; innerFinish)

-- Caps-Face: cached interface — does NOT recheck, deserializes in ~6 s.
-- Import everything the assembly needs in ONE block.
open import Verify-Budget-Sufficient.Caps-Face
  using (Caps; frameStep; capsOK?; valsCaps?; valCaps?; slotsCaps?;
         eventCaps?; burstCaps?; obsCaps?;
         FrameFace; face-lift; fLvl≤fLvlD;
         innerFinish-face-keep;
         lookupNode-caps; capsOK?-nodeSz; capsOK?-nodeWid;
         NodeCaps;
         pathSz?; pathLen)

-- Subscribe-Face: cached interface (just for innerFinish-caps type)
-- Not called directly in the assembly — the sub-postulate delegates to it.
-- open import Verify-Budget-Sufficient.Subscribe-Face using (innerFinish-caps)

-- Caps-Depth: for depthFin type
open import Verify-Budget-Sufficient.Caps-Depth using (depthFin)

-- ─────────────────────────────────────────────────────────────────
-- § 1.  THE NEW SUB-POSTULATE: the drain case with its two real
--       hypotheses.  This is the GENUINE GAP left after the assembly.
--
-- Once H1 and H2 are threaded to the face chain, this becomes a
-- direct call to `innerFinish-caps`:
--
--   innerFinish-concat-drain-face c d j g allNid inst κ id now vals
--       sl sched st 2≤S 1≤R slEq slC inv pC lC vC H1 H2
--     =
--     let IFc = innerFinish-caps c d (frameBud c j) j g concatᵒ
--                   allNid inst κ id now vals sl sched st
--                   2≤S 1≤R slEq slC H1 inv pC lC vC ≤-refl H2
--         j′  = proj₁ IFc
--     in j′
--      , -- budget: innerFinish-caps gives j + j′ ≤ fLvlD S W d j ✓
--        proj₂ (proj₂ (proj₂ (proj₂ IFc)))
--      , -- capsOK?:
--        proj₁ (proj₂ IFc)
--      , -- valsCaps?:
--        proj₁ (proj₂ (proj₂ IFc))
-- ─────────────────────────────────────────────────────────────────
postulate
  innerFinish-concat-drain-face :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    -- standard face hypotheses
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    -- H1: slotsSize bound (needed for obsList→mList-strict / concatDrain-caps)
    slotsSize sl ≤ Caps.cSize c →
    -- H2: depth bound (needed because innerFinish-caps's concat+yes branch is
    --     unreachable at dep = 0 and its result lives in fLvlD S W dep j;
    --     widening to fLvlD S W d j requires depthFin ... ≤ d)
    depthFin g concatᵒ allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ d →
    FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st
                          (lookupNode allNid (EvalSt.nodes st)))

-- ─────────────────────────────────────────────────────────────────
-- § 2.  THE ASSEMBLY: `innerFinish-concat-face-core` as a REAL
--       DEFINITION using the sub-postulate for the drain arm.
--
-- The five toolkit functions (burstCaps?-∷ etc.) are not consumed
-- here — the drain arm delegates to the sub-postulate which calls
-- innerFinish-caps directly.  They remain as parameters so the call
-- site (`innerFinish-concat-face`) is unchanged; an unused-argument
-- warning is expected.
--
-- THE NEW HYPOTHESES H1 and H2 are appended after the existing 8.
-- Call sites (innerFinish-concat-face, innerFinish-face,
-- innerReact-face, stepFrame-face) must also gain them.
-- ─────────────────────────────────────────────────────────────────
innerFinish-concat-face-core :
    -- burstCaps?-∷  (Caps-Face:3608)
    (∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
      (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
      all (eventCaps? c sl) (InstEmit.events em) ≡ true →
      burstCaps? c sl str ≡ true →
      burstCaps? c sl (em ∷ str) ≡ true) →
    -- valsCaps?-slots
    (∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
      (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
      all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true) →
    -- eventsCaps?-slots
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
      all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true) →
    -- burstCaps?-slots
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (str : Stream Γ u) → sl′ ≡ sl →
      burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true) →
    -- obsListCaps?-slots
    (∀ {n} {Γ : Ctx n} {s} {c : Caps} {sl sl′ : Slots Γ}
      (q : List (Closed Γ s)) → sl′ ≡ sl →
      all (obsCaps? c sl) q ≡ true → all (obsCaps? c sl′) q ≡ true) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    -- H1 and H2 — the two new hypotheses to be threaded into the face chain
    slotsSize sl ≤ Caps.cSize c →
    depthFin g concatᵒ allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ d →
    FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st
                          (lookupNode allNid (EvalSt.nodes st)))
-- CASE SPLIT on lookupNode.  Five arms are trivially j′ = 0 via
-- innerFinish-face-keep.  The sixth (concat+yes) delegates to the
-- drain sub-postulate.
innerFinish-concat-face-core _ _ _ _ _ _ _ _ _ _ _ _ c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) allNid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing               | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (scan-st _)      | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (take-st _)      | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (merge-st _ _)   | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (switch-st _ _)  | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (exhaust-st _ _) | _ = innerFinish-face-keep c d j sl vals false sched st inv vC
... | just (concat-st {w} q act od) | (bn , wn) with w ≟ᵗ s
...   | no _     = innerFinish-face-keep c d j sl vals false sched st inv vC
...   | yes refl =
  innerFinish-concat-drain-face c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt
