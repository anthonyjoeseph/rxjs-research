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
--   (H2) depthFin g concatᵒ allNid inst κ id now vals sched st nd ≤ d
--        — where nd = lookupNode allNid (EvalSt.nodes st)
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
--   • H1: from capsAt-base-size.
--   • H2: a depth-fuel ruling: depthFin ... ≤ capsH e sl id.
--
-- ─────────────────────────────────────────────────────────────────
-- ASSEMBLY DESIGN CHOICE: nd taken explicitly, no second with
-- ─────────────────────────────────────────────────────────────────
--
-- Doing `with w ≟ᵗ s` inside the assembly causes a type mismatch:
-- after that second with-abstraction, `dpt`'s type reduces to
-- `suc (depthDrain ...) ≤ d` while the sub-postulate evaluating
-- `depthFin ... (just (concat-st q act od))` fresh yields
-- `depthFinC ... (s ≟ᵗ s) ≤ d`, and Agda can't equate these
-- (for variable `s`, `s ≟ᵗ s` is not definitionally `yes refl`).
--
-- Fix: the sub-postulate `innerFinish-concat-face-go` takes the node
-- result `nd` EXPLICITLY and H2 in terms of `nd` directly.  The
-- assembly passes `nd = lookupNode allNid (EvalSt.nodes st)` WITHOUT
-- any second `with` abstraction, so `dpt`'s type and H2's expected
-- type are literally the same expression.  The sub-postulate handles
-- the `w ≟ᵗ s` dispatch (and every other node case) internally.
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
open import Rx.Exp  using (Ty; Ctx; Closed; Val; _≟ᵗ_)
open import Rx.Evaluator
  using (NodeId; NodeState; scan-st; take-st; merge-st; concat-st;
         switch-st; exhaust-st; lookupNode;
         Slots; Sched; EvalSt; Path; Stream;
         AllOp; concatᵒ; slotsSize;
         fLvlD; innerFinish)

-- Caps-Face: cached interface — does NOT recheck, deserializes in ~6 s.
open import Verify-Budget-Sufficient.Caps-Face
  using (Caps; frameStep; capsOK?; valsCaps?; valCaps?; slotsCaps?;
         eventCaps?; burstCaps?; obsCaps?;
         FrameFace; face-lift; fLvl≤fLvlD;
         innerFinish-face-keep;
         lookupNode-caps; capsOK?-nodeSz; capsOK?-nodeWid;
         NodeCaps;
         pathSz?; pathLen)

-- Caps-Depth: for depthFin type
open import Verify-Budget-Sufficient.Caps-Depth using (depthFin)

-- ─────────────────────────────────────────────────────────────────
-- § 1.  THE NEW SUB-POSTULATE.
--
-- Takes `nd : Maybe (NodeState Γ)` EXPLICITLY and H2 in terms of `nd`.
-- The assembly passes `nd = lookupNode allNid (EvalSt.nodes st)` with
-- no intervening `with`, so `dpt`'s type and H2's type are identical.
--
-- The sub-postulate handles all node cases internally:
--   • nothing, scan-st, take-st, merge-st, switch-st, exhaust-st,
--     concat+no  → innerFinish-face-keep (j′ = 0)
--   • concat+yes → call to innerFinish-caps (Subscribe-Face.agda:1761)
--
-- Once H1 and H2 are threaded to the face chain, this is provable
-- via innerFinish-face-keep + innerFinish-caps.
-- ─────────────────────────────────────────────────────────────────
postulate
  innerFinish-concat-face-go :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d j : ℕ) (g : Gas) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e)
    (nd : Maybe (NodeState Γ)) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    -- H1: slotsSize bound
    slotsSize sl ≤ Caps.cSize c →
    -- H2: depth bound in terms of nd directly
    depthFin g concatᵒ allNid inst κ id now vals sched st nd ≤ d →
    FrameFace c d j sl (innerFinish g concatᵒ allNid inst κ id now vals sched st nd)

-- ─────────────────────────────────────────────────────────────────
-- § 2.  THE ASSEMBLY: `innerFinish-concat-face-core` as a REAL
--       DEFINITION.  The body is a single call to the sub-postulate
--       with nd = lookupNode allNid (EvalSt.nodes st).
--
-- No second `with` abstraction: `dpt`'s type and H2's expected type
-- are the same expression, avoiding the `s ≟ᵗ s` ≠ `yes refl` issue.
--
-- THE NEW HYPOTHESES H1 and H2 are appended after the existing 8.
-- Call sites must gain them: innerFinish-concat-face, innerFinish-face,
-- innerReact-face, stepFrame-face (threaded from caps-tick).
-- ─────────────────────────────────────────────────────────────────
innerFinish-concat-face-core :
    (∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
      (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
      all (eventCaps? c sl) (InstEmit.events em) ≡ true →
      burstCaps? c sl str ≡ true →
      burstCaps? c sl (em ∷ str) ≡ true) →
    (∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
      (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
      all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true) →
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
      all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true) →
    (∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
      (str : Stream Γ u) → sl′ ≡ sl →
      burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true) →
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
-- One call to the sub-postulate.  No with-abstractions.
innerFinish-concat-face-core _ _ _ _ _ c d j g allNid inst κ id now vals sl sched st
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt =
  innerFinish-concat-face-go c d j g allNid inst κ id now vals sl sched st
    (lookupNode allNid (EvalSt.nodes st))
    2≤S 1≤R slEq slC inv pC lC vC slSz dpt
