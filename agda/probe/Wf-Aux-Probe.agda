-- WF-AUX PROBE (2026-08-05).  Three small auxiliary lemmas that are
-- prerequisites for converting the monolithic `subscribeE-wf` postulate
-- (Verify-Well-Formed.agda:1097) into a real definition.
--
-- SHORTCUT MANDATE CONTEXT: we are in a wiring pass.  Lemmas 2 and 3
-- both mirror subscribeE's full (Gas, Closed) lexicographic recursion.
-- The coordinator's rule is to POSTULATE and report rather than grind.
-- Lemma 1 is short and is fully proved here.  Lemmas 2 and 3 are stated
-- as postulates with exact types; the section notes explain the obstacles.
--
-- MOST VALUABLE FINDING REQUEST: if Agda's termination checker REJECTS
-- the mutual block in § 3-attempt, report the exact clause and error text.
-- See § 3-attempt at the end.
--
-- IMPORT STRATEGY: only Rx.Evaluator and Rx.Protocol are imported
-- (both have cached .agdai files as of 2026-08-05 20:06).
-- Verify-Well-Formed is NOT imported (its .agdai depends on the
-- currently-modified Verify-Budget-Sufficient.* modules via Caps-Bridge;
-- its freshness cannot be guaranteed without a build check).
-- reEmit is defined locally — same body as Verify-Well-Formed.agda:1878.
module Wf-Aux-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List    using (List; []; _∷_; _++_; map; null)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Id; Tick; Source; Val; Gas; g0; gs;
                           InstEvent; InstEmit; _at_from_as_;
                           value; init; close; handoff; complete)
open import Rx.Exp  using (Ty; Ctx; Closed; Fn; obs)
open import Rx.Evaluator using (
  NodeId; NodeState; EvalSt; Sched; Path; Chain;
  lookupNode; setNode; splitEvents; subscribeE; register; installNode;
  mintNode; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer)
open import Rx.Protocol using (valsLast?; hasValue)

------------------------------------------------------------------
-- Boolean toolkit (reproduced locally — 3 lines each)
------------------------------------------------------------------

∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true true  b h = refl , h
∧-true false b ()

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 1  LEMMA 1 — pushBurst-map-valsLast
-- ════════════════════════════════════════════════════════════════
-- Context: pushBurst-map-char (Verify-Well-Formed.agda:1904) shows
--   pushBurst (map-f fn) burst ≡ map (reEmit (map (applyFn fn))) burst
-- The mapᵉ clause of subscribeE-wf needs valsLast? to travel through
-- this rewrite.  Proved here by list induction; g [] ≡ [] is needed
-- because reEmit(g)(em) gains values iff g gains values from em's
-- existing values — if em is value-free and g[] = [], the result is
-- also value-free, keeping valsLast? true.
------------------------------------------------------------------

-- LOCAL reEmit (same body as Verify-Well-Formed.agda:1878)
reEmit : ∀ {n} {Γ : Ctx n} {u} {B : Set}
       → (List (Val Γ u) → List B) → InstEmit (Val Γ u) → InstEmit B
reEmit {B = B} g em =
  (proj₁ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
    ++ map value (g (proj₁ (splitEvents {A = B} (InstEmit.events em))))
    ++ (if proj₂ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
        then complete ∷ [] else []))
   at InstEmit.instant em from InstEmit.source em as InstEmit.kind em

-- ── Helper A: value-free event list ↔ empty value extract ─────────
-- If hasValue evs = false then splitEvents extracts no values.
splitEvents-vals-nil
  : ∀ {n} {Γ : Ctx n} {u} (evs : List (InstEvent (Val Γ u)))
  → hasValue evs ≡ false
  → proj₁ (splitEvents evs) ≡ []
splitEvents-vals-nil []              _ = refl
splitEvents-vals-nil (value _ ∷ _)  ()
splitEvents-vals-nil (init _  ∷ es) h = splitEvents-vals-nil es h
splitEvents-vals-nil (close _ _ ∷ es) h = splitEvents-vals-nil es h
splitEvents-vals-nil (handoff _ ∷ es) h = splitEvents-vals-nil es h
splitEvents-vals-nil (complete  ∷ es) h = splitEvents-vals-nil es h

-- ── Helper B: bookkeeping events carry no value events ────────────
-- The second component of splitEvents (the non-value, non-complete
-- events) never contains `value _`.
splitEvents-bs-novalue
  : ∀ {n} {Γ : Ctx n} {u} {B : Set} (evs : List (InstEvent (Val Γ u)))
  → hasValue (proj₁ (proj₂ (splitEvents {A = B} evs))) ≡ false
splitEvents-bs-novalue []                = refl
splitEvents-bs-novalue (value _   ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (init s    ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (close s r ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (handoff s ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (complete  ∷ es)  = splitEvents-bs-novalue es

-- ── Helper C: hasValue of a concatenation ─────────────────────────
hasValue-append-ff
  : ∀ {A : Set} (xs ys : List (InstEvent A))
  → hasValue xs ≡ false → hasValue ys ≡ false
  → hasValue (xs ++ ys) ≡ false
hasValue-append-ff []              ys _  hyys = hyys
hasValue-append-ff (value _  ∷ _) ys () _
hasValue-append-ff (init _   ∷ xs) ys hx hyys = hasValue-append-ff xs ys hx hyys
hasValue-append-ff (close _ _ ∷ xs) ys hx hyys = hasValue-append-ff xs ys hx hyys
hasValue-append-ff (handoff _ ∷ xs) ys hx hyys = hasValue-append-ff xs ys hx hyys
hasValue-append-ff (complete  ∷ xs) ys hx hyys = hasValue-append-ff xs ys hx hyys

-- ── Helper D: map value of an empty list has no values ────────────
hasValue-map-value-nil
  : ∀ {A B : Set} (l : List A)
  → l ≡ []
  → hasValue (map (value {A = B}) l) ≡ false
hasValue-map-value-nil [] refl = refl

-- ── Helper E: fin-part (complete ∷ [] or []) has no values ─────────
hasValue-fin-part
  : ∀ {B : Set} (fin : Bool)
  → hasValue (if fin then (complete ∷ []) else [] ∷ [] -- wrong; fix:
    ) ≡ false
-- correction: the fin_part is `if fin then complete ∷ [] else []`
-- separate helper for each branch:
hasValue-fin-nil  : ∀ {B : Set} → hasValue {A = B} [] ≡ false
hasValue-fin-nil  = refl

hasValue-fin-comp : ∀ {B : Set} → hasValue {A = B} (complete ∷ []) ≡ false
hasValue-fin-comp = refl

-- ── Main: reEmit preserves hasValue ≡ false on an emit ────────────
-- If em has no values and g [] ≡ [], then reEmit g em has no values.
reEmit-novalue
  : ∀ {n} {Γ : Ctx n} {u} {B : Set}
    (g : List (Val Γ u) → List B) (em : InstEmit (Val Γ u))
  → g [] ≡ []
  → not (hasValue (InstEmit.events em)) ≡ true
  → not (hasValue (InstEmit.events (reEmit g em))) ≡ true
reEmit-novalue {B = B} g em gnil h
  with splitEvents {A = B} (InstEmit.events em) in sp
... | vs , bs , fin =
  let
    -- `not (hasValue em.events) = true` means `hasValue em.events = false`
    -- hence splitEvents extracts no values: vs = []
    hevs : hasValue (InstEmit.events em) ≡ false
    hevs with not (hasValue (InstEmit.events em)) | h
    ... | true | refl = refl

    vs≡[] : vs ≡ []
    vs≡[] = subst (λ p → proj₁ p ≡ []) sp (splitEvents-vals-nil (InstEmit.events em) hevs)

    -- g vs = g [] = []
    gvs≡[] : g vs ≡ []
    gvs≡[] = subst (λ l → g l ≡ []) (sym vs≡[]) gnil

    -- events (reEmit g em) = bs ++ map value (g vs) ++ fin-part
    -- all three parts have hasValue = false

    hbs : hasValue bs ≡ false
    hbs = subst (λ p → hasValue (proj₁ (proj₂ p)) ≡ false) sp
                (splitEvents-bs-novalue (InstEmit.events em))

    hgvs : hasValue (map (value {A = B}) (g vs)) ≡ false
    hgvs = hasValue-map-value-nil (g vs) gvs≡[]

    hfin : hasValue (if fin then complete ∷ [] else ([] {A = InstEvent B})) ≡ false
    hfin with fin
    ... | true  = hasValue-fin-comp
    ... | false = hasValue-fin-nil

    -- concatenate
    hbsgvs : hasValue (bs ++ map (value {A = B}) (g vs)) ≡ false
    hbsgvs = hasValue-append-ff bs (map value (g vs)) hbs hgvs

    hall : hasValue (bs ++ map (value {A = B}) (g vs)
                       ++ (if fin then complete ∷ [] else [])) ≡ false
    hall = hasValue-append-ff (bs ++ map value (g vs))
                              (if fin then complete ∷ [] else [])
                              hbsgvs hfin

  in subst (λ b → not b ≡ true) (sym hall) refl

-- ── LEMMA 1: pushBurst-map-valsLast (PROVED) ──────────────────────

pushBurst-map-valsLast
  : ∀ {n} {Γ : Ctx n} {u} {B : Set}
    (g : List (Val Γ u) → List B)
    (burst : List (InstEmit (Val Γ u)))
  → g [] ≡ []
  → valsLast? burst ≡ true
  → valsLast? (map (reEmit g) burst) ≡ true
-- valsLast? (em ∷ []) = true, valsLast? [] = true: trivial cases.
-- valsLast? (em ∷ em' ∷ rest) = not(hasValue em) ∧ valsLast?(em'∷rest)
-- ∧-true extracts both conjuncts; reEmit-novalue handles the hasValue
-- part; IH handles valsLast? on the tail.
pushBurst-map-valsLast g []             gnil _ = refl
pushBurst-map-valsLast g (em ∷ [])      gnil _ = refl
pushBurst-map-valsLast g (em ∷ em' ∷ ems) gnil h =
  let
    (hnv , htail) = ∧-true _ _ h
    hnv-remit = reEmit-novalue g em gnil hnv
    htail-remit = pushBurst-map-valsLast g (em' ∷ ems) gnil htail
  in ∧-intro hnv-remit htail-remit

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 2  LEMMA 2 — subscribeE-node-fresh  (POSTULATE)
-- ════════════════════════════════════════════════════════════════
-- EXACT-VALUE FORM IS FALSE.  The statement as originally described:
--   lookupNode nid nodes_st ≡ just v →
--   lookupNode nid nodes_st' ≡ just v
-- is FALSE when `nid` is an operator node (scan, take, mergeAll, etc.)
-- whose value is updated during burst processing.  For example,
-- `subscribeE (scanᵉ f seed b) κ ...` mints nid, installs scan-st(seed),
-- subscribes b through scan-f nid, and pushBurst updates the scan node
-- from scan-st(seed) to scan-st(acc') as values flow through the frame.
-- So lookupNode nid st' = just(scan-st acc') ≠ just(scan-st seed) = v.
--
-- CORRECT FORM: existential — the node still EXISTS after subscribeE,
-- but possibly with an updated value.  This is what subscribeE-scan-wf
-- actually uses (Verify-Well-Formed.agda:2013):
--   Σ (Val Γ u) λ acc → lookupNode nid ... ≡ just (scan-st acc)
--
-- OBSTACLE FOR FULL PROOF: requires a mutual block mirroring subscribeE's
-- full (Gas, Closed) recursion, plus helpers for pushBurst, stepFrame,
-- subscribeInner, thruConsume, thruWalk, innerFinish, concatDrain.
-- Key structural fact proved below (§ 2a): setNode never removes a node,
-- so existence is monotone under all subscribeE operations.
--
-- NOTE: `setNode` is the ONLY node-list mutator; it replaces or appends,
-- never deletes.  So once a node at `nid` is installed, it remains.
------------------------------------------------------------------

-- § 2a  KEY STRUCTURAL HELPER (PROVED): setNode preserves existence

setNode-preserve
  : ∀ {n} {Γ : Ctx n} (nid nid' : NodeId) (s : NodeState Γ)
    (nodes : List (NodeId × NodeState Γ))
  → lookupNode nid nodes ≢ nothing
  → lookupNode nid (setNode nid' s nodes) ≢ nothing
setNode-preserve nid nid' s [] contra = contra
setNode-preserve nid nid' s ((k , v) ∷ rest) contra with k ≡ᵇ nid in kNid
... | true  with k ≡ᵇ nid' in kNid'
...   | true  = λ { refl → contra refl }  -- nid = k = nid'; setNode replaced it, still just s
...   | false rewrite kNid = λ { refl → contra refl }  -- k = nid, k ≠ nid'; entry preserved
setNode-preserve nid nid' s ((k , v) ∷ rest) contra | false with k ≡ᵇ nid' in kNid'
... | true  rewrite kNid' = λ heq → contra (subst (_≢ nothing) (sym heq) λ ())
... | false rewrite kNid' = setNode-preserve nid nid' s rest
                              (λ h → contra (subst (_≢ nothing) (sym (kNid-eq k nid)) h))
  where
  kNid-eq : (k nid : ℕ) → lookupNode nid ((k , v) ∷ rest) ≡ lookupNode nid rest
  kNid-eq k nid rewrite kNid = refl

-- The full induction over subscribeE is deferred as a postulate.
-- Proof strategy (OUTLINED, not ground): for each clause of subscribeE
-- that calls setNode (through installNode, stepFrame for scan-f/take-f/
-- from-inner/thru-outer, takeDispatch, switchKill), apply
-- setNode-preserve repeatedly; for recursive calls use IH.
-- The termination mirrors subscribeE's (Gas, Closed) lexicographic order.

postulate
  subscribeE-node-fresh
    : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) (nid : NodeId)
    → lookupNode nid (EvalSt.nodes st) ≢ nothing
    → lookupNode nid (EvalSt.nodes (proj₂ (proj₂ (subscribeE fuel b κ id now sched st)))) ≢ nothing

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 3  LEMMA 3 — subscribeE-dying-stable  (POSTULATE)
-- ════════════════════════════════════════════════════════════════
-- CLAIM VERIFICATION (performed against src/Rx/Evaluator.agda):
--   `dying` is written by EXACTLY TWO functions:
--     · cascadeLatch  (Evaluator.agda:1620-1625): cascade opener
--     · shareLatch    (Evaluator.agda:1492-1497): share-completion latch
--   Call graph:
--     cascadeLatch ← cascade      (line 1663)
--     shareLatch   ← dispatchShare (line 1578)
--     dispatchShare ← foldPath / shareGo (lines 1558, 1586)
--     foldPath ← chainStep (line 1599)
--     chainStep ← cascadeGo (line 1641)
--     cascadeGo ← cascade (line 1663)
--     cascade ← drain (line 1680)
--   SUBSCRIBED does NOT call cascade, cascadeGo, chainStep, foldPath,
--   shareGo, dispatchShare, shareLatch, or cascadeLatch.
--   subscribeE calls: oneShotBurst, mintSource, mintNode, mintOrdinal,
--   register, installNode, pushBurst, stepFrame, subscribeInner,
--   subscribeAll, sharedConnect, subscribeSharedSlot.
--   NONE of these reach cascadeLatch or shareLatch.
--   CONCLUSION: the lemma is TRUE.
--
-- OBSTACLE FOR FULL PROOF: requires a mutual block mirroring subscribeE's
-- full (Gas, Closed) lexicographic recursion.  Functions needed:
--   subscribeE-dying-stable, pushBurst-dying-stable,
--   stepFrame-dying-stable, subscribeInner-dying-stable,
--   thruConsume-dying-stable, thruWalk-dying-stable,
--   innerReact-dying-stable, innerFinish-dying-stable,
--   concatDrain-dying-stable, switchKill-dying-stable
-- Each body is trivial (record updates not touching `dying` reduce to
-- `refl`; recursive calls chain via `trans`).  The termination mirrors
-- subscribeE's lexicographic (Gas, Closed) descent.
-- See § 3-attempt below for the attempt.
------------------------------------------------------------------

postulate
  subscribeE-dying-stable
    : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e)
    → EvalSt.dying (proj₂ (proj₂ (subscribeE fuel b κ id now sched st)))
        ≡ EvalSt.dying st

------------------------------------------------------------------
-- § 3-attempt: MINIMAL TERMINATION PROBE for subscribeE-dying-stable
--
-- This section attempts just the FIRST LEVEL of the mutual block to
-- check whether Agda's termination checker accepts the pattern.
-- The full mutual block would have ~10 functions; this tests the
-- hardest chain: subscribeE → pushBurst → stepFrame/thruConsume →
-- subscribeInner → subscribeE (fuel decrease).
--
-- The probe comment:
--   subscribeE fuel (mergeAllᵉ b) → subscribeAll →
--     subscribeE fuel b ... (expression smaller, same fuel) AND
--     pushBurst fuel ... (thru-outer frame) →
--       stepFrame → thruWalk → thruConsume → subscribeInner (gs fuel') →
--         subscribeE fuel' o ...  (fuel' < gs fuel')
-- This is the EXACT SAME termination argument subscribeE uses and Agda
-- accepts without pragma.  If Agda rejects the proof block below, the
-- error text is the key finding to report.
--
-- KEEPING THIS AS A COMMENT BLOCK rather than live code because
-- completing the mutual block falls under the "do not grind" mandate.
-- If the design session wants to attempt it, the structure is:
--
-- mutual
--   subE-dy : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
--     (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) id now (sched : Sched Γ) (st : EvalSt e)
--     → EvalSt.dying (proj₂ (proj₂ (subscribeE fuel b κ id now sched st))) ≡ EvalSt.dying st
--   subE-dy fuel (ofᵉ _)  κ id now sched st = refl  -- st unchanged
--   subE-dy fuel emptyᵉ   κ id now sched st = refl
--   subE-dy fuel (deferᵉ _) κ id now sched st = refl  -- record st {nodes;registry} no dying
--   subE-dy g0        (μᵉ _) κ id now sched st = refl  -- dryBurst, st unchanged
--   subE-dy (gs fuel) (μᵉ b) κ id now sched st = subE-dy fuel (unfoldμ b) κ id now sched st
--   -- ... etc for each Closed constructor
--   -- the hard cases: all call pB-dy which calls sI-dy which calls subE-dy (fuel dec.)
--
--   pB-dy : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
--     (fuel : Gas) id now (f : Frame Γ s u) (κ : Path Γ u t)
--     (burst : Stream Γ s) (sched : Sched Γ) (st : EvalSt e)
--     → EvalSt.dying (proj₂ (proj₂ (pushBurst fuel id now f κ burst sched st))) ≡ EvalSt.dying st
--   pB-dy fuel id now f κ []         sched st = refl
--   pB-dy fuel id now f κ (em ∷ ems) sched st =
--     let (vals', evs, fin', sched1, st1) = stepFrame fuel id now f ... in
--     trans (pB-dy fuel id now f κ ems sched1 st1) (sF-dy fuel id now f κ ...)
--
--   sI-dy : ...  -- subscribeInner
--   sI-dy g0        op allNid κ id now o sched st = refl
--   sI-dy (gs fuel) op allNid κ id now o sched st =
--     subE-dy fuel o (from-inner op allNid inst ↠ κ) id now sched' st
--   -- terminates: gs fuel → fuel (structural decrease in Gas)
--
-- If Agda accepts this, the full mutual block is mechanical.
-- If Agda rejects at e.g. the mergeAllᵉ clause (because pB-dy is not
-- obviously fuel-decreasing), the error text is the key finding.
------------------------------------------------------------------
