-- WF-AUX PROBE (2026-08-05).  Three small auxiliary lemmas that are
-- prerequisites for converting the monolithic `subscribeE-wf` postulate
-- (Verify-Well-Formed.agda:1097) into a real definition.
--
-- SHORTCUT MANDATE CONTEXT: we are in a wiring pass.  Lemmas 2 and 3
-- both mirror subscribeE's full (Gas, Closed) lexicographic recursion.
-- Per the coordinator's rule, they are POSTULATED here with exact types.
-- Lemma 1 is short and is fully proved.
--
-- IMPORT STRATEGY: only Rx.Evaluator and Rx.Protocol are imported
-- (both have cached .agdai files as of 2026-08-05 20:06).
-- Verify-Well-Formed is NOT imported (its .agdai depends on the
-- currently-modified Verify-Budget-Sufficient.* modules via Caps-Bridge).
-- reEmit is defined locally — same body as Verify-Well-Formed.agda:1878.
--
-- KEY FINDING — LEMMA 2: The original task's exact-value form
--   lookupNode nid nodes ≡ just v → lookupNode nid nodes' ≡ just v
-- is FALSE: pushBurst updates operator nodes (scan-st acc → scan-st acc',
-- take-st n → take-st n', etc.) during burst processing.  Correct form
-- is the EXISTENTIAL form (value exists but may change).
--
-- KEY FINDING — LEMMA 3: The task states "cascadeLatch is the only writer
-- of dying."  This is INCORRECT.  Two writers exist:
--   · cascadeLatch (Evaluator.agda:1620-1625) called from cascade
--   · shareLatch   (Evaluator.agda:1492-1497) called from dispatchShare
-- Both are reached only through cascade → cascadeGo → chainStep →
-- foldPath → dispatchShare, which subscribeE never calls.
-- The lemma's CONCLUSION (subscribeE never modifies dying) is still TRUE.

module Wf-Aux-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Id; Tick; Source; Gas; g0; gs;
                           InstEvent; InstEmit; _at_from_as_;
                           value; init; close; handoff; complete;
                           EmitKind; CloseReason)
open import Rx.Exp  using (Ty; Ctx; Val; Closed; Fn; obs)
open import Rx.Evaluator using (
  NodeId; NodeState; EvalSt; Sched;
  Path; Chain; Frame; Stream;
  lookupNode; setNode; splitEvents;
  subscribeE; register; installNode;
  root; _↠_; map-f; scan-f; take-f; from-inner; thru-outer;
  share-sink)
open import Rx.Protocol using (valsLast?; hasValue)

------------------------------------------------------------------
-- Boolean toolkit
------------------------------------------------------------------

not-true→false : ∀ (b : Bool) → not b ≡ true → b ≡ false
not-true→false false refl = refl
not-true→false true  ()

false→not-true : ∀ (b : Bool) → b ≡ false → not b ≡ true
false→not-true false refl = refl
false→not-true true  ()

∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true true  b h = refl , h
∧-true false b ()

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro refl refl = refl

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 1  LEMMA 1 — pushBurst-map-valsLast  (PROVED)
-- ════════════════════════════════════════════════════════════════
-- Context: pushBurst-map-char (Verify-Well-Formed.agda:1904) shows
--   pushBurst (map-f fn) burst ≡ map (reEmit (map (applyFn fn))) burst
-- The mapᵉ clause of subscribeE-wf needs valsLast? to travel through
-- this rewrite.  Proved here by list induction.
-- g [] ≡ [] is required: reEmit(g)(em) gains values iff g gains values
-- from em's existing values — if em is value-free and g [] ≡ [], the
-- result is also value-free.
------------------------------------------------------------------

-- LOCAL reEmit — same body as Verify-Well-Formed.agda:1878.
reEmit : ∀ {n} {Γ : Ctx n} {u} {B : Set}
       → (List (Val Γ u) → List B) → InstEmit (Val Γ u) → InstEmit B
reEmit {B = B} g em =
  (proj₁ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
    ++ map value (g (proj₁ (splitEvents {A = B} (InstEmit.events em))))
    ++ (if proj₂ (proj₂ (splitEvents {A = B} (InstEmit.events em)))
        then complete ∷ [] else []))
   at InstEmit.instant em from InstEmit.source em as InstEmit.kind em

-- ── Helper A: value-free event list → value extract is [] ─────────
splitEvents-vals-nil
  : ∀ {n} {Γ : Ctx n} {u} {A : Set} (evs : List (InstEvent (Val Γ u)))
  → hasValue evs ≡ false
  → proj₁ (splitEvents {A = A} evs) ≡ []
splitEvents-vals-nil []                _  = refl
splitEvents-vals-nil (value _   ∷ _)  ()
splitEvents-vals-nil (init _    ∷ es)  h  = splitEvents-vals-nil es h
splitEvents-vals-nil (close _ _ ∷ es)  h  = splitEvents-vals-nil es h
splitEvents-vals-nil (handoff _  ∷ es) h  = splitEvents-vals-nil es h
splitEvents-vals-nil (complete   ∷ es) h  = splitEvents-vals-nil es h

-- ── Helper B: bookkeeping extract carries no value constructors ────
splitEvents-bs-novalue
  : ∀ {n} {Γ : Ctx n} {u} {A : Set} (evs : List (InstEvent (Val Γ u)))
  → hasValue (proj₁ (proj₂ (splitEvents {A = A} evs))) ≡ false
splitEvents-bs-novalue []                = refl
splitEvents-bs-novalue (value _   ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (init _    ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (close _ _ ∷ es)  = splitEvents-bs-novalue es
splitEvents-bs-novalue (handoff _  ∷ es) = splitEvents-bs-novalue es
splitEvents-bs-novalue (complete   ∷ es) = splitEvents-bs-novalue es

-- ── Helper C: hasValue distributes over ++ ────────────────────────
hasValue-append-ff
  : ∀ {A : Set} (xs ys : List (InstEvent A))
  → hasValue xs ≡ false → hasValue ys ≡ false
  → hasValue (xs ++ ys) ≡ false
hasValue-append-ff []                ys _  h2 = h2
hasValue-append-ff (value _  ∷ _)   ys () _
hasValue-append-ff (init _    ∷ xs) ys h1 h2 = hasValue-append-ff xs ys h1 h2
hasValue-append-ff (close _ _ ∷ xs) ys h1 h2 = hasValue-append-ff xs ys h1 h2
hasValue-append-ff (handoff _  ∷ xs) ys h1 h2 = hasValue-append-ff xs ys h1 h2
hasValue-append-ff (complete   ∷ xs) ys h1 h2 = hasValue-append-ff xs ys h1 h2

-- ── Helper D: fin-part has no value events ────────────────────────
hasValue-fin-part
  : ∀ {A : Set} (fin : Bool)
  → hasValue {A = A} (if fin then complete ∷ [] else []) ≡ false
hasValue-fin-part true  = refl   -- hasValue (complete ∷ []) = false
hasValue-fin-part false = refl   -- hasValue [] = false

-- ── Key sub-lemma A: events part of reEmit has no values ──────────
-- `reEmit g em` wraps the events expression directly; this proves the
-- events expression is value-free without a `with` binding, so the
-- proof is usable in the `reEmit-novalue` wrapper below without the
-- `with`-substitution-propagation issue.
reEmit-events-novalue
  : ∀ {n} {Γ : Ctx n} {u} {B : Set}
    (g : List (Val Γ u) → List B) (evs : List (InstEvent (Val Γ u)))
  → g [] ≡ []
  → hasValue evs ≡ false
  → hasValue (proj₁ (proj₂ (splitEvents {A = B} evs))
               ++ map value (g (proj₁ (splitEvents {A = B} evs)))
               ++ (if proj₂ (proj₂ (splitEvents {A = B} evs))
                   then complete ∷ [] else [])) ≡ false
reEmit-events-novalue {B = B} g evs gnil hevs =
  let
    vs≡[]  = splitEvents-vals-nil   {A = B} evs hevs
    hbs    = splitEvents-bs-novalue {A = B} evs
    gvs≡[] = subst (λ l → g l ≡ []) (sym vs≡[]) gnil
    hmap   = subst (λ l → hasValue (map (value {A = B}) l) ≡ false)
                   (sym gvs≡[]) refl
    hfin      = hasValue-fin-part {A = B} (proj₂ (proj₂ (splitEvents {A = B} evs)))
    -- ++  is infixr 5, so  a ++ b ++ c = a ++ (b ++ c)
    -- reEmit's events are bs ++ (map value ... ++ fin_part)
    -- build from the inside out to match that right-associated form
    h_mv_fin  = hasValue-append-ff
                  (map value (g (proj₁ (splitEvents {A = B} evs))))
                  (if proj₂ (proj₂ (splitEvents {A = B} evs)) then complete ∷ [] else [])
                  hmap hfin
    h2        = hasValue-append-ff
                  (proj₁ (proj₂ (splitEvents {A = B} evs)))
                  (map value (g (proj₁ (splitEvents {A = B} evs)))
                    ++ (if proj₂ (proj₂ (splitEvents {A = B} evs)) then complete ∷ [] else []))
                  hbs h_mv_fin
  in h2

-- ── Key sub-lemma B: reEmit preserves "no value events" ───────────
-- Thin wrapper: InstEmit.events (reEmit g em) reduces by definition
-- to the expression in reEmit-events-novalue above.
reEmit-novalue
  : ∀ {n} {Γ : Ctx n} {u} {B : Set}
    (g : List (Val Γ u) → List B) (em : InstEmit (Val Γ u))
  → g [] ≡ []
  → not (hasValue (InstEmit.events em)) ≡ true
  → not (hasValue (InstEmit.events (reEmit g em))) ≡ true
reEmit-novalue {B = B} g em gnil hnovalue =
  false→not-true _
    (reEmit-events-novalue {B = B} g (InstEmit.events em) gnil
      (not-true→false _ hnovalue))

-- ── LEMMA 1: pushBurst-map-valsLast (PROVED) ──────────────────────
pushBurst-map-valsLast
  : ∀ {n} {Γ : Ctx n} {u} {B : Set}
    (g : List (Val Γ u) → List B)
    (burst : List (InstEmit (Val Γ u)))
  → g [] ≡ []
  → valsLast? burst ≡ true
  → valsLast? (map (reEmit g) burst) ≡ true
pushBurst-map-valsLast g []               gnil _ = refl
pushBurst-map-valsLast g (em ∷ [])        gnil _ = refl
pushBurst-map-valsLast g (em ∷ em′ ∷ ems) gnil h =
  let (hnv , htail) = ∧-true _ _ h
  in ∧-intro (reEmit-novalue g em gnil hnv)
             (pushBurst-map-valsLast g (em′ ∷ ems) gnil htail)

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 2  LEMMA 2 — subscribeE-node-fresh  (POSTULATE)
-- ════════════════════════════════════════════════════════════════
-- EXACT-VALUE FORM IS FALSE: pushBurst updates operator nodes
-- (scan-st acc → scan-st acc', take-st n → take-st n').
-- Correct form: nodes are never REMOVED, only updated or added.
-- setNode (the only mutator) replaces or appends, never deletes.
--
-- setNode-preserve (§2a): once a node exists at nid, setNode at any
-- nid' does not remove it.  Proof outline (not ground here):
--   induction on nodes; case split on k ≡ᵇ nid and k ≡ᵇ nid'.
--   Requires Data.Nat.Properties.≡ᵇ-sym/trans (3–5 lines) to chain
--   k ≡ᵇ nid' with k ≡ᵇ nid in the nid = nid' subcase.
--
-- subscribeE-node-fresh (§2b): full proof needs a mutual block
-- mirroring subscribeE's (Gas, Closed) lexicographic recursion
-- (~10 functions): subscribeE-*, pushBurst-*, stepFrame-*,
-- subscribeInner-*, thruConsume-*, etc.
-- Per the shortcut mandate, both are postulated here.
------------------------------------------------------------------

-- § 2a  Structural helper  (POSTULATED)
postulate
  setNode-preserve
    : ∀ {n} {Γ : Ctx n} (nid nid' : NodeId) (s : NodeState Γ)
      (nodes : List (NodeId × NodeState Γ))
    → lookupNode nid nodes ≢ nothing
    → lookupNode nid (setNode nid' s nodes) ≢ nothing

-- § 2b  LEMMA 2 proper  (POSTULATED)
-- NOTE: statement is EXISTENTIAL (≢ nothing), not exact-value (≡ just v).
postulate
  subscribeE-node-fresh
    : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) (nid : NodeId)
    → lookupNode nid (EvalSt.nodes st) ≢ nothing
    → lookupNode nid (EvalSt.nodes
        (proj₂ (proj₂ (subscribeE fuel b κ id now sched st)))) ≢ nothing

------------------------------------------------------------------
-- ════════════════════════════════════════════════════════════════
-- § 3  LEMMA 3 — subscribeE-dying-stable  (POSTULATE)
-- ════════════════════════════════════════════════════════════════
-- DYING WRITERS (verified against Rx/Evaluator.agda):
--   · cascadeLatch (line 1620-1625): called from cascade (line 1663)
--   · shareLatch   (line 1492-1497): called from dispatchShare (line 1578)
-- Both reachable only via:
--   drain → cascade → cascadeGo → chainStep → foldPath →
--     shareGo → dispatchShare → shareLatch
--   drain → cascade → cascadeGo → chainStep → cascadeGo → cascadeLatch
-- subscribeE's call graph: pushBurst, stepFrame, subscribeInner,
-- subscribeAll, sharedConnect, subscribeSharedSlot, register,
-- installNode, mintNode/Source/Ordinal — NONE reach cascadeLatch or
-- shareLatch.  Lemma is TRUE.
--
-- OBSTACLE: mutual block mirroring subscribeE's full recursion needed.
--
-- Termination note: the mutual block mirrors subscribeE's own accepted
-- (Gas, Closed) lexicographic recursion.  The potential termination
-- failure point: pB-dy → sI-dy → subE-dy (fuel decrease, not Closed
-- decrease).  Whether Agda's checker accepts this depends on the
-- lexicographic ordering it infers.  THE MOST VALUABLE FINDING from
-- attempting this: which exact clause triggers a termination error.
--
-- § 3-attempt commented skeleton:
-- mutual
--   subE-dy : ∀ ... → EvalSt.dying (proj₂ (proj₂ (subscribeE fuel b κ id now sched st))) ≡ EvalSt.dying st
--   subE-dy fuel (ofᵉ _) ... = refl
--   subE-dy fuel emptyᵉ  ... = refl
--   subE-dy fuel (deferᵉ _) ... = refl   -- record st {nodes;registry}: dying unchanged
--   subE-dy g0        (μᵉ _) ... = refl  -- dryBurst
--   subE-dy (gs fuel) (μᵉ b) ... = subE-dy fuel (unfoldμ b) ...
--   subE-dy fuel (mapᵉ f b) ... = trans (pB-dy ...) (subE-dy fuel b ...)
--   ...
--
--   pB-dy  : pushBurst-dying-stable
--   sI-dy  : subscribeInner-dying-stable
--   sI-dy g0        ... = refl
--   sI-dy (gs fuel) ... = subE-dy fuel ...  -- gas decreases
--   ...
------------------------------------------------------------------

postulate
  subscribeE-dying-stable
    : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (fuel : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e)
    → EvalSt.dying (proj₂ (proj₂ (subscribeE fuel b κ id now sched st)))
        ≡ EvalSt.dying st
