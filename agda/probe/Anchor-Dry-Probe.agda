-- ANCHOR DRY PROBE (2026-08-06).  Dry-family statements: three postulates
-- that source the B/Ψ bounds from capsAt rather than the ledger, and a
-- discharge lemma showing the family's shape satisfies hop-edge's second
-- premise `sizeᵛ (obs u) o ≤ Ŝ`.
--
-- WHY A PROBE.  These bodies land in Wet or a module above Wet.
-- Every imported heavy module is UNCHANGED on disk → deserialises,
-- not rechecked.  Only this file itself is new.
--
-- HARD CONSTRAINT: no capᴱ anywhere.  The bounds come from capsAt / sizeCapAt.
-- See the GAP 4 comment at Wet.agda:4132-4200 for why the ledger route is
-- refuted; `walk-hyps-absurd` at Measures.agda:4209 is the machine proof.
--
-- SOURCE FOR EACH POSTULATE'S TELESCOPE — the evaluator call site:
--   chainStep      Evaluator.agda:1592
--   foldPath       Evaluator.agda:1542
--   subscribeInner thruConsume call sites at Evaluator.agda:1109, 1121,
--                  1130, 1140, 1196 (merge/concat/switch/exhaust/concatDrain)
module Anchor-Dry-Probe where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List    using (List; []; _∷_; all)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Rx.Exp: Val, obs, sizeᵛ — NOT re-exported up the Wet chain
open import Rx.Exp using (Ty; Ctx; Closed; Val; obs; sizeᵛ)

-- Rx.Prim: Gas, Id, Tick, Source, InstEvent — NOT re-exported either
open import Rx.Prim using (Gas; g0; gs; Id; Tick; Source; InstEvent)

-- Evaluator: function types and the three functions this probe declares
-- postulates for, plus the types they operate on
open import Rx.Evaluator
  using (Sched; EvalSt; Arrival; Slots; AllOp; NodeId; Path; Stream;
         chainStep; foldPath; subscribeInner;
         arrTy; arrVal)

-- Wet → Caps → Keeps-Ring → Measures (all public).  Provides:
--   INV?, ΨAt, sizeCapAt, capsAt,
--   valB?, burstB?, pathB?, eventB?, valB-sz, valB?-widen
-- UNCHANGED on disk → deserialise only.
open import Verify-Budget-Sufficient.Wet

-- capsOK? from the caps face.  Named explicitly to avoid the ambiguity
-- a bare `open` would introduce (Caps-Face and Wet share Measures names).
open import Verify-Budget-Sufficient.Caps-Face using (capsOK?)

------------------------------------------------------------------
-- § 1  THE THREE DRY POSTULATES
--
-- Shape: given INV?-good and caps-good at instant `id`, and given
-- the inputs are valB?-good at B = sizeCapAt e sl id, the observable
-- values this site hands onward are valB?-good at Ŝ = sizeCapAt e sl
-- (suc id).
--
-- The Ŝ level (not B) is forced by the code: the subscription inside
-- subscribeInner runs at instant `id` and the emitted values emerge
-- at the suc-id caps level.  chainStep and foldPath inherit this from
-- subscribeInner via thruConsume → thruWalk → stepFrame (thru-outer).
--
-- Contrast with the existing -wet family (Wet.agda:776-868), which
-- carries a Σ E′ and bounds at capᴱ W E′.  These postulates fix the
-- anchor at capsAt so no ledger receipt is involved.
------------------------------------------------------------------

postulate
  -- (1) chainStep-dry — TELESCOPE MATCHES Evaluator.agda:1592-1598.
  --
  -- chainStep id a path sched st
  --   = foldPath (budgetAt ...) n id (arrTick a) (arrSource a) path
  --              (arrVal a ∷ []) (if isLast then close ∷ [] else [])
  --              isLast sched st
  --
  -- The delivery clique (chainStep/foldPath/dispatchShare/shareGo)
  -- spends NO gas (Wet.agda comment at 3724-3727); the only source of
  -- Ŝ-bounded values in the output stream is subscribeInner (called
  -- via thruConsume when the path contains a thru-outer frame).
  chainStep-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        Ŝ  = sizeCapAt e sl (suc id)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       valB? B Ψ (arrTy a) (arrVal a) ≡ true →
       pathB? B Ψ path ≡ true →
       burstB? Ŝ Ψ (proj₁ (chainStep id a path sched st)) ≡ true

  -- (2) foldPath-dry — TELESCOPE MATCHES Evaluator.agda:1542-1546.
  --
  -- foldPath sf gas id now envSrc path vals evs fin sched st
  --   root   → emit evs ++ map value vals ++ fin-close
  --   share  → dispatchShare ...
  --   f ↠ p  → stepFrame f; foldPath p (stepFrame-result vals)
  --
  -- When `f = thru-outer op nid`, stepFrame calls thruWalk which
  -- calls subscribeInner for each o ∈ vals — those subscribeInner
  -- calls are the source of the Ŝ-bounded output.
  foldPath-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        Ŝ  = sizeCapAt e sl (suc id)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       pathB? B Ψ path ≡ true →
       all (valB? B Ψ u) vals ≡ true →
       all (eventB? B Ψ) evs ≡ true →
       burstB? Ŝ Ψ (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st)) ≡ true

  -- (3) subscribeInner-dry — THE KEY HOP-EDGE ENABLING POSTULATE.
  --     TELESCOPE MATCHES the subscribeInner call inside thruConsume
  --     (Evaluator.agda:1109, 1121, 1130, 1140, 1196).
  --
  -- subscribeInner (gs fuel) op allNid κ id now o sched st
  --   = subscribeE fuel o (from-inner op allNid inst ↠ κ) id now ...
  --
  -- The `o : Val Γ (obs u)` is subscribed via subscribeE at instant
  -- `id`; its emitted values are bounded at the suc-id caps level Ŝ.
  -- The conclusion bounds the `vs` component (proj₁ ∘ proj₂) of
  -- subscribeInner's return tuple:
  --   NodeId × List (Val Γ u) × ... × Sched Γ × EvalSt e
  --                ^--- proj₁ (proj₂ ...)
  --
  -- Contrast subscribeInner-wet (Wet.agda:856-868): that carries a
  -- Σ E′ and bounds at capᴱ W E′.  Here the anchor is fixed at
  -- sizeCapAt e sl (suc id), no ledger involved.
  subscribeInner-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        Ŝ  = sizeCapAt e sl (suc id)
    in INV? Ψ B sched st ≡ true →
       capsOK? (capsAt e sl id) sched st ≡ true →
       valB? B Ψ (obs u) o ≡ true →
       pathB? B Ψ κ ≡ true →
       all (valB? Ŝ Ψ u)
           (proj₁ (proj₂ (subscribeInner g op allNid κ id now o sched st))) ≡ true

------------------------------------------------------------------
-- § 2  THE DISCHARGE LEMMA — REAL PROOF, NOT A POSTULATE.
--
-- From `valB? B Ψ (obs u) o ≡ true` and `B ≤ Ŝ`,
-- derive `sizeᵛ (obs u) o ≤ Ŝ`.
--
-- This is hop-edge's SECOND PREMISE (Wet.agda:4053):
--   hop-edge Ŝ U r s 2≤Ŝ (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → ...
--
-- The chain:
--   subscribeInner-dry requires `valB? B Ψ (obs u) o ≡ true` as input.
--   foldPath-dry provides this for each o ∈ vals (at the thru-outer frame).
--   dry-hop + sizeCapAt-mono (B ≤ Ŝ) then discharge hop-edge's premise.
--
-- Idiom: decompose the ∧ via ∧-true, project the sizeᵛ conjunct,
-- ≤ᵇ⇒≤ via T-to — same pattern as valB-sz (Measures.agda:4962).
-- Using valB-sz directly is cleaner than inlining it.
------------------------------------------------------------------

dry-hop : ∀ {n} {Γ : Ctx n} {u : Ty} (B Ŝ Ψ : ℕ) (o : Val Γ (obs u)) →
  B ≤ Ŝ →
  valB? B Ψ (obs u) o ≡ true →
  sizeᵛ (obs u) o ≤ Ŝ
dry-hop B Ŝ Ψ o B≤Ŝ h = ≤-trans (valB-sz B Ψ _ o h) B≤Ŝ
