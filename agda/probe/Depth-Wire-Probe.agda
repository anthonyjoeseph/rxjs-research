-- ROADMAP: tier-1 #5 — `baseCaps-is-inner`, parked outside the claim graph BY DESIGN (Caps-Bridge.agda:1018).
-- DELETE WHEN: tier-1 #5's remaining depth postulates are discharged  [T3]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- DEPTH-WIRE-PROBE.  Rehearsal for wiring `depth-capped`
-- (Depth-Bound.agda:244, PROVEN, ORPHANED) to a real consumer.
--
-- Background (PROOF-STATE.md § "RULING: `depth-capped` must be spent
-- at the SMALL caps"): the naive route — apply `depth-capped` at
-- `capsAt e ins 0` — is a dead end because `capsAt e ins 0` is itself
-- a `frameBlowup`, so its `cSize` is tower-sized and the downstream
-- arithmetic is intractable.  The ruling says: apply `depth-capped`
-- at the PRE-BLOWUP inner argument instead, then chain to `capsH`.
--
-- This file:
--
--   STEP 1.  Define `baseCaps` (the inner argument of `capsAt`'s
--            `frameBlowup`) and verify by `refl` that
--            capsAt e sl 0 ≡ frameBlowup (baseCaps e sl) (capsBase e sl).
--
--   STEP 2.  State two real postulates:
--            · init-capsOK?-base : capsOK? holds at baseCaps on init state
--            · three-size≤capsH  : 3 * cSize (baseCaps) ≤ capsH e ins 0
--
--   STEP 3.  Prove depthE≤capsH-root AS A REAL DEFINITION by calling
--            `depth-capped` (at c := baseCaps) and chaining with the
--            two postulates.  Three side conditions — all trivial arithmetic
--            at the base caps' fields.  See inline comment for the chain.
--
--   STEP 4.  Postulate opIterD≤sizeCount-root, then prove
--            opIterD≤capsH-root AS A REAL DEFINITION by `≤-trans` of
--            `opIterD-mono` (d ≤ d′ slot = depthE≤capsH-root) and
--            the postulate.  `2≤capsAt-size` supplies opIterD-mono's
--            `2 ≤ S` side condition; all other arguments are ≤-refl.
--
-- None of the postulates here are ⊤-typed.  Each real definition
-- genuinely calls depth-capped / opIterD-mono.
module Depth-Wire-Probe where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_; _⊔_;
                                z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; m≤n+m; m≤m+n; n≤1+n;
                                       m≤m⊔n;
                                       *-mono-≤; *-monoʳ-≤; +-mono-≤; *-comm;
                                       *-distribˡ-+; *-identityʳ; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; all; any; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import Rx.Prim      using (Gas; Tick; Id; Fuel; Source; close; exhausted)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; sizeᵉ; syncSizeᵉ)
open import Rx.Frame-Width using (dWᵉ; ceilᵉ; dW≤ceil; entryCeil; pWᵛ)
open import Rx.Hop-Depth  using (hopDᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                RegId; Chain;
                                Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                arrTy; arrVal; arrTick; arrSource; cascade;
                                cascadeGo; cascadeLatch; cascadeFinish;
                                chainStep; chainsOf; hasDry;
                                subscribeE; budgetAt; slotsSize; opIterD;
                                sizeStep; capsBase;
                                sched-next; schedGo; schedHeadOf; schedEarlier;
                                drain; evaluate; sched-init; st-init)

-- the whole wet family (INV?, ΨAt, sizeCapAt, sizeCapAt-mono, valB?,
-- fnCapBounded?, regsB?, slotsFnCap, INV-parts, pathLen, the Bool
-- toolkit ∧-true/∧-intro/all-impl/≤ᵇ-widen/T-to/T⇒≡true) via the public
-- chain Wet → Caps → Keeps-Ring → Measures
open import Verify-Budget-Sufficient.Wet

-- the caps face and the subscribe clique (capsOK?, capsOK?-parts,
-- capsOK?-count, caps-tick, pathSz?/regsSz?/frameSz?, slotsCaps?,
-- valCaps?, burstCaps?/burstCount?, subscribeE-caps, nest) via the
-- public chain Subscribe-Face → Caps-Face → {Delivery-Walk, Caps-Nest}
-- Also: capsH, frameBlowup, sizeCount, capsAt, 2≤capsAt-size,
-- capsAt-base-size, opIterD-mono etc. from Caps via Delivery-Walk public.
open import Verify-Budget-Sufficient.Subscribe-Face

-- the depth mirror (S4's currency)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

-- depth-capped (proven in Depth-Bound): depthE ≤ 3·cSize when capsOK?.
-- This probe is the rehearsal for giving it a real consumer.
open import Verify-Budget-Sufficient.Depth-Bound using (depth-capped)

------------------------------------------------------------------
-- STEP 1. baseCaps and the refl identity.
--
-- baseCaps e sl is the INNER argument of capsAt e sl 0's frameBlowup:
--   capsAt e sl 0 = frameBlowup (baseCaps e sl) (capsBase e sl)
--
-- Its cSize field is 2 + sizeᵉ e + slotsSize sl — entry-computable,
-- syntax-linear, no tower arithmetic.
------------------------------------------------------------------

baseCaps : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Caps
baseCaps {n = n} e sl = caps (2 + sizeᵉ e + slotsSize sl)
                             (suc (entryCeil n sl e))
                             (suc (sizeᵉ e + slotsSize sl))

-- capsAt's zero clause IS frameBlowup (baseCaps e sl) (capsBase e sl),
-- by the definition of capsAt (Caps.agda:452-457).  Holds by refl.
baseCaps-is-inner : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  capsAt e sl 0 ≡ frameBlowup (baseCaps e sl) (capsBase e sl)
baseCaps-is-inner e sl = refl

------------------------------------------------------------------
-- STEP 2. Two real postulates.
--
-- init-capsOK?-base: five non-vacuous ≡ true conjuncts on the initial
-- state.  Three hold vacuously (empty registry, empty nodes), but two
-- are real: stBounded? reads slotsSize ≤ cSize (which holds since
-- cSize = 2 + sizeᵉ + slotsSize ≥ slotsSize) and widLive reads
-- Sched.live ≤ cWid (which holds since cWid = suc(entryCeil) and
-- sched-init's live sources have dWᵉ ≤ entryCeil).
--
-- three-size≤capsH: the arithmetic bridge from 3·cSize (baseCaps)
-- to capsH e ins 0.  Caps.cSize (baseCaps e ins) = 2 + sizeᵉ e +
-- slotsSize ins.  capsH e ins 0 = capsHgo (capsBase e ins) 0 =
-- blowH (capsBase e ins) = 6 + capsBase + 2 * poolCount ... — grows
-- faster than any fixed multiple of baseCaps's linear cSize, so ≤
-- holds with room to spare; details are for the actual proof.
------------------------------------------------------------------

postulate
  init-capsOK?-base : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true

  three-size≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    Caps.cSize (baseCaps e ins) + Caps.cSize (baseCaps e ins)
      + Caps.cSize (baseCaps e ins)
      ≤ capsH e ins 0

------------------------------------------------------------------
-- STEP 3. depthE≤capsH-root: REAL DEFINITION calling depth-capped.
--
-- depth-capped (Depth-Bound.agda:244) has four side conditions at
-- c := baseCaps e ins, sched := sched-init e ins, st := st-init e,
-- b := e, κ := root, g := budgetAt e ins 0, bid := 0, now := 0:
--
--   (i)  capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true
--          → init-capsOK?-base e ins
--
--   (ii) slotsSize (Sched.slots (sched-init e ins)) ≤ Caps.cSize (baseCaps e ins)
--          Sched.slots (sched-init e ins) = ins definitionally
--            (sched-init's record body sets slots = ins, Evaluator:121)
--          so this reduces to: slotsSize ins ≤ (2 + sizeᵉ e) + slotsSize ins
--          → m≤n+m (slotsSize ins) (2 + sizeᵉ e)
--
--   (iii) sizeᵉ e ≤ Caps.cSize (baseCaps e ins)
--           = sizeᵉ e ≤ (2 + sizeᵉ e) + slotsSize ins
--           → ≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize ins))
--
--   (iv) suc (pathLen root) ≤ Caps.cSize (baseCaps e ins)
--          pathLen root = 0 definitionally (Measures.agda:5635)
--          so: 1 ≤ 2 + sizeᵉ e + slotsSize ins
--          2 + sizeᵉ e + slotsSize ins = suc (suc (sizeᵉ e) + slotsSize ins)
--          → s≤s z≤n
--
-- depth-capped concludes: depthE ... ≤ cSize c + cSize c + cSize c
-- Then three-size≤capsH chains: ... ≤ capsH e ins 0.
------------------------------------------------------------------

depthE≤capsH-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
    ≤ capsH e ins 0
depthE≤capsH-root e ins =
  ≤-trans
    (depth-capped (baseCaps e ins) (budgetAt e ins 0) e root 0 0
       (sched-init e ins) (st-init e)
       (init-capsOK?-base e ins)
       (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
       (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize ins)))
       (s≤s z≤n))
    (three-size≤capsH e ins)

------------------------------------------------------------------
-- STEP 4. opIterD≤capsH-root: REAL DEFINITION consuming
--         depthE≤capsH-root via opIterD-mono.
--
-- opIterD-mono (Caps.agda:686) has signature:
--   ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
--   2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
--   opIterD S W d k m J ≤ opIterD S′ W′ d′ k′ m′ J′
--
-- Instantiation: S = S′ = Caps.cSize (capsAt e ins 0)
--                W = W′ = Caps.cWid  (capsAt e ins 0)
--                J = J′ = 0
--                m = m′ = suc (sizeᵉ e)
--                d  = depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
--                d′ = capsH e ins 0
--                k = k′ = nest e ins []
--   2 ≤ S  → 2≤capsAt-size e ins 0
--   S ≤ S′ → ≤-refl
--   W ≤ W′ → ≤-refl
--   J ≤ J′ → ≤-refl
--   d ≤ d′ → depthE≤capsH-root e ins
--   k ≤ k′ → ≤-refl
--   m ≤ m′ → ≤-refl
--
-- Then chain with opIterD≤sizeCount-root (postulated).
------------------------------------------------------------------

postulate
  opIterD≤sizeCount-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
            (capsH e ins 0) (nest e ins []) (suc (sizeᵉ e)) 0
      ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)

opIterD≤capsH-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
          (depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e))
          (nest e ins []) (suc (sizeᵉ e)) 0
    ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)
opIterD≤capsH-root e ins =
  ≤-trans
    (opIterD-mono (suc (sizeᵉ e)) (suc (sizeᵉ e))
                  (depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e))
                  (capsH e ins 0)
                  (nest e ins []) (nest e ins [])
                  (2≤capsAt-size e ins 0) ≤-refl ≤-refl ≤-refl
                  (depthE≤capsH-root e ins) ≤-refl ≤-refl)
    (opIterD≤sizeCount-root e ins)
