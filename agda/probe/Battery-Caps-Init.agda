-- BATTERY-CAPS-INIT (2026-08-06).  Falsification sweep for three
-- Caps-Bridge.agda postulates:
--
--   #7  init-capsOK?-base-core  (line 978)
--   #8  init-capsOK?            (line 918)
--   #12 three-size≤capsH-core   (line 1021)
--
-- VERDICTS (derived below):
--
--   #7  PROBED-GREEN — PARTIAL COVERAGE, STRUCTURAL ANALYSIS COMPLETES IT.
--       `capsOK?` is five conjuncts (Caps-Face.agda:297-305):
--         (1) stBounded? cSize sched st
--         (2) regsSz? cSize (registry st)
--         (3) all (widLive cWid slots) live
--         (4) all (widNode cWid slots) nodes
--         (5) length registry ≤ᵇ cReg
--       Conjuncts (2), (4), (5) are STRUCTURALLY VACUOUS at st-init
--       (registry=[], nodes=[]) and are confirmed trivially by refl
--       at Programs A and B (pending=[]).  The two substantive conjuncts:
--       (3) widLive: CONFIRMED-HOLD-BY-STRUCTURE.  For scripted slots
--           T(isData t) is enforced, and for every data type
--           Frame-Width.agda:294-299 gives pWᵛ = 0, so 0 ≤ᵇ cWid = true
--           unconditionally.  A refutation is IMPOSSIBLE regardless of
--           value count, slot count, or value content.
--       (1) stBounded?: CONFIRMED-HOLD-BY-PROBE (Programs C and D).
--           cSize = 2 + sizeᵉ e + slotsSize ins; each pending value v
--           satisfies sizeᵛ t v ≤ slotSize-1 ≤ slotsSize-1 < cSize, so
--           the check is always true and a refutation is IMPOSSIBLE.
--       Programs C (one nat pending) and D (three nat pending) exercise
--       stBounded? and widLive non-vacuously.  All four rows are green;
--       no refutation was found.
--       CORRECTION OF PRIOR CLAIM: `init-capsOK?-base` (line 1030) CALLS
--       the postulate `init-capsOK?-base-core` as an assembly — it does
--       NOT prove the postulate.  The POSTULATE IS STILL THE GAP.
--
--   #8  BLOCKED / DERIVABLE.  `capsAt e ins id` involves `sizeCount`
--       (Caps.agda:369, abstract), so the term does not reduce and refl
--       checks are not possible.  DERIVABLE from #7 via `capsOK?-mono`
--       once `capsAt-base-reg` is proved — the only missing sub-lemma.
--       (`capsAt-base-size` and `capsAt-base-wid` already exist in Caps.agda.)
--
--   #12 PROBED-GREEN AND PROMOTABLE.  `three-size-le-blowH X E (s≤s (s≤s z≤n))`
--       from Pool-Lower-Probe discharges `three-size≤capsH-core` in full
--       generality for arbitrary e and ins.  § 3 confirms this typechecks
--       for a symbolic general statement.  The unused first argument
--       (S≤sizeStep) can be discarded with _.
--       Discharge text for src/:
--         three-size≤capsH-core _ e ins =
--           three-size-le-blowH _ _ (s≤s (s≤s z≤n))
--       Home in src/: Verify-Budget-Sufficient/Caps.agda (all deps present
--       there: blowH, poolCount, towerℕ via Measures→Keeps-Ring→Caps,
--       capsHgo, capsBase; Pool-Lower-Probe helpers move verbatim).

module Battery-Caps-Init where

open import Data.Bool using (Bool; true)
open import Data.Nat  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin) renaming (zero to fzero)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (hot; after_,_)
open import Rx.Slots using (scripted; Slots)
open import Rx.Exp   using (Ty; Ctx; natᵗ; Closed; emptyᵉ; input)
open import Rx.Evaluator using (sched-init; st-init)

-- The wet family, Caps record, capsAt, capsH — cached when unchanged.
open import Verify-Budget-Sufficient.Wet

-- Caps-Face: named explicitly to avoid ambiguity with Wet's re-exports.
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?)

-- Caps-Bridge: baseCaps (and init-capsOK?-base, already proven there).
open import Verify-Budget-Sufficient.Caps-Bridge
  using (baseCaps)

-- Pool-Lower-Probe: the arithmetic chain needed for #12.
open import Pool-Lower-Probe
  using (three-size-le-blowH)

----------------------------------------------------------------------
-- Concrete programs
----------------------------------------------------------------------

private
  -- Program A: empty context, no slots.
  Γ₀ : Ctx 0
  Γ₀ = []ᵛ

  ins₀ : Slots Γ₀
  ins₀ ()

  e₀ : Closed Γ₀ natᵗ
  e₀ = emptyᵉ

  -- Program B: one-nat-input context, scripted hot slot, pending = [].
  -- widLive and stBounded? both vacuous (nothing to check).
  Γ₁ : Ctx 1
  Γ₁ = natᵗ ∷ᵛ []ᵛ

  ins₁ : Slots Γ₁
  ins₁ fzero = scripted (hot [])

  e₁ : Closed Γ₁ natᵗ
  e₁ = input fzero

  -- Program C (NON-VACUOUS): scripted hot slot, pending = [(0,1)].
  -- stBounded? checks sizeᵛ natᵗ 1 = 1 ≤ᵇ cSize.
  -- widLive   checks pWᵛ n ins₂ natᵗ 1 = 0 ≤ᵇ cWid.
  ins₂ : Slots Γ₁
  ins₂ fzero = scripted (hot (after 0 , 1 ∷ []))

  -- Program D (NON-VACUOUS): scripted hot slot, pending = [(0,5),(0,7),(0,11)].
  -- stBounded? checks 1 ≤ᵇ cSize three times.
  -- widLive   checks 0 ≤ᵇ cWid three times.
  -- Maximum pressure obtainable with natᵗ (sizeᵛ natᵗ _ = 1 always).
  ins₃ : Slots Γ₁
  ins₃ fzero = scripted (hot (after 0 , 5 ∷ after 0 , 7 ∷ after 0 , 11 ∷ []))

----------------------------------------------------------------------
-- § 1  PROBE: #7 init-capsOK?-base-core
----------------------------------------------------------------------
--
-- Four rows; the two non-vacuous rows (C, D) exercise conjuncts (1) and (3).
--
-- At st-init: registry = [], nodes = [] → conjuncts (2)(4)(5) are vacuous.
--
-- Conjunct (3) widLive for scripted natᵗ: Frame-Width.agda:294 gives
-- outWᵛ j sl natᵗ _ = 0, and dWᵛ j sl natᵗ _ = 0 similarly, so pWᵛ = 0.
-- Hence 0 ≤ᵇ cWid = true for every value regardless of cWid.
-- STRUCTURAL IMPOSSIBILITY: cannot be refuted at any concrete natᵗ program.
--
-- Conjunct (1) stBounded? for scripted natᵗ: sizeᵛ natᵗ n = 1 always, and
-- cSize = 2 + sizeᵉ e + slotsSize ins ≥ 2 > 1, so 1 ≤ᵇ cSize = true always.
-- STRUCTURAL IMPOSSIBILITY: cannot be refuted.
--
-- Programs A and B: pending = [] → all of (1)(2)(3)(4)(5) trivially vacuous.
-- Programs C and D: pending ≠ [] → (1) and (3) computed non-vacuously.
-- NO REFUTATION FOUND.

-- A: capsOK? (caps 3 1 2) sched₀ st₀ — all vacuous
_ : capsOK? (baseCaps e₀ ins₀) (sched-init e₀ ins₀) (st-init e₀) ≡ true
_ = refl

-- B: capsOK? (caps 4 2 3) sched₁ st₀ — live present but pending=[]
_ : capsOK? (baseCaps e₁ ins₁) (sched-init e₁ ins₁) (st-init e₁) ≡ true
_ = refl

-- C (NON-VACUOUS): pending = [(0,1)]; stBounded? checks 1 ≤ᵇ cSize, widLive checks 0 ≤ᵇ cWid
_ : capsOK? (baseCaps e₁ ins₂) (sched-init e₁ ins₂) (st-init e₁) ≡ true
_ = refl

-- D (NON-VACUOUS): pending = [(0,5),(0,7),(0,11)]; three checks each
_ : capsOK? (baseCaps e₁ ins₃) (sched-init e₁ ins₃) (st-init e₁) ≡ true
_ = refl

-- VERDICT: PROBED-GREEN on four rows (two non-vacuous).
-- Structural analysis shows neither conjunct (1) nor (3) can be refuted
-- at baseCaps.  The postulate init-capsOK?-base-core is STILL THE GAP.

----------------------------------------------------------------------
-- § 2  NOTE: #8 init-capsOK?  (BLOCKED / DERIVABLE)
----------------------------------------------------------------------
--
-- No refl check possible: capsAt e ins id involves sizeCount
-- (Caps.agda:369, abstract).  Path to proof:
--   capsAt-base-size : 2 + sizeᵉ e + slotsSize ins ≤ Caps.cSize (capsAt e ins id)
--   capsAt-base-wid  : suc (entryCeil n ins e)      ≤ Caps.cWid  (capsAt e ins id)
--   capsAt-base-reg  : suc (sizeᵉ e + slotsSize ins) ≤ Caps.cReg (capsAt e ins id)
--                      ← THIS IS THE ONLY MISSING PIECE
-- These give baseCaps e ins ⊑ᶜ capsAt e ins id; capsOK?-mono
-- (Caps-Face.agda:365) lifts the §1 result to the blown-up caps.

----------------------------------------------------------------------
-- § 3  PROBE: #12 three-size≤capsH-core  (PROBED-GREEN, PROMOTABLE)
----------------------------------------------------------------------
--
-- Reductions (capsHgo and capsBase are NOT abstract):
--   capsH e ins 0 = blowH (capsBase e ins)
-- where capsBase e ins = 3 + X + suc E,
--   X = sizeᵉ e + slotsSize ins,  E = entryCeil n ins e.
-- cSize (baseCaps e ins) = 2 + X.
--
-- three-size-le-blowH X E h : (2+X)+(2+X)+(2+X) ≤ blowH (3+X+suc E)
-- is exactly the conclusion of three-size≤capsH-core after reductions.
--
-- Side condition 2 ≤ 3+X+suc E: holds for all X,E since
--   3+X+suc E = suc(suc(1+X+suc E)), so s≤s(s≤s z≤n) always works.
--
-- GENERAL STATEMENT (symbolic e and ins — not a concrete instance):

three-size≤capsH-general : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Caps.cSize (baseCaps e ins) + Caps.cSize (baseCaps e ins)
    + Caps.cSize (baseCaps e ins)
  ≤ capsH e ins 0
three-size≤capsH-general e ins = three-size-le-blowH _ _ (s≤s (s≤s z≤n))

-- VERDICT: PROMOTABLE.  The body `three-size-le-blowH _ _ (s≤s (s≤s z≤n))`
-- discharges the postulate in full generality.  The first argument of
-- three-size≤capsH-core (the S≤sizeStep hypothesis) is unused and goes to _.
-- Exact discharge text:
--   three-size≤capsH-core _ e ins =
--     three-size-le-blowH _ _ (s≤s (s≤s z≤n))
-- Home: Verify-Budget-Sufficient/Caps.agda (all deps already present there).

-- Concrete instances also pass (blowH is abstract so no numeral, but the
-- generalized arithmetic lemma fires):

three-size≤capsH-A :
  Caps.cSize (baseCaps e₀ ins₀) + Caps.cSize (baseCaps e₀ ins₀)
    + Caps.cSize (baseCaps e₀ ins₀)
  ≤ capsH e₀ ins₀ 0
three-size≤capsH-A = three-size-le-blowH 1 0 (s≤s (s≤s z≤n))

three-size≤capsH-B :
  Caps.cSize (baseCaps e₁ ins₁) + Caps.cSize (baseCaps e₁ ins₁)
    + Caps.cSize (baseCaps e₁ ins₁)
  ≤ capsH e₁ ins₁ 0
three-size≤capsH-B = three-size-le-blowH 2 1 (s≤s (s≤s z≤n))
