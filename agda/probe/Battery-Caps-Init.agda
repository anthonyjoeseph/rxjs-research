-- BATTERY-CAPS-INIT (2026-08-06).  Falsification sweep for three
-- Caps-Bridge.agda postulates:
--
--   #7  init-capsOK?-base-core  (line 978)
--   #8  init-capsOK?            (line 918)
--   #12 three-size≤capsH-core   (line 1021)
--
-- VERDICTS (derived below):
--
--   #7  PROBED-GREEN.  `capsOK? (baseCaps e ins) (sched-init e ins) (st-init e) ≡ true`
--       reduces to `true ≡ true` by refl at every concrete program: no abstract
--       function is touched.  Also: `init-capsOK?-base` (line 1030) already
--       unconditionally proves this by calling the postulate with all proven
--       hypotheses.
--
--   #8  BLOCKED / DERIVABLE.  `capsAt e ins id` involves `sizeCount`
--       (Caps.agda:369, abstract), so the term does not reduce and refl is
--       impossible.  The postulate is DERIVABLE from #7 via `capsOK?-mono` once
--       `capsAt-base-reg` is proved; the size and wid directions already exist
--       (`capsAt-base-size`, `capsAt-base-wid` in Caps.agda) and `capsAt-base-reg`
--       is the sole missing piece for `baseCaps ⊑ᶜ capsAt e ins id`.
--
--   #12 PROBED-GREEN.  `capsH e ins 0 = blowH (capsBase e ins)` (capsHgo is
--       not abstract), and `three-size-le-blowH X E _` from Pool-Lower-Probe
--       proves `(2+X)+(2+X)+(2+X) ≤ blowH (3+X+suc E)` which is exactly what
--       `three-size≤capsH-core` needs (X = sizeᵉ e + slotsSize ins,
--       E = entryCeil n ins e, cSize = 2+X, capsBase = 3+X+suc E).

module Battery-Caps-Init where

open import Data.Bool using (Bool; true)
open import Data.Nat  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin) renaming (zero to fzero)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (hot)
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
-- Concrete program A: empty context, no slots.
----------------------------------------------------------------------

private
  Γ₀ : Ctx 0
  Γ₀ = []ᵛ

  ins₀ : Slots Γ₀
  ins₀ ()

  e₀ : Closed Γ₀ natᵗ
  e₀ = emptyᵉ

----------------------------------------------------------------------
-- Concrete program B: one-nat-input context, scripted hot slot with
-- no async values.
----------------------------------------------------------------------

private
  Γ₁ : Ctx 1
  Γ₁ = natᵗ ∷ᵛ []ᵛ

  ins₁ : Slots Γ₁
  ins₁ fzero = scripted (hot [])

  e₁ : Closed Γ₁ natᵗ
  e₁ = input fzero

----------------------------------------------------------------------
-- § 1  PROBE: #7 init-capsOK?-base-core  (PROBED-GREEN)
----------------------------------------------------------------------
--
-- Every branch of capsOK? terminates with `all _ []` at the initial state:
--   · stBounded?  loops over Sched.live and EvalSt.nodes — both []
--   · regsSz?     loops over EvalSt.registry — []
--   · widLive / widNode  loop over Sched.live / EvalSt.nodes — both []
--   · length [] ≤ᵇ cReg = true
--
-- Program A: live = [] (Fin 0 ctx has no hot inputs), registry = [], nodes = []
--   baseCaps e₀ ins₀ = caps 3 1 2
--   capsOK? (caps 3 1 2) sched st = true ∧ true ∧ true ∧ true ∧ true ✓

_ : capsOK? (baseCaps e₀ ins₀) (sched-init e₀ ins₀) (st-init e₀) ≡ true
_ = refl

-- Program B: live = [{ pending = [] }] (one scripted hot source, empty pending)
--   baseCaps e₁ ins₁ = caps 4 2 3
--   widLive loops over pending = [] → true; stBounded? over that source → true
--   registry = [], nodes = []  → all other conjuncts vacuous ✓

_ : capsOK? (baseCaps e₁ ins₁) (sched-init e₁ ins₁) (st-init e₁) ≡ true
_ = refl

----------------------------------------------------------------------
-- § 2  NOTE: #8 init-capsOK?  (BLOCKED / DERIVABLE)
----------------------------------------------------------------------
--
-- No refl check is possible: capsAt e ins id involves sizeCount
-- (Caps.agda:369, abstract), so the term does not reduce to a numeral.
--
-- Path to proof once capsAt-base-reg is stated:
--   capsAt-base-size : 2 + sizeᵉ e + slotsSize ins ≤ Caps.cSize (capsAt e ins id)
--   capsAt-base-wid  : suc (entryCeil n ins e)      ≤ Caps.cWid  (capsAt e ins id)
--   capsAt-base-reg  : suc (sizeᵉ e + slotsSize ins) ≤ Caps.cReg (capsAt e ins id)
--                      ← THIS IS MISSING
-- Together these give baseCaps e ins ⊑ᶜ capsAt e ins id, and
-- capsOK?-mono lifts init-capsOK?-base (#7) to the blown-up caps.

----------------------------------------------------------------------
-- § 3  PROBE: #12 three-size≤capsH-core  (PROBED-GREEN)
----------------------------------------------------------------------
--
-- Reductions (no abstract function involved):
--   capsH e ins 0 = capsHgo (capsBase e ins) 0   (Caps.agda:450)
--                 = blowH (capsBase e ins)        (Evaluator.agda:905)
-- where capsBase e ins = 3 + X + suc E,
--   X = sizeᵉ e + slotsSize ins,  E = entryCeil n ins e.
--
-- Caps.cSize (baseCaps e ins) = 2 + X.
--
-- three-size-le-blowH X E h :
--   (2+X)+(2+X)+(2+X) ≤ blowH (3+X+suc E)
-- is exactly the conclusion of three-size≤capsH-core.
--
-- PROGRAM A: X = sizeᵉ e₀ + slotsSize ins₀ = 1 + 0 = 1, E = 0, m = 5
--   cSize = 3, capsH e₀ ins₀ 0 = blowH 5
--   three-size-le-blowH 1 0 (s≤s (s≤s z≤n)) : 3+3+3 ≤ blowH 5  ✓

three-size≤capsH-A :
  Caps.cSize (baseCaps e₀ ins₀) + Caps.cSize (baseCaps e₀ ins₀)
    + Caps.cSize (baseCaps e₀ ins₀)
  ≤ capsH e₀ ins₀ 0
three-size≤capsH-A = three-size-le-blowH 1 0 (s≤s (s≤s z≤n))

-- PROGRAM B: X = sizeᵉ e₁ + slotsSize ins₁ = 1 + 1 = 2, E = 1, m = 7
--   (outWⱽ 1 [] ins₁ (input zero) = 1 since scripted slot → entryCeil = 1)
--   cSize = 4, capsH e₁ ins₁ 0 = blowH 7
--   three-size-le-blowH 2 1 (s≤s (s≤s z≤n)) : 4+4+4 ≤ blowH 7  ✓

three-size≤capsH-B :
  Caps.cSize (baseCaps e₁ ins₁) + Caps.cSize (baseCaps e₁ ins₁)
    + Caps.cSize (baseCaps e₁ ins₁)
  ≤ capsH e₁ ins₁ 0
three-size≤capsH-B = three-size-le-blowH 2 1 (s≤s (s≤s z≤n))
