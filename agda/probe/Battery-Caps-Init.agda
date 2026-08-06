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

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using ([]; _∷_)
open import Data.Fin  using (zero)
open import Data.Vec  using (lookup)
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
-- § 1  PROBE: #7 init-capsOK?-base-core  (PROBED-GREEN)
----------------------------------------------------------------------
--
-- Every branch of capsOK? terminates with `all _ []` when st-init and
-- sched-init are applied to any program:
--   · stBounded?  uses all over Sched.live  and EvalSt.nodes — both []
--   · regsSz?     uses all over EvalSt.registry — []
--   · widLive / widNode  loop over Sched.live / EvalSt.nodes — both []
--   · length [] ≤ᵇ cReg = true
-- The computation involves no abstract function; refl discharges it.

-- Case A: empty context, no slots.
--   baseCaps emptyᵉ (λ()) = caps 3 1 2
--   sched-init emptyᵉ (λ()) → live = []  (no hot inputs in Fin 0 ctx)
--   st-init emptyᵉ          → registry = [], nodes = []
--   Result: true ∧ true ∧ true ∧ true ∧ true = true  ✓
_ : capsOK?
      (baseCaps (emptyᵉ {Γ = []} {t = natᵗ}) (λ()))
      (sched-init (emptyᵉ {Γ = []} {t = natᵗ}) (λ()))
      (st-init (emptyᵉ {Γ = []} {t = natᵗ}))
    ≡ true
_ = refl

-- Case B: one-nat-input context, scripted hot slot with no values.
--   baseCaps (input zero) ins1 = caps 4 2 3
--   sched-init → live = [{ pending = [] }]  (one live source, empty pending)
--   st-init    → registry = [], nodes = []
--   widLive loops over pending = [] → true.  All others vacuous.  ✓
private
  ins1 : Slots (natᵗ ∷ [])
  ins1 _ = scripted (hot [])

_ : capsOK?
      (baseCaps (input {Γ = natᵗ ∷ []} zero) ins1)
      (sched-init (input {Γ = natᵗ ∷ []} zero) ins1)
      (st-init (input {Γ = natᵗ ∷ []} zero))
    ≡ true
_ = refl

----------------------------------------------------------------------
-- § 2  NOTE: #8 init-capsOK?  (BLOCKED / DERIVABLE)
----------------------------------------------------------------------
--
-- No checkable row: capsAt e ins id involves sizeCount (abstract,
-- Caps.agda:369), so the term does not reduce and refl is not available.
--
-- Path to proof once capsAt-base-reg is stated:
--   capsAt-base-size  : 2 + sizeᵉ e + slotsSize ins ≤ Caps.cSize (capsAt e ins id)
--   capsAt-base-wid   : suc (entryCeil n ins e)      ≤ Caps.cWid  (capsAt e ins id)
--   capsAt-base-reg   : suc (sizeᵉ e + slotsSize ins) ≤ Caps.cReg (capsAt e ins id)
--                       ← THIS IS MISSING
-- Together these give  baseCaps e ins ⊑ᶜ capsAt e ins id,  and
-- capsOK?-mono then lifts init-capsOK?-base (#7) to the blown-up caps.

----------------------------------------------------------------------
-- § 3  PROBE: #12 three-size≤capsH-core  (PROBED-GREEN)
----------------------------------------------------------------------
--
-- capsH e ins 0 reduces:
--   capsH e ins 0 = capsHgo (capsBase e ins) 0   (Caps.agda:450, not abstract)
--                 = blowH (capsBase e ins)        (Evaluator.agda:905, not abstract)
-- where capsBase e ins = 3 + (sizeᵉ e + slotsSize ins) + suc (entryCeil n ins e).
--
-- Setting X = sizeᵉ e + slotsSize ins, E = entryCeil n ins e:
--   Caps.cSize (baseCaps e ins) = 2 + X
--   capsH e ins 0               = blowH (3 + X + suc E)
-- Pool-Lower-Probe.three-size-le-blowH X E h proves
--   (2+X)+(2+X)+(2+X) ≤ blowH (3+X+suc E)
-- which is exactly the conclusion of three-size≤capsH-core.
--
-- Concrete instance: emptyᵉ / (λ())  →  X = 1, E = 0, m = 5.
--   Caps.cSize (baseCaps emptyᵉ (λ())) = 3
--   capsH emptyᵉ (λ()) 0               = blowH 5
--   three-size-le-blowH 1 0 (s≤s (s≤s z≤n)) : 3+3+3 ≤ blowH 5

three-size≤capsH-concrete :
  Caps.cSize (baseCaps (emptyᵉ {Γ = []} {t = natᵗ}) (λ()))
    + Caps.cSize (baseCaps (emptyᵉ {Γ = []} {t = natᵗ}) (λ()))
    + Caps.cSize (baseCaps (emptyᵉ {Γ = []} {t = natᵗ}) (λ()))
  ≤ capsH (emptyᵉ {Γ = []} {t = natᵗ}) (λ()) 0
three-size≤capsH-concrete = three-size-le-blowH 1 0 (s≤s (s≤s z≤n))

-- Case B: one-nat-input context, scripted hot slot (same ins1 as § 1).
--   X = 2 (sizeᵉ (input zero) + inputSize (hot []) = 1+1 = 2),
--   E = entryCeil 1 ins1 (input zero) = 1  (outW 1 [] ins1 (input zero) = 1)
--   m = capsBase (input zero) ins1 = 3 + 2 + suc 1 = 7
--   three-size-le-blowH 2 1 (s≤s (s≤s z≤n)) : (2+2)+(2+2)+(2+2) ≤ blowH 7

three-size≤capsH-concrete-B :
  Caps.cSize (baseCaps (input {Γ = natᵗ ∷ []} zero) ins1)
    + Caps.cSize (baseCaps (input {Γ = natᵗ ∷ []} zero) ins1)
    + Caps.cSize (baseCaps (input {Γ = natᵗ ∷ []} zero) ins1)
  ≤ capsH (input {Γ = natᵗ ∷ []} zero) ins1 0
three-size≤capsH-concrete-B = three-size-le-blowH 2 1 (s≤s (s≤s z≤n))
