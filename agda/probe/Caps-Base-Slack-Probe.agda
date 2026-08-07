------------------------------------------------------------------
-- LEDGER CLASS: LANDING: Verify-Budget-Sufficient/Caps-Bridge.agda
--
-- ONE MORE UNIT OF SIZE SLACK AT EVERY BASE.  `opIterD-dominated`'s
-- repaired guard (`3 + k ≤ S`, Op-Budget) asks the nestOK supplier for
-- one unit more than `capsAt-base-size` gives.  It is free, and this
-- probe is where that is checked cheaply: capsAt's base is
-- `frameBlowup c₀ _`, whose cSize is `iterSize (cSize c₀) (sizeCount
-- c₀ _) (cSize c₀)`, and `2≤sizeCount` says at least TWO sizeSteps
-- run.  One is enough: sizeStep S S = S * suc (2 * S) ≥ S + S ≥ suc S.
------------------------------------------------------------------
module Caps-Base-Slack-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; m≤m+n;
         *-identityʳ; *-monoʳ-≤; *-suc; +-monoˡ-≤; +-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using (sym)

open import Rx.Exp   using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator using (iterSize; sizeStep; capsBase)
open import Rx.Frame-Width using (entryCeil)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; capsAt; capsH; frameBlowup;
         iterSize-mono-count; 2≤sizeCount; cSize≤frameBlowup;
         2≤capsAt-size)

-- ONE sizeStep already clears a suc, so a positive sizeCount lifts the
-- floor by one.  (2≤sizeCount is the positivity; only 1 ≤ is spent.)
sucSize≤frameBlowup : ∀ (c : Caps) (d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  suc (Caps.cSize c) ≤ Caps.cSize (frameBlowup c d)
sucSize≤frameBlowup c d 2≤S 1≤R =
  ≤-trans sucS≤step
          (iterSize-mono-count S S 1≤S
            (≤-trans (s≤s z≤n) (2≤sizeCount c d 2≤S 1≤R)))
  where
  S = Caps.cSize c

  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  1≤2S : 1 ≤ 2 * S
  1≤2S = ≤-trans (s≤s z≤n)
                 (≤-trans (≤-reflexive (sym (*-identityʳ 2)))
                          (*-monoʳ-≤ 2 1≤S))

  S≤S2S : S ≤ S * (2 * S)
  S≤S2S = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤2S)

  -- suc S = 1 + S ≤ S + S ≤ S + S * (2 * S) = S * suc (2 * S)
  sucS≤step : suc S ≤ sizeStep S S
  sucS≤step = ≤-trans (+-monoˡ-≤ S 1≤S)
              (≤-trans (+-monoʳ-≤ S S≤S2S)
                       (≤-reflexive (sym (*-suc S (2 * S)))))

capsAt-base-size⁺ : ∀ {n} {Γ : Ctx n} {t}
  (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  3 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
capsAt-base-size⁺ {n = n} e sl zero =
  sucSize≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl)
                            (suc (entryCeil n sl e))
                            (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
    (s≤s z≤n)
capsAt-base-size⁺ e sl (suc id) =
  ≤-trans (capsAt-base-size⁺ e sl id)
          (cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))
