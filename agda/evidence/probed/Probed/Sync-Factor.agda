-- THE SUBSTITUTION FACTOR, RE-DENOMINATED IN SYNC SIZE, at the family
-- that refuted its additive form.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: evalWith-nest-sync @07243b
--
-- WHAT IS BEING TESTED.  The substitution walk's charge is a factor
-- `2 ^ sizeᵗ fn`, and the whole question is which SIZE CLASS the
-- exponent should be read in.  Each row is the target's conclusion at
-- a one-entry environment -- `applyFn` IS `evalWith` at that
-- environment, and the `EnvNest` premise is the payload's own depth.  Full size grows under a μ-unfolding --
-- substitution rewrites frames that embed deferred observables -- while
-- the nest currency the factor pays for reads zero at every `deferᵉ`,
-- exactly where `syncSizeᵗ` stops counting.  If the factor holds at
-- `2 ^ syncSizeᵗ fn`, the two currencies agree in visibility and the
-- unfold head stops being unpayable at a fixed cap; if it does not,
-- some substitution deepens a payload through a position sync size
-- cannot see, and the re-denomination dies here for one program's
-- worth of arithmetic.
--
-- EVERY ROW PINS ITS FIGURES, so a repair that moves either side fails
-- naming a number.  What would make the family fail: a payload
-- occurrence that is sync-INVISIBLE in the function but lands
-- sync-VISIBLE in the output -- substitution relocating content across
-- a defer gate.  Rows A and B are LOAD-BEARING on the bound itself, at
-- the duplicating function `Refuted.Apply-Fn-Nest` refuted the additive
-- form with; row C is LOAD-BEARING on the visibility claim -- the same
-- duplication under a `deferᵉ` must contribute ZERO, pinned as an
-- equality and not an inequality; row D mixes one visible and one
-- hidden copy and must price exactly the visible one.
--
-- WHAT IS NOT COVERED.  Every row runs the walk at a ONE-entry
-- environment whose depth premise is the payload's own reading, so the
-- empty environment (`evalTm` at a closed seed) and any wider one are
-- untouched, and no row stacks substitutions.
module Probed.Sync-Factor where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤ᵇ⇒≤)
open import Data.Bool using (true)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (natᵗ; obs; Fn; Val; applyFn; syncSizeᵗ; sizeᵗ;
         ofᵉ; mapᵉ; takeᵉ; switchAllᵉ; deferᵉ; varᵗ; nat̂; strmᵗ)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Subst using (EnvNest; evalWith-nest-sync)
open import Refuted.Demand-Programs using (Γ₂)

open import Probed.Apparatus using (Confirms)

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV ℕ.zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (ℕ.suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the refuting duplicator: names its payload once on each side of a
-- `mapᵉ` sum, everything sync-visible
fnDup : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fnDup = strmᵗ (mapᵉ (varᵗ (there (here refl)))
                    (ofᵉ (varᵗ (here refl) ∷ [])))

-- the same duplicator under a defer gate: full size grows, sync size
-- and the output's nesting must not
fnHid : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fnHid = strmᵗ (takeᵉ (nat̂ 3)
                (deferᵉ (mapᵉ (varᵗ (there (here refl)))
                              (ofᵉ (varᵗ (here refl) ∷ [])))))

-- one visible copy beside the hidden pair
fnMix : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fnMix = strmᵗ (mapᵉ (varᵗ (there (here refl)))
                (takeᵉ (nat̂ 3)
                  (deferᵉ (mapᵉ (varᵗ (there (here refl)))
                                (ofᵉ (varᵗ (here refl) ∷ []))))))

syncBound : ∀ {s u} → Fn Γ₂ [] [] [] s u → Val Γ₂ s → ℕ
syncBound {s = s} fn v = 2 ^ syncSizeᵗ fn * (nestDᵗ fn + nestDᵛ s v)

-- ROW A: real duplication, shallow payload.  Two copies against a
-- sync-denominated factor of sixty-four.
dupSync≡6 : syncSizeᵗ fnDup ≡ 6
dupSync≡6 = refl

dupOut≡2 : nestDᵛ (obs (obs natᵗ)) (applyFn fnDup (deepV 1)) ≡ 2
dupOut≡2 = refl

dupA-holds : (nestDᵛ (obs (obs natᵗ)) (applyFn fnDup (deepV 1))
               ≤ᵇ syncBound fnDup (deepV 1)) ≡ true
dupA-holds = refl

-- ROW B: the same duplicator at a payload three layers deep -- the
-- demand scales with the payload and the bound must carry it.
dupOut₃≡6 : nestDᵛ (obs (obs natᵗ)) (applyFn fnDup (deepV 3)) ≡ 6
dupOut₃≡6 = refl

dupB-holds : (nestDᵛ (obs (obs natᵗ)) (applyFn fnDup (deepV 3))
               ≤ᵇ syncBound fnDup (deepV 3)) ≡ true
dupB-holds = refl

-- ROW C: the currencies split -- full size grows past sync size -- and
-- the hidden duplication prices at ZERO, as an equality.
hidSync≡4 : syncSizeᵗ fnHid ≡ 4
hidSync≡4 = refl

hidSize≡9 : sizeᵗ fnHid ≡ 9
hidSize≡9 = refl

hidOut≡0 : nestDᵛ (obs (obs natᵗ)) (applyFn fnHid (deepV 3)) ≡ 0
hidOut≡0 = refl

-- ROW D: one visible copy, one hidden pair -- exactly the visible copy
-- is priced.
mixOut≡3 : nestDᵛ (obs (obs natᵗ)) (applyFn fnMix (deepV 3)) ≡ 3
mixOut≡3 = refl

mixD-holds : (nestDᵛ (obs (obs natᵗ)) (applyFn fnMix (deepV 3))
               ≤ᵇ syncBound fnMix (deepV 3)) ≡ true
mixD-holds = refl

-- ── the tie: the statement's own inequality, at the same points ─────

-- `syncBound` above is a HAND restatement of the target's right side,
-- and `applyFn` of its left, so the rows are a reading of an
-- arithmetic that resembles the statement rather than the statement.
-- The rows below are the statement: Agda writes each type from
-- `evalWith-nest-sync` as it reads, the environment is the one
-- `applyFn` builds, and the grant is instantiated at the payload's own
-- depth -- which is the tightest `N` the premise admits, so a row here
-- cannot be passing on a slack the caller would not have.
--
-- The environment premise is `(nestDᵛ _ v ≤ N) × ⊤` at a one-entry
-- environment, and at `N` the payload's own depth that first conjunct
-- is reflexivity.  Rows A and B are the duplicator that refuted the
-- additive form, at two payload depths; row D is the mixed function,
-- where the hidden pair must not be priced.  Row C is not tied because
-- its content is an EQUALITY at zero rather than the bound.
envDup1 : EnvNest (nestDᵛ (obs natᵗ) (deepV 1)) (deepV 1 ∷ᵃ []ᵃ)
envDup1 = ≤-refl , tt

envDeep3 : EnvNest (nestDᵛ (obs natᵗ) (deepV 3)) (deepV 3 ∷ᵃ []ᵃ)
envDeep3 = ≤-refl , tt

dupRowA : Confirms
  (evalWith-nest-sync (nestDᵛ (obs natᵗ) (deepV 1)) fnDup
     (deepV 1 ∷ᵃ []ᵃ) envDup1)
dupRowA = ≤ᵇ⇒≤ _ _ tt

dupRowB : Confirms
  (evalWith-nest-sync (nestDᵛ (obs natᵗ) (deepV 3)) fnDup
     (deepV 3 ∷ᵃ []ᵃ) envDeep3)
dupRowB = ≤ᵇ⇒≤ _ _ tt

mixRowD : Confirms
  (evalWith-nest-sync (nestDᵛ (obs natᵗ) (deepV 3)) fnMix
     (deepV 3 ∷ᵃ []ᵃ) envDeep3)
mixRowD = ≤ᵇ⇒≤ _ _ tt
