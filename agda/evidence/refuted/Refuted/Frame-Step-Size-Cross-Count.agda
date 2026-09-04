-- ══════════════════════════════════════════════════════════════════
-- AND THE REPAIR THE CROSSING REFUTATIONS POINT AT DIES AT THE FRAME
-- CEILING, NOT AT THE FRAME.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  All four crossing arms fail on one
-- quantity, the size of what the subscribed program emits, and the
-- move that answers it is to charge the arriving observables' own
-- `sizeᵉ` instead of a constant.  That move has to survive the one
-- place a frame's charge is spent against a ceiling: the count is
-- capped by a width times a successor cap, and that cap reads the
-- PROGRAM rather than the level.
--
-- WHERE IT BREAKS.  The frame's own size test says nothing whatever
-- about a crossing frame -- it is `true` there by definition -- so
-- the only reading of the arriving values in the neighbourhood is the
-- LEVEL, and no premise ties the level down to the cap in the
-- direction a ceiling needs.  The row takes the level ONE RUNG above
-- the cap, which is where the walk stands after a single frame, and
-- the width AT the cap, which is what the consumer passes.  An
-- observable value of four thousand and ninety-seven sits under that
-- level and over a ceiling of three thousand six hundred and sixty.
-- Raising the cap does not close it: the ceiling is quadratic in the
-- cap while the level is the caps recurrence itself, so the gap opens
-- rather than shuts.
--
-- AND THE VALUE IS REACHABLE, which is the half a hand-built state
-- would not buy.  A function of one argument whose body is
-- `strmᵗ (ofᵉ (varᵗ … ∷ []))` reifies whatever arrives into a one-shot
-- observable, and its own syntax is a handful of nodes -- so a
-- `map-f` the size test already admits hands the next frame an
-- observable whose syntax is the arriving VALUE's size.  That is
-- `reify` at a product mirroring the value it came from, the same
-- mechanism the store half was refuted on.
--
-- WHAT THIS DOES NOT SHOW.  It does not refute charging the size at
-- the FRAME: `stepFrame-sz`'s crossing arms plausibly become true
-- under it, and nothing here instantiates them.  Nor does it reach
-- the `from-inner` arm, whose subscribed program arrives through the
-- store rather than through its own argument list and therefore
-- cannot be read off `vals` at any price.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Size-Cross-Count where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat.ListAction using (sum)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; Val; natᵗ; obs; _×ᵗ_; ofᵉ; reify; sizeᵛ)
open import Rx.Evaluator using (NodeId; AllOp; mergeAllᵒ; thru-outer; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?; frameCh)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED -- and it stands
-- nowhere in `src`, because what is refuted is the REPAIR the
-- crossing refutations propose rather than a statement standing there
-- today.  It is `szCount≤ch`'s crossing arm with the constant
-- replaced by the size, carrying every premise that arm has, plus the
-- level reading the walk supplies and a tie putting the level at or
-- above the cap.
----------------------------------------------------------------------
CrossCountCh : Set
CrossCountCh = ∀ {n} {Γ : Ctx n} {u} (S W B : ℕ) → 2 ≤ S → 1 ≤ W → S ≤ B →
  (op : AllOp) (nid : NodeId) (vals : List (Val Γ (obs u))) →
  frameSz? S (thru-outer {Γ = Γ} {u = u} op nid) ≡ true →
  length vals ≤ W → valsSz? B vals ≡ true →
  sum (map (sizeᵛ (obs u)) vals) ≤ frameCh S W

----------------------------------------------------------------------
-- THE WITNESS.  A value that doubles per layer, reified into a
-- one-shot observable -- so the observable's `sizeᵛ` is its own
-- syntax size, `sizeᵛ` at an `obs` being `sizeᵉ` of what it holds.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

Pow : ℕ → Ty
Pow zero    = natᵗ
Pow (suc k) = Pow k ×ᵗ Pow k

pow : (k : ℕ) → Val Γ₁ (Pow k)
pow zero    = 0
pow (suc k) = pow k , pow k

bigObs : Val Γ₁ (obs (Pow 11))
bigObs = ofᵉ (reify {t = Pow 11} (pow 11) ∷ [])

vals₁ : List (Val Γ₁ (obs (Pow 11)))
vals₁ = bigObs ∷ []

-- THE THREE FIGURES THE ROW TURNS ON: the observable's own size, the
-- level one rung above a cap of sixty, and the ceiling that cap and a
-- width of sixty buy.
figures : List ℕ
figures = sizeᵛ (obs (Pow 11)) bigObs ∷ iterSize 60 1 60 ∷ frameCh 60 60 ∷ []

figures≡ : figures ≡ 4097 ∷ 7260 ∷ 3660 ∷ []
figures≡ = refl

-- LOAD-BEARING: the level premise is genuinely met, so the row is not
-- a claim about a reading no walk could have.  It would fail for a
-- value the level does not admit.
prem : valsSz? 7260 vals₁ ≡ true
prem = refl

-- LOAD-BEARING: and the count genuinely overruns.  Both sides are
-- numerals, so nothing here rests on a normal form.
count≡ : sum (map (sizeᵛ (obs (Pow 11))) vals₁) ≡ 4097
count≡ = refl

cross-count-ch-absurd : CrossCountCh → ⊥
cross-count-ch-absurd pr =
  ≤⇒≤ᵇ (pr {Γ = Γ₁} 60 60 7260
           (s≤s (s≤s z≤n)) (s≤s z≤n) (≤ᵇ⇒≤ 60 7260 tt)
           mergeAllᵒ 0 vals₁ refl (s≤s z≤n) prem)
