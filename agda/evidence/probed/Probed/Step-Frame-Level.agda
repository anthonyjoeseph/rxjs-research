-- ══════════════════════════════════════════════════════════════════
-- ONE STEP PAYS FOR A REBUILD, and by a factor of eight at the worst
-- shape the caller's own premises admit.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT THE QUESTION IS.  A frame REBUILDS the values it passes on, so
-- the closure reading on its output cannot be taken at the cap its
-- inputs were read at, and that form is already dead at every cap at
-- once.  The repair states the output one level up.  Whether one level is
-- ENOUGH is arithmetic nobody had run: a rebuild costs the template
-- plus the argument plus a constructor, and what the level buys is a
-- single `iterSize` step.
--
-- WHAT MAKES THE ROWS ADVERSARIAL RATHER THAN CONVENIENT.  Both
-- factors of the rebuild are pushed to the ceiling the caller's own
-- premises permit and no further.  The template names the slot as
-- many times as the path pricing admits, since `pathSz?` charges the
-- frame's function against the same cap; and the slot's DEFINITION is
-- fattened, since the entry cap's base carries `slotsClos` as a
-- summand, so a fat slot raises the cap that has to pay for it as
-- fast as it raises the bill.  The product of the two is therefore
-- quadratic in the cap -- and a step is quadratic too, which is the
-- whole of why it fits.
--
-- WHAT IS COVERED IS THE CLOSURE CONJUNCT AND NOTHING ELSE, at a cap
-- standing in for the entry recurrence's own base floor rather than at
-- that recurrence: `sizeCount` is sealed, so no row can compute
-- `capsAt` and none claims to.  What the rows do establish is the
-- RATIO, which is the part the seal cannot change -- the floor is a
-- lower bound on the recurrence, and the step is monotone, so a
-- rebuild that fits over the floor fits over anything the recurrence
-- climbs to.
--
-- THE ROW AT THE SMALLEST SLOT IS DEGENERATE AND IS KEPT AS THE
-- BOUNDARY: at one copy the base cap already admits the rebuild, so
-- nothing there could have failed.  The two above it are
-- LOAD-BEARING -- the base cap REFUSES and the stepped cap admits --
-- which is what makes the level the thing being measured.
--
-- TARGET: step-frame-clos @68ae2a
-- REFUTED: Refuted.Step-Frame-Clos
-- ══════════════════════════════════════════════════════════════════
module Probed.Step-Frame-Level where

open import Data.Bool using (true; false; T)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Val; Fn; Tm; natᵗ; obs; ofᵉ; input;
  strmᵗ; varᵗ; nat̂; applyFn; sizeᵉ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Evaluator using (Path; root; _↠_; map-f; thru-outer; mergeAllᵒ)
open import Rx.Slots using (Slots; shared; slotsSize)
open import Rx.Slot-Clos using (slotClos; slotsClos)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestClosOK?; pathSz?)

------------------------------------------------------------------
-- the slot, whose DEFINITION is a parameter: `m` copies of a literal
------------------------------------------------------------------

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

leaf : Tm Γₛ [] [] [] (obs natᵗ)
leaf = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

copies : ℕ → List (Tm Γₛ [] [] [] (obs natᵗ))
copies zero    = []
copies (suc m) = leaf ∷ copies m

defn : ℕ → Closed Γₛ (obs natᵗ)
defn m = ofᵉ (copies m)

okc : ∀ m → T (inputsBelowᵉ 0 (defn m))
okc zero    = tt
okc (suc m) = okc m

slots : ℕ → Slots Γₛ
slots m fzero = shared (defn m) {ok = okc m}

------------------------------------------------------------------
-- the frame, whose TEMPLATE is a parameter: `k` references to the slot
-- beside the argument it was handed
------------------------------------------------------------------

tmpl : ℕ → List (Tm Γₛ [] [] (obs (obs natᵗ) ∷ []) (obs (obs natᵗ)))
tmpl zero    = varᵗ (here refl) ∷ []
tmpl (suc k) = strmᵗ (input fzero) ∷ tmpl k

fnk : ℕ → Fn Γₛ [] [] [] (obs (obs natᵗ)) (obs (obs (obs natᵗ)))
fnk k = strmᵗ (ofᵉ (tmpl k))

v₀ : Val Γₛ (obs (obs natᵗ))
v₀ = input fzero

out : ℕ → Val Γₛ (obs (obs (obs natᵗ)))
out k = applyFn (fnk k) v₀

prog : Closed Γₛ (obs (obs natᵗ))
prog = ofᵉ (strmᵗ (input fzero) ∷ [])

κ : ℕ → Path Γₛ (obs (obs natᵗ)) (obs (obs natᵗ))
κ k = map-f (fnk k) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

------------------------------------------------------------------
-- the cap: the entry recurrence's own base floor, at the same slots
------------------------------------------------------------------

base : ℕ → ℕ
base m = 2 + sizeᵉ prog + slotsSize (slots m) + slotsClos (slots m)

cap : ℕ → Caps
cap m = caps (base m) 4096 4096

------------------------------------------------------------------
-- the premises the caller carries, at the BASE cap
------------------------------------------------------------------

argOK₄ : nestClosOK? (cap 4) (slots 4) v₀ ≡ true
argOK₄ = refl

argOK₁₆ : nestClosOK? (cap 16) (slots 16) v₀ ≡ true
argOK₁₆ = refl

pathOK₄ : pathSz? (base 4) (κ 4) ≡ true
pathOK₄ = refl

pathOK₁₆ : pathSz? (base 16) (κ 16) ≡ true
pathOK₁₆ = refl

pathOK₆₇ : pathSz? (base 16) (κ 67) ≡ true
pathOK₆₇ = refl

------------------------------------------------------------------
-- DEGENERATE: at one copy the base cap already admits the rebuild
------------------------------------------------------------------

deg-base : nestClosOK? (cap 1) (slots 1) (out 1) ≡ true
deg-base = refl

------------------------------------------------------------------
-- LOAD-BEARING: the base cap REFUSES and one step admits
------------------------------------------------------------------

flat₄ : nestClosOK? (cap 4) (slots 4) (out 4) ≡ false
flat₄ = refl

step₄ : nestClosOK? (frameStep 1 (cap 4)) (slots 4) (out 4) ≡ true
step₄ = refl

flat₁₆ : nestClosOK? (cap 16) (slots 16) (out 16) ≡ false
flat₁₆ = refl

step₁₆ : nestClosOK? (frameStep 1 (cap 16)) (slots 16) (out 16) ≡ true
step₁₆ = refl

-- and with the template pushed to the cap the path pricing permits
flat₆₇ : nestClosOK? (cap 16) (slots 16) (out 67) ≡ false
flat₆₇ = refl

step₆₇ : nestClosOK? (frameStep 1 (cap 16)) (slots 16) (out 67) ≡ true
step₆₇ = refl

------------------------------------------------------------------
-- THE COLUMNS, packed base 10000: the floor, the rebuilt closure, and
-- what one step buys
------------------------------------------------------------------

floors : ℕ
floors = base 1 + 10000 * base 4 + 100000000 * base 16

rebuilds : ℕ
rebuilds = closSizeᵉ (slotClos (slots 1)) (out 1)
         + 10000 * closSizeᵉ (slotClos (slots 4)) (out 4)
         + 100000000 * closSizeᵉ (slotClos (slots 16)) (out 16)

worst : ℕ
worst = closSizeᵉ (slotClos (slots 16)) (out 67)
      + 100000 * Caps.cSize (frameStep 1 (cap 16))

floors≡ : floors ≡ 13900430019
floors≡ = refl

rebuilds≡ : rebuilds ≡ 115801020018
rebuilds≡ = refl

worst≡ : worst ≡ 3878104626
worst≡ = refl
