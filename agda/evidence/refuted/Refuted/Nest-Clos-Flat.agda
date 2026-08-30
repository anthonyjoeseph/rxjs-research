-- ══════════════════════════════════════════════════════════════════
-- A VALUE'S SYNTAX DOES NOT BOUND ITS CLOSURE, so reading the closure
-- measure off the SAME flat cap the syntax is charged against is FALSE
-- at every cap at once.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A value admitted by `valCaps? c` -- its
-- syntactic size under `cSize c`, its width under `cWid c` -- also
-- satisfies `nestClosOK? c`, which reads the same value through the
-- slot telescope.  The two coincide on a slot-free value, which is
-- what makes the reading look like a repackaging of the receipt.
--
-- WHERE IT BREAKS, AND THE GAP GROWS WITH THE VALUE.  `sizeᵉ (input i)`
-- is one whatever the slot holds, while `closSizeᵉ` reads that leaf as
-- the whole definition.  So a value is charged one per reference and
-- credited the definition per reference, and the deficit scales with
-- the number of leaves rather than sitting at a constant: the three
-- rows below carry one, two and three references to the same slot and
-- read `4 6 8` of syntax against `10 18 26` of closure -- a deficit of
-- six per reference, so no summand and no larger cap repairs it.
--
-- WHY THE CAP CANNOT BE RAISED TO FIX IT.  The refuted form is stated
-- over an ARBITRARY `c`, and the witness cap is `sizeᵉ` of the value
-- itself, so the premise is met exactly and by construction at every
-- size the family reaches.  Raising the cap raises the admitted value
-- with it.
--
-- WHAT THIS DOES NOT KILL.  It says nothing about the reading under a
-- cap that is not the value's own -- `capsAt`'s size is an `iterSize`
-- at a count that already dominates the telescope, and whether it
-- dominates the telescope PER REFERENCE is the open question this
-- leaves standing.
-- What dies is the cap-agnostic route: no proof of the closure reading
-- can go through `valCaps?` alone, so the specific size of `capsAt` is
-- the only thing left that could pay for it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Clos-Flat where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; nat̂; strmᵗ; input; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (valCaps?; nestClosOK?)

-- an OBSERVABLE-typed slot, so a reference to it is a value the walk
-- can actually be handed
Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

-- a definition strictly bigger than the reference that names it
defn : Closed Γₛ (obs natᵗ)
defn = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

sl : Slots Γₛ
sl fzero = shared defn {ok = tt}

----------------------------------------------------------------------
-- THE FAMILY: one, two and three references to the same slot
----------------------------------------------------------------------

o₁ : Val Γₛ (obs (obs (obs natᵗ)))
o₁ = ofᵉ (strmᵗ (input fzero) ∷ [])

o₂ : Val Γₛ (obs (obs (obs natᵗ)))
o₂ = ofᵉ (strmᵗ (input fzero) ∷ strmᵗ (input fzero) ∷ [])

o₃ : Val Γₛ (obs (obs (obs natᵗ)))
o₃ = ofᵉ (strmᵗ (input fzero) ∷ strmᵗ (input fzero) ∷ strmᵗ (input fzero) ∷ [])

----------------------------------------------------------------------
-- THE CAP IS THE VALUE'S OWN SIZE, so the premise holds by refl and
-- the witness is not a corner of some chosen number
----------------------------------------------------------------------

c₀ : Caps
c₀ = caps (sizeᵉ o₃) 4096 4096

premise : valCaps? c₀ sl (obs (obs (obs natᵗ))) o₃ ≡ true
premise = refl

broken : nestClosOK? c₀ sl o₃ ≡ false
broken = refl

nest-clos-flat-absurd :
  (∀ {n} {Γ : Ctx n} {u} (c : Caps) (s : Slots Γ) (o : Val Γ (obs u)) →
     valCaps? c s (obs u) o ≡ true →
     nestClosOK? c s o ≡ true) → ⊥
nest-clos-flat-absurd f with f c₀ sl o₃ premise
... | ()

----------------------------------------------------------------------
-- THE TWO COLUMNS, packed base 100: syntax against closure
----------------------------------------------------------------------

syntaxes : ℕ
syntaxes = sizeᵉ o₁ + 100 * sizeᵉ o₂ + 10000 * sizeᵉ o₃

closures : ℕ
closures = closSizeᵉ (slotClos sl) o₁ + 100 * closSizeᵉ (slotClos sl) o₂
         + 10000 * closSizeᵉ (slotClos sl) o₃

syntaxes≡ : syntaxes ≡ 80604
syntaxes≡ = refl

closures≡ : closures ≡ 261810
closures≡ = refl
