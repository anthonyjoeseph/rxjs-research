-- ══════════════════════════════════════════════════════════════════
-- THE SIGHTED CEILING'S TRADED SUM IS A NESTING MEASURE, SO IT CANNOT
-- BOUND A CLOSURE READING: the sum is gated by `nestDᵉ` and reads ZERO
-- on a telescope with no `*All` head, while the closure reading expands
-- every slot reference regardless of head.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  The subscribe-side ceiling prices a slot's
-- own BODY rather than counting slots -- `slotWrap (shared d) = 2 ^
-- syncSizeᵉ d * nestDᵉ d`, summed over the vocabulary and scaled by the
-- arrival's stratum.  That is the only quantity in the tier that looks
-- through the telescope, so the route was to read the closure key off
-- it: a value's closure under the traded sum at its own stratum, which
-- would make the frame head's resolved-size premise a corollary.
--
-- WHERE IT BREAKS.  Both factors of `slotWrap` are nesting-denominated
-- and the second is a plain `nestDᵉ`, so a slot whose definition wears
-- no `*All` head contributes NOTHING to the sum however large its body
-- is.  The arrival's own term of the trade is gated the same way.  So
-- the whole traded sum sits at zero on a pure-`map` vocabulary while
-- `closSizeᵉ` reads the definition per reference -- and the stratum
-- scale cannot repair it, because a factor on zero is zero at every
-- stratum, which is why the refuted form quantifies over `k`.
--
-- WHAT IT DOES NOT KILL.  Nothing about the ceiling itself: the sum is
-- correct for what it is for, a DESCENT bound, where a slot with no
-- nesting genuinely costs no depth.  What dies is the transport -- the
-- fan-out sees a quantity the sum does not, namely the slot body's
-- SIZE, and the ceiling has no term in that currency at all.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Clos-Wrap-Sum where

open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≤_)
open import Data.Nat.Properties using (*-zeroʳ)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; nat̂; strmᵗ; input; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Verify-Budget-Sufficient.Nest-Store using (slotWrapSum)

-- an OBSERVABLE-typed slot whose definition wears no `*All` head, so
-- the wrap reads it at zero however big the body is
Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

defn : Closed Γₛ (obs natᵗ)
defn = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

sl : Slots Γₛ
sl fzero = shared defn {ok = tt}

-- an arrival that merely NAMES the slot, and wears no `*All` head
-- either, so its own term of the trade is zero too
o : Val Γₛ (obs (obs (obs natᵗ)))
o = ofᵉ (strmᵗ (input fzero) ∷ [])

----------------------------------------------------------------------
-- THE TWO COLUMNS
----------------------------------------------------------------------

wrapSum≡ : slotWrapSum sl ≡ 0
wrapSum≡ = refl

ownNest≡ : nestDᵉ o ≡ 0
ownNest≡ = refl

closRead≡ : closSizeᵉ (slotClos sl) o ≡ 10
closRead≡ = refl

----------------------------------------------------------------------
-- THE STATEMENT, quantified over the stratum, since scaling zero is
-- what the route was really asking for
----------------------------------------------------------------------

Traded : ∀ {n} {Γ : Ctx n} {u} → Slots Γ → ℕ → Val Γ (obs u) → ℕ
Traded s k v = 2 ^ syncSizeᵉ v * nestDᵉ v + k * slotWrapSum s

traded≡ : ∀ (k : ℕ) → Traded sl k o ≡ 0
traded≡ k = *-zeroʳ k

clos-wrap-sum-absurd :
  (∀ {n} {Γ : Ctx n} {u} (s : Slots Γ) (k : ℕ) (v : Val Γ (obs u)) →
     closSizeᵉ (slotClos s) v ≤ Traded s k v) → ⊥
clos-wrap-sum-absurd f with f sl 4096 o
... | ()
