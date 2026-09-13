-- THE INPUT BOUND SURVIVES A μ-UNFOLD, AT THE ONE FLOOR WHERE IT COULD
-- HAVE FAILED.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THE FLOOR HAS TO SIT STRICTLY INSIDE THE CONTEXT.  Every other
-- clause of the bound is a fold over children, so an unfold is the one
-- place a term ENTERS another rather than being walked into — and at the
-- context's own size the claim is FREE, since the root's witness proves
-- it of every term the syntax admits.  So every row below stands at a
-- context of three with the floor strictly inside it, leaving at least
-- one slot the predicate would reject and that a substitution reaching
-- for the wrong variable could land on.
--
-- WHAT MAKES THE ROWS LOAD-BEARING RATHER THAN TIDY.  The predicate at
-- these programs is not constantly true: the negative control fixes the
-- same unfolded term at floor zero and the predicate computes to
-- `false`, so the empty type really is reachable along this conclusion
-- and a green row is a reading rather than a vacuity.  The two positive
-- rows then differ in how much slack the floor leaves — one slot named
-- against two spare, and two named against one — so a graft drifting by
-- a single position fails the tighter row while the looser one stays
-- green, which is what makes the pair a reading of the bound rather
-- than of the unfold's shape.
--
-- NOT COVERED, and it is the axis the harness cannot reach cheaply: a
-- nested μ, where `elimGExp` walks under a second binder and the graft
-- index is `there`.  Every row here is one binder deep.
--
-- TARGET: below-unfoldμ @24734a
module Probed.Unfold-Bound where

open import Data.Bool using (false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Exp; natᵗ; input; ofᵉ; mergeAllᵉ; varᵉ; deferᵉ; strmᵗ; inputsBelowᵉ; unfoldμ)
open import Rx.Inputs-Below using (below-unfoldμ)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT AND THE TWO BODIES.  `low` names only the slot below the
-- floor the rows stand at; `both` names the slot above it too, so the
-- pair separates a bound that is CARRIED from one that is merely not
-- contradicted.  Each reaches its own binding through `deferᵉ`, which
-- is the only gate that lets a graft variable be named at all.
----------------------------------------------------------------------

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

low : Exp Γ₃ (natᵗ ∷ []) [] [] natᵗ
low = mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ []))

both : Exp Γ₃ (natᵗ ∷ []) [] [] natᵗ
both = mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (input (suc zero))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ []))

----------------------------------------------------------------------
-- THE NEGATIVE CONTROL, first, because it is what the two rows under it
-- are read against.  Nothing is claimed by it beyond the conclusion's
-- own falsifiability at these programs: drop the floor to zero and the
-- unfolded term's bound computes to `false`, so `T` of it is empty.
----------------------------------------------------------------------

ground : inputsBelowᵉ 0 (unfoldμ low) ≡ false     -- LOAD-BEARING
ground = refl

----------------------------------------------------------------------
-- THE ROWS.  Each is the target applied at this probe's own point, so
-- Agda generates the type from the statement as it reads and a
-- restatement moves both of them.
----------------------------------------------------------------------

carriesLow : Confirms (below-unfoldμ {Γ = Γ₃} 1 low tt)
carriesLow = tt

carriesBoth : Confirms (below-unfoldμ {Γ = Γ₃} 2 both tt)
carriesBoth = tt
