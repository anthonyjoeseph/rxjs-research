-- THE SHARED-DEF PALETTE: which trees a slot table may draw a shared
-- definition from, and how such a definition is read back as a plain
-- tree.
--
-- WHY THIS EXISTS.  A `shared` slot carries a definition, and until now
-- that definition was an ARBITRARY `Closed Γ t`.  At an observable type
-- that is a hole no predicate on the author's term could ever see: the
-- TABLE, not the program, hands the run a tree nothing elaborated.  A
-- machine-checked table did exactly that --
--
--   shared (ofᵉ (strmᵗ (mintᵉ (ofᵉ (instEmitᵛ nilᵗ tok tok deliveryᵛ ∷ [])))
--                ∷ []))
--
-- under an ordinary `mergeAllˢ (inputˢ i)` drove the protocol automaton
-- to `nothing`: a `delivery` whose source no `init` ever enlisted.  The
-- author wrote nothing unusual.
--
-- WHY A PARAMETER AND NOT A RESTRICTION.  Narrowing `shared` in place
-- -- requiring `isData`, say -- closes the hole by DELETING the
-- observable-typed slot, and with it the ability to declare an input
-- that SUPPLIES observables.  That is a reduction in what the evaluator
-- can express, and the evaluator's scope is not the proof's to spend.
-- The palette instead lets the two live apart: the CLI, the generator
-- corpus and the unit tests run at `plainPalette`, where every plain
-- tree is a legal def and nothing is lost, while a THEOREM may be
-- stated over a narrower palette whose inhabitants provably cannot
-- forge.  Both instantiations coexist in one build.
--
-- `embed` CARRIES NO LAWS, and that is a fact about the evaluator
-- rather than an omission here.  The record is consumed in exactly two
-- places -- `subs-shared`, which subscribes the def, and
-- `red-input-shared`, which walks it -- and neither asks what `embed`
-- computes.  Termination survives the opacity because the shared-slot
-- descent is `<-wellFounded (gsizeᵉ (embed d))`: accessibility of a
-- NUMBER, which is a theorem however stuck that number is, and not a
-- structural measure that an abstract projection could defeat.
module Rx.Palette where

open import Rx.Exp using (Ty; Ctx; Closed)

record Palette : Set₁ where
  field
    -- the family a shared def may be drawn from
    Tree  : ∀ {n} → Ctx n → Ty → Set
    -- how the evaluator reads such a def as a plain tree
    embed : ∀ {n} {Γ : Ctx n} {t} → Tree Γ t → Closed Γ t

open Palette public

-- THE IDENTITY INSTANTIATION: every plain tree is a legal shared def.
-- This is the evaluator at full scope, and it is what the CLI, the
-- QuickCheck corpus and the unit tests run at.  It is also where the
-- forgery above is representable, which is the point: the run is not
-- where the restriction belongs.
plainPalette : Palette
plainPalette = record { Tree = λ Γ t → Closed Γ t ; embed = λ d → d }
