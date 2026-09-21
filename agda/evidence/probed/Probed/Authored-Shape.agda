-- IS THE AUTHORSHIP HYPOTHESIS IN THE FORM THE TWO LEAVES WILL WANT?
-- Three readings, taken before either leaf is ground.
module Probed.Authored-Shape where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; natᵗ; obs; Closed)
open import Rx.SExp using (emitᵗ)
open import Rx.Envelope using (machineEmitᵗ)
open import Rx.Authored using (Authᵉ; isEnvᵗ)
open import Rx.Palette.SExp using (sexpPalette)
open import Rx.Slots sexpPalette using (Slots; Slot; shared; embed)

------------------------------------------------------------------
-- READING 1: the hypothesis is CARRIED BY THE TYPE, not by a premise.
------------------------------------------------------------------

-- `Sched` holds `slots : Slots Γ`, and at this palette a `shared` slot
-- cannot be built without its authorship.  So EVERY `Sched Γ` in scope
-- already has authored slots, and `cascade-shaped` -- which quantifies
-- over an arbitrary `sched′` with no tie to the root's `ins` -- needs
-- no new premise.  Extraction at the point of use is the second
-- projection and nothing more.
slot-authored : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (i : Fin n)
                  {d : Σ (Closed Γ _) Authᵉ} {ok} →
                ins i ≡ shared d {ok = ok} → Authᵉ (embed d)
slot-authored ins i {d} _ = proj₂ d

------------------------------------------------------------------
-- READING 2: the bar PROVABLY engages at the stamp's own type.
------------------------------------------------------------------

-- `inputᵖ`'s deliveries arm carries
--   stamp = strmᵗ (mintᵉ (ofᵉ (instEmitᵛ evs inst srcᵍ deliveryᵛ ∷ [])))
-- (Rx.Elaborate), and that `strmᵗ` stands at `obs (machineEmitᵗ a)` --
-- an ENVELOPE type.  So `auth-strm`'s side condition is uninhabited
-- there and only `auth-strmᵉ` can apply.
stamp-is-barred : T (not (isEnvᵗ (machineEmitᵗ natᵗ))) → ⊥
stamp-is-barred x = x

------------------------------------------------------------------
-- READING 3: therefore `Elabᵉ` is ESSENTIAL, and the induction is
-- two-layer.
------------------------------------------------------------------

-- The consequence of reading 2 is the one that shapes the grind.  An
-- elaborated tree contains envelope-typed `strmᵗ`s that are NOT
-- elaborations of any `SExp` -- `mintᵉ (ofᵉ (instEmitᵛ …))` is built by
-- `inputᵖ`, not by `toPlain` -- so `Authᵉ` is NOT closed structurally
-- over the image of the elaboration, and `auth-elab` is an opaque
-- escape rather than a convenience.
--
-- SO NEITHER LEAF CAN BE AN INDUCTION ON `Authᵉ` ALONE.  At an
-- `auth-elab` node the derivation stops handing over subterms and the
-- proof must switch to an induction on the `SExp` the node carries;
-- at a structural node it recurses as usual.  The two interleave,
-- because an authored tree may carry elaborations and an elaboration's
-- slots may hold authored trees.
--
-- AND THE INTERLEAVING TERMINATES, by the measure already in the
-- telescope rather than a new one: slot k's definition may reference
-- only inputs strictly below k (`inputsBelowᵉ`, Rx.Slots), so each hop
-- from an elaboration into a slot's authored definition strictly drops
-- the slot ceiling.  That is the same stratification `red-input-shared`
-- buys its descent from, which is the one arm of Rx.Evaluator.Reducible
-- whose termination is paid for ENTIRELY by the telescope's order.
