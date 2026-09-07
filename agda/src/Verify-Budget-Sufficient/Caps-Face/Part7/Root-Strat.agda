-- Verify-Budget-Sufficient.Caps-Face.Part7.Root-Strat
-- frameStrat-top … pathStrat-top
module Verify-Budget-Sufficient.Caps-Face.Part7.Root-Strat where

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (true)

open import Rx.Exp using (Ctx)
open import Rx.Evaluator using
  (Frame; map-f; scan-f; take-f; from-inner; thru-outer;
   Path; root; share-sink; _↠_)
open import Rx.Inputs-Below using (ib-topᵗ; ib-monoᵗ)
open import Decide using (T⇒≡true; ∧-intro)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (frameStrat?; pathFloor; pathStrat?)

-- WHY THIS IS ITS OWN MODULE AND NOT A PAIR OF LEMMAS BESIDE THE
-- PREDICATE THEY ARE ABOUT.  The proofs need `Rx.Inputs-Below`, whose
-- five mutual blocks are not in the cone of the module defining
-- `pathStrat?` -- and that module is imported almost everywhere on
-- this face, so the edge would be paid by every one of its consumers.
-- Measured on the module that consumes these two: sixty-three seconds
-- with the lemmas in a separate module against over eight minutes with
-- the edge added to the predicate's own, and the difference is the
-- edge rather than the bodies, which are five clauses of `refl`.

-- AND AT THE ROOT'S OWN FLOOR THE READING HAS NO CONTENT, WHICH IS
-- WHAT MAKES IT AFFORDABLE TO ASK FOR.  A frame names inputs of `Γ`
-- and nothing else, so `ib-topᵗ` puts every closure below `n` for
-- every program, and `ib-monoᵗ` carries that up to any floor at or
-- above `n`.  Only two frames carry syntax at all; the other three are
-- `true` by definition.
frameStrat-top : ∀ {n} {Γ : Ctx n} {s u} (k : ℕ) → n ≤ k →
  (f : Frame Γ s u) → frameStrat? k f ≡ true
frameStrat-top k le (map-f fn)         = T⇒≡true _ (ib-monoᵗ _ k le fn (ib-topᵗ fn))
frameStrat-top k le (scan-f fn _)      = T⇒≡true _ (ib-monoᵗ _ k le fn (ib-topᵗ fn))
frameStrat-top k le (take-f _)         = refl
frameStrat-top k le (from-inner _ _ _) = refl
frameStrat-top k le (thru-outer _ _)   = refl

-- SO THE PREDICATE'S WHOLE CONTENT SITS AT A `share-sink` TERMINAL.
-- `pathFloor` reports the TERMINAL's floor from anywhere along the
-- chain, so every frame of a root-terminated chain is charged at
-- exactly the bound it cannot exceed and no fact about the state is
-- spent.  At a sink the floor drops to the slot's index and a frame
-- naming any higher input fails -- which is the region a consumer has
-- to pay for, strictly smaller than the chain set the statements about
-- this predicate quantify over.
pathStrat-top : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) →
  n ≤ pathFloor p → pathStrat? p ≡ true
pathStrat-top root           h = refl
pathStrat-top (share-sink i) h = refl
pathStrat-top (f ↠ p)        h =
  ∧-intro (frameStrat-top (pathFloor p) h f) (pathStrat-top p h)
