-- WHICH CURRENCY A REGISTERED CHAIN'S SIZE OBLIGATION IS OWED IN, AND
-- IT IS A CHOICE BETWEEN TWO READINGS OF ONE REGISTRY.  The walk hands
-- values to chains it did not walk, and it has to know something about
-- them before it may price the hand-over.  Two candidates read the same
-- registry.  The CAP reading asks each chain to be legal at the cap --
-- every frame's own syntax under it and the chain no longer than twice
-- it -- which is the predicate the face is written in today.  The
-- CHARGE reading asks only that the chain's priced potential fit the
-- budget the walk already affords at that cap, which is the quantity
-- the hand-over actually spends.  This is a FORK and not a receipt
-- because its product is that the two DISAGREE at a state the
-- evaluator reaches, not that either one held.
--
-- FORK: fan-regsSzL-mint
--
-- WHY THE DISAGREEMENT IS THE WHOLE POINT.  A subscribing frame swaps
-- its head for an inner-sourced one and pushes a frame per operator of
-- the inner, and the frame it pushes carries that operator's
-- transformer verbatim.  What bounds the inner is the receipt in hand,
-- which is taken at a cap the walk has already stepped -- so the
-- syntax a registration carries is a quantity from LATER in the
-- instant than the cap the hand-over is denominated at.  The cap
-- reading compares the two directly and loses.  The charge reading
-- never compares them: it asks a single number about the whole chain
-- against a budget that is exponential in the cap, and the exponent
-- has room for syntax the cap itself does not admit.
--
-- WHAT THE ROWS SAY.  At the reached registry the cap reading is false
-- at every cap up to and including forty-eight and turns true at
-- sixty-four, while the charge reading is false at two and true from
-- three upward.  So there is an interval more than an order of
-- magnitude wide in which the face's own predicate is unavailable and
-- the quantity the face actually spends is affordable.
--
-- WHAT THE ROWS DO NOT BUY.  Nothing about whether the charge reading
-- is RE-ESTABLISHABLE at registration, which is a producer obligation
-- and the real question the fork opens rather than closes.  Nothing
-- about a registry built by anything but this family -- a scan that
-- carries syntax as a value, under a merge -- and in particular
-- nothing about a chain that ends at a sink, since every chain here
-- ends at the root and the sink leaf's own cubic is therefore never
-- charged.  And nothing about the margin: the budget these rows are
-- read against is the walk's own at the cap named, not the instant's
-- potential, which is larger and sealed.
module Probed.Regs-Charge-Currency where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Evaluator using (EvalSt)
open import Verify-Budget-Sufficient.Walk-Factor using (pathSzL?; pathΦF)
open import Probed.Apparatus using (Separates; separates-at)
open import Refuted.Reg-Nest-Reached using (run)

----------------------------------------------------------------------
-- THE TWO CANDIDATES, AS FUNCTIONS OF THE CAP
----------------------------------------------------------------------

-- the predicate the face threads today: every frame under the cap and
-- the chain within twice it
capV : ℕ → Bool
capV B = all (λ en → pathSzL? B (proj₂ (proj₂ (proj₂ en))))
             (EvalSt.registry (run 5))

-- the quantity the hand-over actually spends: the chain's priced
-- potential against the walk's own budget at the same cap
chgV : ℕ → Bool
chgV B = all (λ en → pathΦF B (proj₂ (proj₂ (proj₂ en)))
                       ≤ᵇ 2 ^ ((B + B + (B + B)) * (suc B * B)))
             (EvalSt.registry (run 5))

----------------------------------------------------------------------
-- THE SEPARATION
----------------------------------------------------------------------

-- LOAD-BEARING.  It fails if the reached registry ever holds only
-- chains whose frames fit the cap they are read at, which is exactly
-- what the face assumes and what a subscribing frame breaks.
separates : Separates capV chgV
separates = separates-at 6 (λ ())

bits : List Bool → ℕ
bits = foldr (λ b acc → (if b then 1 else 0) + 2 * acc) 0

----------------------------------------------------------------------
-- THE INTERVAL, READ OFF AT BOTH ENDS
----------------------------------------------------------------------

-- LOAD-BEARING at every entry.  The first pair is the charge reading's
-- own crossing, which is what says it is not vacuously true: at a cap
-- of two the budget is smaller than one registered chain's charge.
-- The last pair is the cap reading's, which is what says it is not
-- vacuously false and so fixes the interval's upper end.  A row would
-- fail if the two readings crossed together, which is the shape a
-- single underlying obstacle would have produced.
interval : List Bool
interval = chgV 2 ∷ chgV 3
         ∷ capV 6 ∷ chgV 6
         ∷ capV 48 ∷ capV 64
         ∷ []

interval≡ : interval ≡ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ []
interval≡ = refl

-- DEGENERATE by construction and kept as the scale check: the cap
-- reading does not recover anywhere inside the interval, so the gap is
-- a gap and not a single awkward cap.
inside : ℕ
inside = bits (capV 3 ∷ capV 4 ∷ capV 8 ∷ capV 12 ∷ capV 16
             ∷ capV 24 ∷ capV 32 ∷ [])

inside≡ : inside ≡ 0
inside≡ = refl
