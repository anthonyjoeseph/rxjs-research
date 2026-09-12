-- A STEP WHOSE EMISSION IS ITSELF A FOLD ESCAPES THE SWAPPED READING
-- TOO, SO THE EXPONENT WAS NOT THE WHOLE OF WHAT WAS FALSE.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- THE ESCAPE IS THE ONE THE LIVE READING DIED OF, ONE CLAUSE ACROSS.  A
-- frame's emissions are not subterms of the term it entered on: a fold
-- builds its accumulator at RUN time, so what the frame hands out is a
-- term the entry never read.  The sibling family's step emits a MERGE,
-- whose reading is the nesting it writes, and the swapped exponent
-- covers that.  A step emitting a SCAN hands out a term whose own
-- exponent is read off ITS source — and that source is the accumulator,
-- which the entry sees only as a VARIABLE.  A variable delivers zero, so
-- the entry prices the emitted fold's exponent at one and the run pays
-- it in full, once per refold.
--
-- WHAT THE TWO FAMILIES SEPARATE.  The narrow one puts a single
-- reference to the accumulator under the emitted fold: the run's depth
-- climbs to three halves of the reading, so the reading is TIGHT at one
-- literal and crossed at two.  That much a coefficient could repair.
-- The wide one puts two, which doubles the emitted fold's exponent per
-- refold while leaving the entry's reading untouched — the same reading,
-- to the numeral — so what crosses there is the RATE and no coefficient
-- reaches it.  The pair is what makes this decisive rather than an
-- off-by-one: the first says the swap is wrong, the second says it is
-- not wrong by a constant.
--
-- THE BOUNDARY.  One flattener, one shape of emitted fold, and an
-- accumulator reached through a merge.  Nothing here reaches a step
-- emitting a MAP or a TAKE, whose clauses carry no exponent at all, and
-- nothing sweeps a switch or an exhaust root.
--
-- FORK: dry-operator
module Probed.Step-Fold where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Fn; obs; natᵗ; _×ᵗ_;
                         ofᵉ; scanᵉ; mergeAllᵉ;
                         varᵗ; nat̂; fstᵗ; strmᵗ)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Swapped-Exponent using (hopD′ᵉ; carried′; ν₀; η₀)
open import Refuted.Sync-Count using (Γ₀; ins₀; liveSeed)
open import Refuted.Root-Refold using (burstAt)

----------------------------------------------------------------------
-- THE STEP.  Its body is a fold, and the fold's source is the
-- accumulator it was handed — reached the only way a term of observable
-- type reaches an expression position, through a flattener.  At the
-- entry that source is a VARIABLE, so the reading charges the emitted
-- fold an exponent of zero; at the run it is the whole accumulator.
----------------------------------------------------------------------

-- the emitted fold's own step, as small as it can be: the accumulator
-- through, so nothing below is an artefact of what the inner step
-- writes
inner : Fn Γ₀ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (natᵗ ×ᵗ natᵗ) natᵗ
inner = fstᵗ (varᵗ (here refl))

stepN : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepN = strmᵗ (scanᵉ inner (nat̂ 0)
                (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))

stepW : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepW = strmᵗ (scanᵉ inner (nat̂ 0)
                (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                                         fstᵗ (varᵗ (here refl)) ∷ []))))

----------------------------------------------------------------------
-- THE TWO FAMILIES, differing in literals alone, exactly as the
-- refutation's does — so every row moves the refolds and leaves the step
-- fixed.
----------------------------------------------------------------------

narrow₁ narrow₂ narrow₃ narrow₄ : Closed Γ₀ (obs natᵗ)
narrow₁ = scanᵉ stepN liveSeed (ofᵉ (nat̂ 0 ∷ []))
narrow₂ = scanᵉ stepN liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))
narrow₃ = scanᵉ stepN liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))
narrow₄ = scanᵉ stepN liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

wide₁ wide₂ : Closed Γ₀ (obs natᵗ)
wide₁ = scanᵉ stepW liveSeed (ofᵉ (nat̂ 0 ∷ []))
wide₂ = scanᵉ stepW liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

----------------------------------------------------------------------
-- THE READING, AND IT IS THE SAME NUMBER FOR BOTH FAMILIES.  Each row
-- is LOAD-BEARING and could have failed either way: a reading that saw
-- the emitted fold's source would differ between the two steps, and one
-- that stopped growing with the literals would say the outer exponent
-- has gone flat again.  That it moves with the outer source and not with
-- the inner one is exactly the blindness under test.
----------------------------------------------------------------------

_ : hopD′ᵉ ν₀ η₀ narrow₁ ≡ 3                           -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ narrow₂ ≡ 9                           -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ narrow₃ ≡ 27                          -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ narrow₄ ≡ 81                          -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ wide₁ ≡ 3                             -- LOAD-BEARING
_ = refl

_ : hopD′ᵉ ν₀ η₀ wide₂ ≡ 9                             -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- WHAT THE RUN HANDS OUT.  Each row is LOAD-BEARING: a depth that
-- stalled would say the emitted fold does not re-wrap what it is handed,
-- and one that matched the reading would say the entry prices the
-- emitted exponent after all.  The narrow family climbs by a factor of
-- three plus a constant per refold; the wide one squares its own
-- exponent per refold, on the same reading.
----------------------------------------------------------------------

_ : carried′ ν₀ η₀ (burstAt 1 narrow₁ ins₀) ≡ 3        -- LOAD-BEARING
_ = refl

_ : carried′ ν₀ η₀ (burstAt 1 narrow₂ ins₀) ≡ 12       -- LOAD-BEARING
_ = refl

_ : carried′ ν₀ η₀ (burstAt 1 narrow₃ ins₀) ≡ 39       -- LOAD-BEARING
_ = refl

_ : carried′ ν₀ η₀ (burstAt 1 narrow₄ ins₀) ≡ 120      -- LOAD-BEARING
_ = refl

_ : carried′ ν₀ η₀ (burstAt 1 wide₁ ins₀) ≡ 9          -- LOAD-BEARING
_ = refl

_ : carried′ ν₀ η₀ (burstAt 1 wide₂ ins₀) ≡ 810        -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CROSSING.  The first row HOLDS, and tightly — three against
-- three — which is what says the guard is deciding on the refolds and
-- not on the family; the rest are false.  Pinned by `refl` so that they
-- move visibly if either side does.
----------------------------------------------------------------------

_ : (carried′ ν₀ η₀ (burstAt 1 narrow₁ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ narrow₁) ≡ true
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 narrow₂ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ narrow₂) ≡ false
_ = refl

_ : (carried′ ν₀ η₀ (burstAt 1 narrow₄ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ narrow₄) ≡ false
_ = refl

-- the rate, not the coefficient: the same reading, and a depth ninety
-- times it one refold later
_ : (carried′ ν₀ η₀ (burstAt 1 wide₂ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ wide₂) ≡ false
_ = refl

-- the degenerate bound, so nothing above rests on the store having room
_ : (carried′ ν₀ η₀ (burstAt 0 narrow₂ ins₀) ≤ᵇ hopD′ᵉ ν₀ η₀ narrow₂) ≡ false
_ = refl

----------------------------------------------------------------------
-- THE FORK.  The choice is between a depth READ AT THE DOOR off the
-- term the frame is entered on and one the walk would have to CARRY
-- beside the emissions it builds.  The sibling refutation takes that
-- pair apart at the live reading; these rows retake it at the swapped
-- one, which is the whole of what changed, and they are apart at the
-- first term the swap fails on.
----------------------------------------------------------------------

Point : Set
Point = Closed Γ₀ (obs natᵗ)

entryRead runReport : Point → ℕ
entryRead  e = hopD′ᵉ ν₀ η₀ e
runReport  e = carried′ ν₀ η₀ (burstAt 1 e ins₀)

step-fold-fork : Separates entryRead runReport
step-fold-fork = separates-at narrow₂ (λ ())
