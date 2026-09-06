-- ══════════════════════════════════════════════════════════════════
-- A CHAIN'S WALK CANNOT BE READ AT THE WIDTH OF THE INSTANT IT RUNS
-- IN, ONCE THE BURST PACKAGE IS THE ONE THE CASCADE HANDS OVER.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
-- ══════════════════════════════════════════════════════════════════

-- WHAT THE STATEMENT SAYS.  The walk's ledger needs a burst width at
-- every frame -- once for its own head conjunct and once to pay a
-- scan, which is a width times a size -- and the caps package a chain
-- carries does not report one.  What DOES report one is the cascade's
-- own burst package, delivered at `nestBurstAt`.  So the transport
-- that would close the ledger is a width descent: from the width the
-- cascade hands over to the size cap the walk is otherwise read at,
-- both at the same instant.  Every conjunct of the walk's burst
-- predicate is upward-closed in that width, so a descent is the only
-- direction that could carry it, and this row is that descent as a
-- bare inequality.

-- WHERE IT BREAKS, AND IT IS THE LADDER RATHER THAN A PROGRAM.  The
-- burst the cascade reports is the size cap ONE INSTANT UP -- not
-- merely bounded by it, but equal to it -- and the caps ladder's own
-- proven climb puts one instant of it past a POWER of the instant
-- below, at an exponent the same ladder proves is at least two.  So
-- the descent asks a cap to be no smaller than its own cube, at a cap
-- this tower proves exceeds a hundred.  Nothing about the program
-- enters: the witness below is the empty program at the first instant
-- only because the hypothesis is universally quantified and needs a
-- point, and every other point refutes it identically.

-- SO THE REPAIR IS NOT AT THE WIDTH COORDINATE, WHICH IS THE PART
-- WORTH CARRYING.  Reading the row as a rung to be crossed invites
-- three moves that are all closed by the same arithmetic: tightening
-- what the cascade reports, since it reports an equality; widening
-- what the walk is read at, since that is the instant's own cap and
-- moving it moves the ladder; and interposing a bound between them,
-- since a power of the cap admits nothing under the cap.  What is
-- left is the CONSUMER: the walk's ledger may be read at the wider
-- width, and then its ceiling has to afford a frame charge stated in
-- that width instead of in the cap.

-- WHAT THIS DOES NOT SHOW.  It says nothing about whether the walk's
-- bursts are in fact within the instant's own cap -- that is a claim
-- about what an evaluator delivers, and it may well be true.  What it
-- refutes is deriving it from the package the cascade hands over,
-- which is the only proven source of a burst bound at a chain.  Nor
-- does it reach the ledger's OTHER two residues, the crossing charge
-- and the registry term, which are unrelated arithmetic.

module Refuted.Walk-Burst-Rung where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _^_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; 1+n≰n; n≤1+n;
  ^-monoʳ-<; ^-identityʳ)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (sym; cong)

open import Rx.Exp using (Ctx; Closed; natᵗ; emptyᵉ)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Caps
  using (Caps; capsAt; capsH; sizeCount; 2≤sizeCount; 2≤capsAt-size;
         1≤capsAt-reg)
open import Verify-Budget-Sufficient.Nest-Store
  using (nestBurstAt; nestBurstAt-def)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith
  using (capsAt-size-lower)

----------------------------------------------------------------------
-- THE DESCENT, STATED AT EVERY PROGRAM AND EVERY INSTANT, since that
-- is the shape a transport for the walk's ledger would have to have:
-- one lemma spent at whatever instant the chain is entered at.
----------------------------------------------------------------------

WidthAtOwnInstant : Set
WidthAtOwnInstant = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) → nestBurstAt e sl id ≤ Caps.cSize (capsAt e sl id)

----------------------------------------------------------------------
-- THE LADDER'S OWN CLIMB, AT AN ARBITRARY POINT.  Both halves come off
-- proven statements of this tower, so the crossing below is not read
-- off numerals that a repair to a measure could move underneath it.
----------------------------------------------------------------------

module _ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) where

  S : ℕ
  S = Caps.cSize (capsAt e sl id)

  K : ℕ
  K = sizeCount (capsAt e sl id) (capsH e sl id)

  2≤S : 2 ≤ S
  2≤S = 2≤capsAt-size e sl id

  -- LOAD-BEARING: the exponent is what makes the descent absurd rather
  -- than merely unproven.  At an exponent of one the climb would admit
  -- an equality and this row would say nothing.
  2≤K : 2 ≤ K
  2≤K = 2≤sizeCount (capsAt e sl id) (capsH e sl id) 2≤S
          (1≤capsAt-reg e sl id)

  1<sucK : 1 < suc K
  1<sucK = ≤-trans 2≤K (n≤1+n K)

  -- LOAD-BEARING: the cap is strictly under its own climb, so no
  -- reading of the width at the instant below can hold the one above.
  S<climb : S < S ^ suc K
  S<climb = ≤-trans (≤-reflexive (cong suc (sym (^-identityʳ S))))
                    (^-monoʳ-< S 2≤S 1<sucK)

  -- LOAD-BEARING: the cascade's burst IS the next instant's cap, so
  -- the climb sits under the width the package reports rather than
  -- merely near it.
  climb≤burst : S ^ suc K ≤ nestBurstAt e sl id
  climb≤burst = ≤-trans (capsAt-size-lower e sl id)
                        (≤-reflexive (sym (nestBurstAt-def e sl id)))

----------------------------------------------------------------------
-- THE WITNESS.  The empty program at the first instant, chosen only
-- because a universally quantified hypothesis needs a point: nothing
-- above reads the program, so any point refutes it.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

sl₀ : Slots Γ₀
sl₀ ()

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

walk-burst-rung-absurd : WidthAtOwnInstant → ⊥
walk-burst-rung-absurd pr =
  1+n≰n (≤-trans (S<climb e₀ sl₀ 0)
                 (≤-trans (climb≤burst e₀ sl₀ 0) (pr e₀ sl₀ 0)))
