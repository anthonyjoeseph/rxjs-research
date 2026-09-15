-- A DEPTH READ OFF THE PROGRAM TEXT DOES NOT BOUND THE VALUES A RUN
-- EMITS, and the witness is a program with an rxjs source line:
-- `of(0,0,0).pipe(scan((acc, v) => of(acc).pipe(mergeAll()), EMPTY))`.
-- The template is behaviourally the identity on the accumulator and
-- genuinely one subscription hop deeper, so each delivery of the burst
-- hands back an observable wrapping the last — and the burst arrives
-- whole, from the seed, on the first delivery.
--
-- WHAT THIS KILLS, AND IT IS A ROUTE RATHER THAN A STATEMENT.  The
-- climb was already known: a sibling witness proves the accumulator
-- deepens once per element, for every burst length.  What it left open
-- was whether a RUN can ever stand a configuration that deep beside a
-- burst that long — and if it could not, the obligation dissolves by
-- restricting the claim to reachable configurations, bounding nothing
-- and costing no mathematics.  It can.  The configuration is reached by
-- a one-line plain rxjs pipeline at the shallowest input this language
-- can write, so excluding it would cost rxjs parity, which is the one
-- price this development does not pay.  The reachability move is dead.
--
-- AND THE FIGURES SAY WHAT REPLACES IT.  Two burst lengths are run
-- against one template.  The emitted depths are exactly the burst
-- POSITION, and the program's own reading holds still at one across
-- both — so the gap is not an offset that a wider margin absorbs, it is
-- a RATE in a quantity the reading does not carry.  The positive figure
-- beside the witness is the repair's shape, taken at the same point: a
-- bound denominated in the reading PLUS THE BURST LENGTH holds here,
-- and holds with one to spare rather than by slack, since the peak is
-- the last element's position.  That is evidence for the restatement
-- and not for the statement — it says what currency a repair has to be
-- written in, never that a repair in that currency is true.
--
-- The three figures are claimed because the finding is their
-- relationship: two depth lists and one static reading, where a repair
-- moving any single one would leave a witness reporting numbers that no
-- longer meet.
--
-- REFUTED: Refuted.Scan-Deepens — the climb this stands on, proven as a
--   rate over every burst length; this witness closes the reachability
--   question its own boundary paragraph left open
module Refuted.Scan-Reachable where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; concatMap; length)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _+_; z≤n; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit; InstEvent; value)
open import Rx.Exp using (Ctx; Closed; Val; Fn; Tm; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; varᵗ; nat̂; fstᵗ; strmᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Refuted.Apparatus using (obsDepthᵛ; obsDepthᵉ)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

-- the identity on the accumulator, one subscription hop deeper
bump : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
bump = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

inputs₃ inputs₅ : List (Tm Γ₀ [] [] [] natᵗ)
inputs₃ = nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ []
inputs₅ = nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ []

prog₃ prog₅ : Closed Γ₀ (obs natᵗ)
prog₃ = scanᵉ bump (strmᵗ emptyᵉ) (ofᵉ inputs₃)
prog₅ = scanᵉ bump (strmᵗ emptyᵉ) (ofᵉ inputs₅)

vals : List (InstEvent (Val Γ₀ (obs natᵗ))) → List (Val Γ₀ (obs natᵗ))
vals []              = []
vals (value v ∷ evs) = v ∷ vals evs
vals (_ ∷ evs)       = vals evs

runDepths : ℕ → Closed Γ₀ (obs natᵗ) → Slots Γ₀ → List ℕ
runDepths fuel e ins = map (obsDepthᵛ {Γ = Γ₀} (obs natᵗ))
  (concatMap (λ em → vals (InstEmit.events em)) (evaluate↓ fuel e ins))

depths₃ depths₅ : List ℕ
depths₃ = runDepths 100 prog₃ ins₀
depths₅ = runDepths 100 prog₅ ins₀

-- the run's own answer at both lengths: the emitted depth is the burst
-- position, so it grows with the burst rather than with the program
rows₃ : depths₃ ≡ 1 ∷ 2 ∷ 3 ∷ []
rows₃ = refl

rows₅ : depths₅ ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
rows₅ = refl

-- and the reading taken off the program text, which does not move
static₃ : obsDepthᵉ prog₃ ≡ 1
static₃ = refl

static₅ : obsDepthᵉ prog₅ ≡ 1
static₅ = refl

-- THE STATEMENT.  Every value a run emits is at most as deep as the
-- program it came from, read at the zero environment.  Quantified over
-- the fuel and the slots so that no instance of it can be rescued by
-- choosing either.
StaticBoundsRun : Set
StaticBoundsRun = ∀ (fuel : ℕ) (e : Closed Γ₀ (obs natᵗ)) (ins : Slots Γ₀) →
  All (_≤ obsDepthᵉ e) (runDepths fuel e ins)

static-bounds-run-false : StaticBoundsRun → ⊥
static-bounds-run-false claim with claim 100 prog₅ ins₀
... | _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ _ ∷ᴬ s≤s () ∷ᴬ []ᴬ

-- THE REPAIR'S CURRENCY, at the same point.  A bound carrying the burst
-- length beside the reading does hold here, and the peak is the last
-- element's position, so the margin is one rather than slack.
length-bound : All (_≤ obsDepthᵉ prog₅ + length inputs₅) depths₅
length-bound =
  s≤s z≤n ∷ᴬ
  s≤s (s≤s z≤n) ∷ᴬ
  s≤s (s≤s (s≤s z≤n)) ∷ᴬ
  s≤s (s≤s (s≤s (s≤s z≤n))) ∷ᴬ
  s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ᴬ []ᴬ
