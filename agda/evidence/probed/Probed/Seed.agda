-- THE SEED, INSTANTIATED — the rows that ask whether a run's own values
-- stay under the rank, now that the reading which used to answer that by
-- proxy is refuted.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
-- TARGET: drain-dry-free @140a87
--
-- WHY THIS REGION.  The machine seeds the ROOT's rank at `2 ^ (sizeᵉ e +
-- slotsSize sl)` and peels ONE per inner-subscribe hop, so the guard
-- holds exactly while the values a run produces stay under that count.
-- An arrival re-enters at that exponent plus its own reading, so every
-- row below reads against the SMALLER of the two entries and the margin
-- it reports is the conservative one.
-- Nothing had ever instantiated it: the claim that an emitted inner reads
-- strictly under its emitter was doing the job, and `Refuted.Burst-Nesting`
-- killed it at a scan whose step re-wraps its own accumulator.  These rows
-- take that same shape — the one place the nesting is known to GROW along
-- a run — and read the growth against the seed rather than against the
-- emitter.
--
-- WHAT `carried` READS, and why it is the honest quantity.  A burst is a
-- stream of emits and an emit at an observable type carries closed
-- expressions, so the measure applies to the payloads unchanged; two
-- payloads abreast cost what the deeper costs, which is the list clause
-- the measure itself uses.  That makes this the FRIENDLIEST reading
-- available — a sum would only report a larger number, and the claim
-- being instantiated is an upper bound.
--
-- THE GROWTH LAW IS WHAT THESE ROWS ARE FOR, and it is the M3/M6 pair
-- that states it.  One extra delivery costs ONE nesting layer and buys
-- ONE doubling of the seed, because the literal that produces the
-- delivery is counted in `sizeᵉ` and the seed is exponential in that.
-- Three literals against six: the carried nesting goes 3 to 6 while the
-- seed goes 2^14 to 2^17.  The margin does not merely hold, it widens
-- multiplicatively in the one parameter that moves both sides — which is
-- the shape a proof would have to encode, and the reason the hop is
-- payable out of the seed at all.
--
-- EVERY ROW IS LABELLED, because a row that could not have failed is not
-- a row.  A `≤ᵇ` row is DEGENERATE by itself, since `0 ≤ᵇ n` is `true`
-- for every `n` and a burst that emitted nothing reads zero.  What makes
-- each one load-bearing is the POSITIVE reading pinned beside it: the
-- carried figure says the fold walked something, and it is free, since
-- the crossing forced it already.
--
-- WHAT IS NOT COVERED.  These are flat scans at an operator root; no `μᵉ`
-- appears, so the unfolding guard is untouched here and `Probed.Descent`
-- is where that lives.  Nor is the slot axis swept: one scripted source
-- is enough to put deliveries on the DRAIN rather than in the subscribe
-- frame, which is the only thing about it these rows need.
module Probed.Seed where

open import Data.Bool using (true)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; sizeᵉ;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
  strmᵗ; nat̂; fstᵗ; varᵗ; input)
open import Rx.Slots using (Slots; slotsSize; scripted)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The two quantities the rows compare: how deep the values a run hands
-- out actually read, and what the ROOT is seeded at.
----------------------------------------------------------------------

evNest : ∀ {n} {Γ : Ctx n} {u} → List (InstEvent (Closed Γ u)) → ℕ
evNest []             = 0
evNest (value v ∷ es) = nestDᵉ v ⊔ evNest es
evNest (_ ∷ es)       = evNest es

carried : ∀ {n} {Γ : Ctx n} {u} → Stream Γ (obs u) → ℕ
carried []         = 0
carried (em ∷ ems) = evNest (InstEmit.events em) ⊔ carried ems

seed : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
seed e sl = 2 ^ (sizeᵉ e + slotsSize sl)

----------------------------------------------------------------------
-- The two halves a run splits into, named once so a row can point at
-- either.  `entry` is the root subscribe the evaluator performs before
-- it drains, so `burstOf` is what the subscribe frame carries and
-- `drainOf` is what `drain-dry-free` is about everywhere.
----------------------------------------------------------------------

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt e
entry e ins = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins = proj₁ (entry e ins)

FUEL : Fuel
FUEL = 30

drainOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
drainOf e ins = drain FUEL 1 (proj₁ (proj₂ (entry e ins))) (proj₂ (proj₂ (entry e ins)))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE STEP FUNCTIONS.  Each hands its accumulator straight back inside
-- ONE flattening layer, so the value it emits reads one deeper than the
-- value before it while the term is charged for that layer once.  The
-- three differ only in WHICH layer, which is the axis the leaf's own
-- shape predicate admits and the one thing separating them here.
----------------------------------------------------------------------

stepM : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepM = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

stepS : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepS = strmᵗ (switchAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

stepX : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepX = strmᵗ (exhaustAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

----------------------------------------------------------------------
-- M3 — the refutation's own program, read against the seed instead of
-- against its emitter.  The crossing that killed the emitter reading is
-- the first two rows here: the term reads 1 and its burst reads 3.  What
-- is new is the third, which is what the machine actually compares
-- against, and it is four orders of magnitude clear.
----------------------------------------------------------------------

progM3 : Closed Γ₀ (obs natᵗ)
progM3 = scanᵉ stepM (strmᵗ emptyᵉ) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

_ : nestDᵉ progM3 ≡ 1                                  -- LOAD-BEARING
_ = refl

_ : carried (burstOf progM3 ins₀) ≡ 3                  -- LOAD-BEARING
_ = refl

_ : seed progM3 ins₀ ≡ 16384                           -- LOAD-BEARING
_ = refl

_ : (carried (burstOf progM3 ins₀) ≤ᵇ seed progM3 ins₀) ≡ true
_ = refl                                               -- LOAD-BEARING


----------------------------------------------------------------------
-- M6 — THE GROWTH ROW, and the only one here that says something a
-- single program cannot.  Three more literals in the same three-line
-- term: the reading of the TERM does not move, the burst's reading goes
-- up by three, and the seed goes up by a factor of eight.  One delivery,
-- one layer, one doubling — so the parameter that drives the growth is
-- the parameter the seed is exponential in, and the gap cannot be closed
-- by making the source longer.
----------------------------------------------------------------------

progM6 : Closed Γ₀ (obs natᵗ)
progM6 = scanᵉ stepM (strmᵗ emptyᵉ)
  (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ []))

_ : nestDᵉ progM6 ≡ 1                                  -- LOAD-BEARING
_ = refl

_ : carried (burstOf progM6 ins₀) ≡ 6                  -- LOAD-BEARING
_ = refl

_ : seed progM6 ins₀ ≡ 131072                          -- LOAD-BEARING
_ = refl

_ : (carried (burstOf progM6 ins₀) ≤ᵇ seed progM6 ins₀) ≡ true
_ = refl                                               -- LOAD-BEARING


----------------------------------------------------------------------
-- S3 and X3 — the same fold re-wrapping under the other two flattening
-- strategies.  They agree with the merge emit for emit, because the
-- accumulator handed back is SYNCHRONOUS and completes before the next
-- delivery arrives, so a switch has nothing live to drop and an exhaust
-- nothing live to block.  The rows stay: they reach the rank peel
-- through different registry clauses, which is what the leaf's shape
-- predicate quantifies over, and identical output is not identical
-- descent.
----------------------------------------------------------------------

progS3 : Closed Γ₀ (obs natᵗ)
progS3 = scanᵉ stepS (strmᵗ emptyᵉ) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

_ : carried (burstOf progS3 ins₀) ≡ 3                  -- LOAD-BEARING
_ = refl

_ : (carried (burstOf progS3 ins₀) ≤ᵇ seed progS3 ins₀) ≡ true
_ = refl                                               -- LOAD-BEARING


progX3 : Closed Γ₀ (obs natᵗ)
progX3 = scanᵉ stepX (strmᵗ emptyᵉ) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

_ : carried (burstOf progX3 ins₀) ≡ 3                  -- LOAD-BEARING
_ = refl

_ : (carried (burstOf progX3 ins₀) ≤ᵇ seed progX3 ins₀) ≡ true
_ = refl                                               -- LOAD-BEARING


----------------------------------------------------------------------
-- A — THE SAME FOLD FED FROM SCRIPTED SLOT DATA, which is the shape the
-- three above are silent about and the reason it is here.  A cold source
-- with an async tail delivers once inside the subscribe frame and twice
-- after it, so the accumulator grows on the DRAIN rather than in the
-- burst: the burst carries 1 and the drain carries 3.  The seed does not
-- move to meet it, because slot data is counted by `slotsSize` and the
-- seed is exponential in that sum too — which is the half of the growth
-- law no literal source can exhibit.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insAsync : Slots Γ₁
insAsync zero = scripted (cold (1 ∷ []) (after 1 , 2 ∷ after 1 , 3 ∷ []))

stepA : Fn Γ₁ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepA = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

progA : Closed Γ₁ (obs natᵗ)
progA = scanᵉ stepA (strmᵗ emptyᵉ) (input zero)

_ : carried (burstOf progA insAsync) ≡ 1               -- LOAD-BEARING
_ = refl

_ : carried (drainOf progA insAsync) ≡ 3               -- LOAD-BEARING
_ = refl

_ : seed progA insAsync ≡ 16384                        -- LOAD-BEARING
_ = refl

_ : (carried (drainOf progA insAsync) ≤ᵇ seed progA insAsync) ≡ true
_ = refl                                               -- LOAD-BEARING


drA : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progA insAsync))) (proj₂ (proj₂ (entry progA insAsync))) Below)
drA = refl
