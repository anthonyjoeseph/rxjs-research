-- A BURST'S DELIVERIES ARE NOT ITS SYNCHRONOUS SIZE, SO THE THIRD
-- COMPONENT CANNOT PAY FOR WHAT A CASCADE GROWS.
--
-- The sibling witnesses killed every rank conjunct that reads the TERM,
-- and what they left standing was one candidate: denominate the rank in
-- the triple's own sync component, since that is the quantity the μ
-- guard re-seeds and so the one measure surviving both edges.  The
-- candidate rests on an arithmetic nobody had instantiated — that the
-- values a burst delivers are bounded by the program's synchronous
-- size — and this witness is that instantiation.  It is false, and the
-- shape of the failure is what makes it decisive rather than an
-- off-by-one: the deliveries are EXPONENTIAL in the source length while
-- `syncSizeᵉ` is linear in it, so the two cross and never come back.
--
-- THE PROGRAM IS A DOUBLING FOLD OVER A LIVE SEED, and the live seed is
-- the whole trick.  A scan whose step re-wraps its accumulator TWICE
-- emits a binary tree of accumulators; give the seed no values and every
-- leaf of that tree is empty, so the tree grows in size while delivering
-- nothing, which is why a fold over an empty seed reads small and says
-- nothing.  One value in the seed makes every leaf live, and the
-- flattener at the root subscribes each of them inside the one instant
-- the literal source fires in.  So the count doubles per delivery while
-- the term is charged `suc` for a merge and one per literal.
--
-- WHAT IT KILLS.  Any route that pays for a cascade's growth out of the
-- entry triple's sync component, which is the last of the three
-- components to be tried and the one the μ edge was going to make
-- payable.  It kills it for every additive syntactic measure and not
-- merely for this one: the counterexample scales by lengthening the
-- source, which multiplies the deliveries and adds one to the measure.
-- What a measure has to have to survive is a rate that MULTIPLIES per
-- delivery, and no additive syntactic component gives one — which is
-- why the surviving reading prices a variable off an ENVIRONMENT and
-- lets the fold clause ITERATE over its refold count, rather than
-- naming any single syntactic quantity at all.
--
-- THE COUNT IS THE HONEST ONE, and that is why it is not `burstLen`.  A
-- burst's emits carry `init`, `close`, `handoff` and `complete` beside
-- `value`, and only a `value` is a delivery — a bound refuted by an
-- `init` would be refuted off a burst that delivered nothing at all.
-- Every row below also pins the instant, since a claim about a burst is
-- a claim about ONE instant and deliveries pushed to a later tick would
-- refute nothing.
--
-- RECOVERY: git show 1f1730e^:agda/probe/Battery-Value-Count.agda holds
--   the gas-era rows this witness is ported from, and the abstract
--   `sync-count-bounded` postulate they killed.
module Refuted.Sync-Count where

open import Data.Bool using (false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; _≤ᵇ_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Prim using (InstEmit; InstEvent; init; value; close; handoff;
  complete)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ;
  varᵗ; fstᵗ; ofᵉ; scanᵉ; mergeAllᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; subscribeE; rootWitness; root; sched-init; st-init)

----------------------------------------------------------------------
-- THE MEASURE.  Generic in the payload rather than indexed, because
-- `Val Γ natᵗ` REDUCES to `ℕ` and an index-carrying signature leaves
-- both indices un-inferrable at exactly the programs below.
----------------------------------------------------------------------

countVals : ∀ {A : Set} → List (InstEvent A) → ℕ
countVals []                = 0
countVals (value _ ∷ es)    = suc (countVals es)
countVals (init _ ∷ es)     = countVals es
countVals (close _ _ ∷ es)  = countVals es
countVals (handoff _ ∷ es)  = countVals es
countVals (complete ∷ es)   = countVals es

valueCount : ∀ {A : Set} → List (InstEmit A) → ℕ
valueCount b = sum (map (λ em → countVals (InstEmit.events em)) b)

maxInstant : ∀ {A : Set} → List (InstEmit A) → ℕ
maxInstant b = foldr (λ em acc → InstEmit.instant em ⊔ acc) 0 b

----------------------------------------------------------------------
-- THE STATEMENT, at the machine's own root entry.  The seed is
-- `rootWitness`, so no hand-picked triple is doing any of the work here:
-- what is claimed is that a program's own subscribe frame cannot deliver
-- more values than the program's synchronous size.
----------------------------------------------------------------------

-- THE RUN TAKES NO PARAMETER BUT THE PROGRAM AND THE TELESCOPE, so
-- there is no allowance here to choose generously or ungenerously and
-- no truncation for a row to be on the wrong side of.  The four counts
-- below are the cascade's own.
Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins =
  proj₁ (subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e))

SyncCountBounded : Set
SyncCountBounded = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  valueCount (burstOf e ins) ≤ syncSizeᵉ e

----------------------------------------------------------------------
-- THE FAMILY.  One step function, four sources, differing in the number
-- of literals alone — so every row moves the deliveries and leaves the
-- step fixed, which is what makes the pair of rates comparable.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

prog₁ : Closed Γ₀ natᵗ
prog₁ = mergeAllᵉ nothing (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ [])))

prog₂ : Closed Γ₀ natᵗ
prog₂ = mergeAllᵉ nothing (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ [])))

prog₃ : Closed Γ₀ natᵗ
prog₃ = mergeAllᵉ nothing
  (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog₄ : Closed Γ₀ natᵗ
prog₄ = mergeAllᵉ nothing
  (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

----------------------------------------------------------------------
-- THE TWO RATES.  Each row is LOAD-BEARING and each could have failed in
-- either direction: a count that stalled would say the accumulator tree
-- stops doubling, and a count that jumped would say the merged inners do
-- not all land in the one instant.  The first three rows HOLD the bound,
-- which is the point — the crossing is not visible from small cases.
----------------------------------------------------------------------

_ : valueCount (burstOf prog₁ ins₀) ≡ 2                -- LOAD-BEARING
_ = refl

_ : valueCount (burstOf prog₂ ins₀) ≡ 6                -- LOAD-BEARING
_ = refl

_ : valueCount (burstOf prog₃ ins₀) ≡ 14               -- LOAD-BEARING
_ = refl

_ : valueCount (burstOf prog₄ ins₀) ≡ 30               -- LOAD-BEARING
_ = refl

_ : syncSizeᵉ prog₄ ≡ 20                               -- LOAD-BEARING
_ = refl

-- LOAD-BEARING, and it is what makes this a PER-INSTANT refutation
-- rather than a statement about a whole run: every emit in the burst
-- carries instant zero, so nothing here was deferred to a later tick.
_ : maxInstant (burstOf prog₄ ins₀) ≡ 0                -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CROSSING.  Pinned by `refl` outside the ⊥ so that it moves visibly
-- if either side does — thirty deliveries against a measure of twenty,
-- where three literals gave fourteen against nineteen.
----------------------------------------------------------------------

cross₄ : (valueCount (burstOf prog₄ ins₀) ≤ᵇ syncSizeᵉ prog₄) ≡ false
cross₄ = refl

sync-count-bounded-false : SyncCountBounded → ⊥
sync-count-bounded-false h = subst T cross₄ (≤⇒≤ᵇ (h prog₄ ins₀))

