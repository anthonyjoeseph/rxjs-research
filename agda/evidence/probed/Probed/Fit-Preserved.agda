-- THE FIT AT A STATE THE DRAIN ITSELF PRODUCED — the one region every
-- sibling probe of this target is silent about, and the whole of whether
-- the premise the leaf was restated onto is the right invariant.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS REGION.  Fifteen rows say the fit holds at the door, where
-- the chain really is the one the root subscribe built out of `e`.  None
-- of them says anything about the state the drain hands its own
-- recursive call, and that is the direction the statement is USED in: a
-- proof of the leaf inducts on fuel, so every step but the first applies
-- it at a state a cascade produced.  An invariant that holds at entry
-- and is destroyed by one arrival is not an invariant, and grinding the
-- leaf before asking would spend the tier establishing that.

-- HOW A STATE AFTER k ARRIVALS IS REACHED.  `drain` returns the emit
-- stream and throws the state away, so the rows cannot read one off it.
-- `stepOnce` is the drain's own recursive step with the stream dropped —
-- the same `sched-next` and the same `cascade`, in the same order and at
-- the same instant counter — so the pair it returns is the pair `drain`
-- would have recursed on, not a state written by hand.  That distinction
-- is the reason this file exists: a hand-built state is refutation
-- material at best, and the fit is being asked about REACHED ones.

-- WHAT THE ROWS FOUND, and it is stronger than preservation.  The fit's
-- left side does not merely stay under the rank, it does not MOVE: two
-- at every step of the plain recursion, three at every step of both
-- nested ones, against rank exponents of eleven, nineteen and
-- twenty-eight.  The registry churns underneath all of it — a `repeat`
-- registers a fresh inner and drops the spent one, so its length returns
-- to where it was while the mint counter climbs — and the reading is
-- flat across that churn.  Which is what the measure was chosen for: a
-- `μᵉ` unfolding substitutes rather than adding a flattener, so it adds
-- no hop, and the three `*All` nodes that do add one are already in the
-- term when the entry reads it.

-- WHAT MAKES A FIT ROW LOAD-BEARING.  It spends `Below` — the decision
-- procedure on the comparison — so its implicit is inhabited exactly
-- when the fit is TRUE at that point: a fit destroyed by the k-th
-- arrival leaves the row unsolvable rather than letting it through,
-- which is what makes this a refutation attempt and not a confirmation
-- exercise.  A row is also a single equation rather than a tuple of
-- them, and that is a COST finding and not a style one: a four-component
-- tuple of the same readings costs upward of fifty seconds where the
-- four rows cost about one, so a probe of this shape written the tidy
-- way cannot be iterated on at all.

-- AND THE MINT ROWS ARE WHY THE FLAT READINGS MEAN ANYTHING.  A
-- `stepOnce` that had silently become a fixed point would report the
-- same figure at every k, which is exactly what the carried readings do
-- report — so the constancy has to be separated from a no-op, and the
-- registration counter is what separates them.  It is minted once per
-- registration and never reused, so it is strictly increasing across a
-- cascade that did anything; it climbs on every program at every step.
-- An emit count could not have done this job, since the drain is
-- fuel-bounded over programs that never quiesce and returns much the
-- same stream from any state.

-- THE THREE PROGRAMS are the widest spread the sibling file reaches:
-- plain recursion, μ nested directly in μ, and a share holding a
-- recursion referenced from inside a second one — the shape whose
-- nesting the rank guard cannot read off the term it compares.

-- THE BOUNDARY.  Three arrivals deep, at the naive reading `V = 0` and
-- `η` constantly zero, over one flattening strategy, and exactly one
-- row runs a drain — six steps, on the cheapest of the three programs.
-- That last bound is what the iteration loop will hold rather than what
-- the question wants: a drain is the one thing here that is not nearly
-- free, so the file buys its coverage from the fit rows and spends the
-- drain once, where the target demands it.  Nothing here reaches the
-- late-slot cascade its sibling instantiates, where one arrival
-- delivers many times, and nothing sweeps a nonzero slot reading.  Nor
-- does a flat reading over three steps establish a flat
-- reading over all of them: what the rows buy is that the fit SURVIVES a
-- cascade, and that the quantity it bounds is not the one that grows.
--
-- TARGET: drain-dry-free @140a87
module Probed.Fit-Preserved where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id)
open import Rx.Exp using (Ctx; Closed; sizeᵉ; natᵗ; nat̂; strmᵗ; ofᵉ;
  mergeAllᵉ; μᵉ; varᵉ; deferᵉ; input)
open import Rx.Evaluator using (Sched; EvalSt; cascade;
  sched-next; subscribeE; rootWitness; root; sched-init; st-init; stNest)
open import Rx.Slots using (Slots; slotsSize; shared)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Verify-Rank-Sufficient.Hop using (liveHopD; regsHopD; hopFits)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The non-vacuity measure, taken verbatim from the sibling probes so a
-- row here is comparable with a row there: how many EVENTS `hasDry` had
-- to look at.
----------------------------------------------------------------------

stepOnce : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
stepOnce nextId (sched , st) with sched-next sched
... | inj₁ _            = sched , st
... | inj₂ (a , sched′) =
  let (_ , sched″ , st′) = cascade a nextId sched′ st in sched″ , st′

after : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  ℕ → Id → Sched Γ × EvalSt e → Sched Γ × EvalSt e
after 0       _      p = p
after (suc k) nextId p = after k (suc nextId) (stepOnce nextId p)

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
entry e ins =
  let (_ , sched , st) =
        subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)
  in sched , st

at : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
at k e ins = after k 1 (entry e ins)

FUEL : Fuel
FUEL = 6

carriedAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
carriedAt k e ins =
  liveHopD 0 (λ _ → 0) (Sched.live (proj₁ (at k e ins)))
    + regsHopD 0 (λ _ → 0) (EvalSt.registry (proj₂ (at k e ins)))

rankAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
rankAt k e ins =
  sizeᵉ e + slotsSize (Sched.slots (proj₁ (at k e ins)))
    + stNest (proj₂ (at k e ins))

mintAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
mintAt k e ins = EvalSt.nextReg (proj₂ (at k e ins))

fitAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → Set
fitAt k e ins = hopFits 0 (λ _ → 0) (proj₁ (at k e ins)) (proj₂ (at k e ins))

----------------------------------------------------------------------
-- The programs.  Q1 is plain recursion over the empty context, Q2 is μ
-- directly inside μ, and Q3 puts the recursion in a SHARE referenced
-- from inside a second one — where the emitted inner's nesting is fixed
-- outside the emitter's own syntax.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

insMu : Slots Γ₁
insMu zero = shared (μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 5 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ []))))

progQ1 : Closed Γ₀ natᵗ
progQ1 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

progQ2 : Closed Γ₀ natᵗ
progQ2 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (μᵉ (mergeAllᵉ nothing
           (ofᵉ ( strmᵗ (ofᵉ (nat̂ 2 ∷ []))
                ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
                ∷ []))))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

progQ3 : Closed Γ₁ natᵗ
progQ3 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (μᵉ (mergeAllᵉ nothing
           (ofᵉ ( strmᵗ (input zero)
                ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
                ∷ []))))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

----------------------------------------------------------------------
-- PLAIN RECURSION.  The mint row is the one to read first: four
-- distinct values, so each of the three steps ran a cascade that
-- registered.  The carried reading is flat across all of them while the
-- registry returns to length one each time — a `repeat` drops the spent
-- inner as it registers the next — and it sits at two against a rank
-- exponent of eleven, so the margin is three orders of magnitude wide
-- and not moving.
----------------------------------------------------------------------

_ : mintAt 0 progQ1 ins₀ ≡ 1          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ1 ins₀ ≡ 2          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ1 ins₀ ≡ 3          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ1 ins₀ ≡ 4          -- LOAD-BEARING
_ = refl

_ : carriedAt 0 progQ1 ins₀ ≡ 2       -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ1 ins₀ ≡ 2       -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ1 ins₀ ≡ 2       -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ1 ins₀ ≡ 2       -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ1 ins₀ ≡ 11             -- LOAD-BEARING
_ = refl

fpQ1₁ : fitAt 1 progQ1 ins₀
fpQ1₁ = Below

fpQ1₂ : fitAt 2 progQ1 ins₀
fpQ1₂ = Below

fpQ1₃ : fitAt 3 progQ1 ins₀
fpQ1₃ = Below

----------------------------------------------------------------------
-- μ INSIDE μ.  The inner recursion is an observable EMITTED by the outer
-- one, so a step here grows the registry along the axis the rank guard
-- is stated over rather than merely along its length — and the registry
-- does grow, two to three, while the carried reading stays at three.
----------------------------------------------------------------------

_ : mintAt 0 progQ2 ins₀ ≡ 2          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ2 ins₀ ≡ 3          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ2 ins₀ ≡ 5          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ2 ins₀ ≡ 6          -- LOAD-BEARING
_ = refl

_ : carriedAt 0 progQ2 ins₀ ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ2 ins₀ ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ2 ins₀ ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ2 ins₀ ≡ 3       -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ2 ins₀ ≡ 19             -- LOAD-BEARING
_ = refl

fpQ2₁ : fitAt 1 progQ2 ins₀
fpQ2₁ = Below

fpQ2₂ : fitAt 2 progQ2 ins₀
fpQ2₂ = Below

fpQ2₃ : fitAt 3 progQ2 ins₀
fpQ2₃ = Below

----------------------------------------------------------------------
-- THE SHARE HOLDING A RECURSION, reached from inside a second one.  The
-- sharpest shape the sibling file reaches, and the one where a fit read
-- off the term alone would be expected to fail — a slot reference is one
-- symbol standing for a definition of any size.  It is also the one
-- whose registry grows fastest, four to seven across three steps, and
-- its carried reading is flat too.
----------------------------------------------------------------------

_ : mintAt 0 progQ3 insMu ≡ 4          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ3 insMu ≡ 5          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ3 insMu ≡ 7          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ3 insMu ≡ 10          -- LOAD-BEARING
_ = refl

_ : carriedAt 0 progQ3 insMu ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ3 insMu ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ3 insMu ≡ 3       -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ3 insMu ≡ 3       -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ3 insMu ≡ 28             -- LOAD-BEARING
_ = refl

fpQ3₁ : fitAt 1 progQ3 insMu
fpQ3₁ = Below

fpQ3₂ : fitAt 2 progQ3 insMu
fpQ3₂ = Below

fpQ3₃ : fitAt 3 progQ3 insMu
fpQ3₃ = Below

----------------------------------------------------------------------
-- THE ROW THE TARGET ITSELF GENERATES.  Everything above reads the
-- fit; this one spends it, at the state one arrival produced, and its
-- type is written by `drain-dry-free` rather than by this file — so a
-- restatement of the leaf moves it and a weaker predicate cannot be
-- smuggled in beside it.  `refl` forces the whole six-step drain, which
-- is why there is one of these and not nine.
----------------------------------------------------------------------

fpDrain : Confirms (drain-dry-free FUEL 2 0 (λ _ → 0)
            (proj₁ (at 1 progQ1 ins₀)) (proj₂ (at 1 progQ1 ins₀)) fpQ1₁)
fpDrain = refl
