-- THE FIT AT A STATE THE DRAIN ITSELF PRODUCED — the one region every
-- sibling probe of this target is silent about, and the whole of whether
-- the premise the leaf was restated onto is the right invariant.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- WHY THIS REGION.  Its sibling says the fit holds at the door, where
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
-- left side does not merely stay under the program's reading, it does
-- not MOVE: one at every step of all three programs, against readings of
-- one, two and three.  The registry churns underneath all of it — a
-- `repeat` registers a fresh inner and drops the spent one, so its
-- length returns to where it was while the mint counter climbs — and the
-- reading is flat across that churn.  Which is what the measure was
-- chosen for: a `μᵉ` unfolding substitutes rather than adding a
-- flattener, so it adds no hop, and the three `*All` nodes that do add
-- one are already in the term when the entry reads it.

-- AND THE PLAIN RECURSION IS TIGHT, WHICH IS WHERE THE COVERAGE IS.  Q1
-- reads one against one, so the fit has no slack whatever on the
-- simplest program run here: a registry carrying one hop more than the
-- term does would fail it outright, and the deeper two only widen it.
-- That is what makes flat rows evidence rather than comfort — the
-- statement is being instantiated at the point it is closest to false,
-- and a preservation claim bought only where there was room to spare
-- would say nothing about the clause a proof actually has to walk.

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

-- THE BOUNDARY.  Three arrivals deep, at the store bound the run was
-- BUILT at rather than one a row chose, over one flattening strategy,
-- and exactly one row runs a drain — six steps, on the cheapest of the
-- three programs.
-- That last bound is what the iteration loop will hold rather than what
-- the question wants: a drain is the one thing here that is not nearly
-- free, so the file buys its coverage from the fit rows and spends the
-- drain once, where the target demands it.  Nothing here reaches the
-- late-slot cascade its sibling instantiates, where one arrival
-- delivers many times, and the only nonzero slot reading swept is Q3's
-- single shared one.  Nor does a flat reading over three steps
-- establish a flat reading over all of them: what the rows buy is that
-- the fit SURVIVES a cascade, and that the quantity it bounds is not
-- the one that grows.
--
-- TARGET: drain-dry-free @0b82eb
module Probed.Fit-Preserved where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id)
open import Rx.Exp using (Ctx; Closed; natᵗ; nat̂; strmᵗ; ofᵉ;
  mergeAllᵉ; μᵉ; varᵉ; deferᵉ; input)
open import Rx.Evaluator using (Sched; EvalSt; cascade;
  sched-next; subscribeE; rootWitness; root; sched-init; st-init)
open import Rx.Slots using (Slots; shared)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Verify-Rank-Sufficient.Hop using (regsHopD; hopFits)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
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

FUEL : Fuel
FUEL = 6

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
entry e ins =
  let (_ , sched , st) =
        subscribeE (rootWitness FUEL e ins) e root 0 0 (sched-init FUEL e ins)
          (st-init e)
  in sched , st

at : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) →
  Sched Γ × EvalSt e
at k e ins = after k 1 (entry e ins)

-- THE TWO SIDES, READ OFF THE SCHEDULE RATHER THAN OFF A CHOICE.  Both
-- take their store bound from `Sched.storeBound`, which is what the fit
-- itself reads, so neither can be taken at a bound the run was not
-- built at — and the environment is `slotHop` at that same bound, which
-- `Rx.Slot-Hop` records as the one honest reading.
carriedAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
carriedAt k e ins =
  let sched = proj₁ (at k e ins)
      V     = Sched.storeBound sched
      η     = slotHop V (Sched.slots sched) in
  regsHopD V η (EvalSt.registry (proj₂ (at k e ins)))

-- WHAT THE CARRIED AMOUNT IS MEASURED AGAINST, and it is now the
-- program's own reading rather than a counter seeded off its SIZE.  The
-- two are not comparable and nothing here converts between them: this
-- is one currency, which is exactly what deleting the seed bought.
rankAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
rankAt k e ins =
  let sched = proj₁ (at k e ins)
      V     = Sched.storeBound sched in
  hopDᵉ V (slotHop V (Sched.slots sched)) e

mintAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → ℕ
mintAt k e ins = EvalSt.nextReg (proj₂ (at k e ins))

fitAt : ∀ {n} {Γ : Ctx n} {t} → ℕ → (e : Closed Γ t) (ins : Slots Γ) → Set
fitAt k e ins = hopFits (proj₁ (at k e ins)) (proj₂ (at k e ins))

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
-- inner as it registers the next — and it sits at ONE against a term
-- reading of one, which is the tight case: there is no margin here to
-- absorb a step that added a hop.
----------------------------------------------------------------------

_ : mintAt 0 progQ1 ins₀ ≡ 1          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ1 ins₀ ≡ 2          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ1 ins₀ ≡ 3          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ1 ins₀ ≡ 4          -- LOAD-BEARING
_ = refl






_ : carriedAt 0 progQ1 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ1 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ1 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ1 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ1 ins₀ ≡ 1          -- LOAD-BEARING
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
-- is stated over rather than merely along its length — and the mint
-- counter does climb, two to six, while the carried reading stays at
-- one against a term reading of two.
----------------------------------------------------------------------

_ : mintAt 0 progQ2 ins₀ ≡ 2          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ2 ins₀ ≡ 3          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ2 ins₀ ≡ 5          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ2 ins₀ ≡ 6          -- LOAD-BEARING
_ = refl

_ : carriedAt 0 progQ2 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ2 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ2 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ2 ins₀ ≡ 1       -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ2 ins₀ ≡ 2          -- LOAD-BEARING
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
-- whose registry grows fastest, four to ten across three steps, and its
-- carried reading is flat at one against a term reading of three.
----------------------------------------------------------------------

_ : mintAt 0 progQ3 insMu ≡ 4          -- LOAD-BEARING
_ = refl

_ : mintAt 1 progQ3 insMu ≡ 5          -- LOAD-BEARING
_ = refl

_ : mintAt 2 progQ3 insMu ≡ 7          -- LOAD-BEARING
_ = refl

_ : mintAt 3 progQ3 insMu ≡ 10         -- LOAD-BEARING
_ = refl

_ : carriedAt 0 progQ3 insMu ≡ 1      -- LOAD-BEARING
_ = refl

_ : carriedAt 1 progQ3 insMu ≡ 1      -- LOAD-BEARING
_ = refl

_ : carriedAt 2 progQ3 insMu ≡ 1      -- LOAD-BEARING
_ = refl

_ : carriedAt 3 progQ3 insMu ≡ 1      -- LOAD-BEARING
_ = refl

_ : rankAt 0 progQ3 insMu ≡ 3         -- LOAD-BEARING
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

fpDrain : Confirms (drain-dry-free FUEL 2
            (proj₁ (at 1 progQ1 ins₀)) (proj₂ (at 1 progQ1 ins₀)) fpQ1₁)
fpDrain = refl
