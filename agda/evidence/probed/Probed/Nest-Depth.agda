------------------------------------------------------------------
-- TARGET: depth-nest-compositional
--
-- THE CURRENCY, INSTANTIATED BEFORE ANY OF ITS INDUCTION IS WRITTEN.
-- The target says a subscribe's depth is under what the subject's
-- syntax wraps, plus what the path wraps, plus what the store holds.
-- At a root path over an empty context the second and third summands
-- are zero, so the rows below read the bound at its bare first
-- summand — which is the summand the whole restatement turns on.
--
-- THE MEASURE, read off the mechanism: a `*All` layer is worth one
-- `suc`, because that is what `depthFrame` at a `thru-outer` charges;
-- a `scanᵉ` is worth its FOLD COUNT times its step function's layers,
-- because the accumulator is re-wrapped once per delivered payload
-- while `depthFrame` charges a scan's own emissions nothing.
--
-- AND THE FOLD COUNT IS A PARAMETER, WHICH IS THE ONE THING THAT
-- SEPARATES THIS MEASURE FROM ITS REFUTED PREDECESSOR.  That one read
-- the count off the subject's own syntax, and a subject loses its
-- count under substitution — so two programs whose runs differ in
-- depth shared one cap.  Here the count is supplied by the caller and
-- comes from the instant's own fold count, so the cap moves when the
-- run does.
------------------------------------------------------------------
-- WHAT EACH SECTION BUYS.  §1 pins the bound at the two crossings the
-- predecessor's refutation measured, and pins them as EQUALITIES: the
-- rows do not ask the measure to dominate the depth, they ask it to
-- meet it, so a measure off by anything in either direction fails
-- them.  §2 asks the question the recovered harness could not: its
-- nested-scan row had the inner and outer counts EQUAL, so it could
-- not tell a single global count from two separate ones.  §3 is the
-- witness that the payload-list clause is a `⊔` and not a sum.  §4
-- pins the gate clause, which is where this measure and its
-- predecessor disagree.
--
-- SHAPES NOT COVERED, and they are why this is evidence and not the
-- theorem.  Only `mergeAllᵉ` — no concat, switch or exhaust layer,
-- whose queueing the store term charges separately.  No slot descent,
-- so the connect arc is unmeasured and `slotsNestSum` is read only at
-- an empty context.  No post-cascade state: every row starts from
-- `st-init`, so the store summand is DEGENERATE throughout and §0 says
-- so by pinning it at zero rather than leaving it implied.  And no
-- `takeᵉ`, whose clause passes its subject through unchanged.
--
-- CONJUNCTS COVERED: the subject summand, load-bearing at four values.
-- The path summand and the store summand: degenerate, pinned zero.
------------------------------------------------------------------
module Probed.Nest-Depth where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; zero; suc; _≤ᵇ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; fstᵗ; varᵗ;
  ofᵉ; scanᵉ; mapᵉ; mergeAllᵉ; deferᵉ; applyFn)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Path; root; sched-init; st-init)
-- THE MEASURE AND THE CAP ITSELF, from `src` — these rows are evidence
-- about the definitions the proof uses, never about a local copy
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; storeNestMax)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

------------------------------------------------------------------
-- the harness: the wrap/fold family the predecessor's crossings were
-- measured on, so the two generations are read on one fixture
------------------------------------------------------------------

gasN : ℕ → Gas
gasN zero    = g0
gasN (suc m) = gs (gasN m)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

Step : Set
Step = Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

accᵗ : Step
accᵗ = fstᵗ (varᵗ (here refl))

-- w layers of `*All` around the step function: the factor the fold
-- count multiplies
wraps : ℕ → Step → Step
wraps zero    t = t
wraps (suc m) t = strmᵗ (mergeAllᵉ (ofᵉ (wraps m t ∷ [])))

nats : ∀ {Θ} → ℕ → List (Tm Γ₀ [] [] Θ natᵗ)
nats zero    = []
nats (suc m) = nat̂ m ∷ nats m

seedᵗ : Tm Γ₀ [] [] [] (obs natᵗ)
seedᵗ = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

prog : ℕ → ℕ → Closed Γ₀ (obs natᵗ)
prog w k = scanᵉ (wraps w accᵗ) seedᵗ (ofᵉ (nats k))

rootProg : ℕ → ℕ → Closed Γ₀ natᵗ
rootProg w k = mergeAllᵉ (prog w k)

rootPath : Path Γ₀ natᵗ natᵗ
rootPath = root {Γ = Γ₀} {t = natᵗ}

------------------------------------------------------------------
-- §0  THE TWO SUMMANDS THAT ARE NOT BEING TESTED
--
-- DEGENERATE, and stated rather than left implied: at a root path the
-- path summand is zero by the clause, and at `sched-init`/`st-init`
-- over an empty context every store site is empty.  So each row below
-- is the target's bound with its other two summands pinned out, and
-- none of these rows could have failed.
------------------------------------------------------------------

_ : pathNestD 12 rootPath ≡ 0
_ = refl

_ : storeNestMax 12 (sched-init (rootProg 4 12) slots₀)
                            (st-init (rootProg 4 12)) ≡ 0
_ = refl

------------------------------------------------------------------
-- §1  THE MEASURE MEETS THE DEPTH AT BOTH CROSSINGS
--
-- LOAD-BEARING, in the strongest form available: equalities, not
-- bounds.  The two crossings are 12·4+1 and 29·7+1, so no single
-- constant and no measure reading the program's SIZE satisfies both.
-- The count is supplied as the source's payload count, which is what
-- the instant's fold count is at these programs.
------------------------------------------------------------------

_ : nestDᵉ 12 (rootProg 4 12) ≡ 49
_ = refl

_ : depthE (gasN 70) (rootProg 4 12) rootPath 0 0
           (sched-init (rootProg 4 12) slots₀) (st-init (rootProg 4 12))
         ≡ nestDᵉ 12 (rootProg 4 12)
_ = refl

_ : nestDᵉ 29 (rootProg 7 29) ≡ 204
_ = refl

_ : depthE (gasN 215) (rootProg 7 29) rootPath 0 0
            (sched-init (rootProg 7 29) slots₀) (st-init (rootProg 7 29))
          ≡ nestDᵉ 29 (rootProg 7 29)
_ = refl

-- LOAD-BEARING as the non-degeneracy row: at zero wraps the product
-- collapses and the measure must fall back to one, which is what says
-- the rows above read a product and not a program's size.
_ : nestDᵉ 5 (rootProg 0 5) ≡ 1
_ = refl

-- LOAD-BEARING as the row the PARAMETER buys: same wrap count, a
-- different fold count, and the cap moves with it.  A measure reading
-- the count off the subject cannot make this row and the first one
-- disagree by the right amount, which is the shape that refuted the
-- predecessor.
_ : nestDᵉ 29 (rootProg 4 29) ≡ 117
_ = refl

_ : depthE (gasN 150) (rootProg 4 29) rootPath 0 0
             (sched-init (rootProg 4 29) slots₀) (st-init (rootProg 4 29))
           ≡ nestDᵉ 29 (rootProg 4 29)
_ = refl

------------------------------------------------------------------
-- §2  A SCAN INSIDE A SCAN'S STEP FUNCTION, WITH THE TWO COUNTS
--     DIFFERENT — the question one global count is answerable at
--
-- The outer scan's step function runs an INNER scan seeded by the old
-- accumulator, so the inner scan's layers are re-applied once per
-- outer payload and the true depth is a product of THREE factors.
-- The measure has only ONE count to spend, so it spends it twice:
-- `W · (W · w + 1) + 1`.  That over-approximates when `W` dominates
-- both counts and UNDER-approximates when it does not, and the two
-- rows here are exactly that pair.
--
-- LOAD-BEARING: the third row is the bound at a count dominating both,
-- and it could fail — it does fail if the product compounds faster
-- than the measure's two factors.  The last row is the arithmetic that
-- says what the caller owes: at a count dominating only the inner one
-- the measure lands under the depth, so the target's caller must
-- supply a count above EVERY scan's fold count and not merely the
-- outermost.  That is a requirement on the fold count the instant
-- loop passes, recorded here because it is invisible from the
-- statement.
------------------------------------------------------------------

Step₂ : Set
Step₂ = Fn Γ₀ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

acc₂ : Step₂
acc₂ = fstᵗ (varᵗ (here refl))

wraps₂ : ℕ → Step₂ → Step₂
wraps₂ zero    t = t
wraps₂ (suc m) t = strmᵗ (mergeAllᵉ (ofᵉ (wraps₂ m t ∷ [])))

innerStep : ℕ → ℕ → Step
innerStep w k =
  strmᵗ (mergeAllᵉ
    (scanᵉ (wraps₂ w acc₂) (fstᵗ (varᵗ (here refl))) (ofᵉ (nats k))))

prog₂ : ℕ → ℕ → ℕ → Closed Γ₀ (obs natᵗ)
prog₂ w k j = scanᵉ (innerStep w k) seedᵗ (ofᵉ (nats j))

rootProg₂ : ℕ → ℕ → ℕ → Closed Γ₀ natᵗ
rootProg₂ w k j = mergeAllᵉ (prog₂ w k j)

_ : nestDᵉ 4 (rootProg₂ 2 3 4) ≡ 37
_ = refl

_ : depthE (gasN 130) (rootProg₂ 2 3 4) rootPath 0 0
              (sched-init (rootProg₂ 2 3 4) slots₀)
              (st-init (rootProg₂ 2 3 4))
            ≡ 29
_ = refl

_ : (depthE (gasN 130) (rootProg₂ 2 3 4) rootPath 0 0
            (sched-init (rootProg₂ 2 3 4) slots₀)
            (st-init (rootProg₂ 2 3 4))
          ≤ᵇ nestDᵉ 4 (rootProg₂ 2 3 4)) ≡ true
_ = refl

_ : nestDᵉ 3 (rootProg₂ 2 3 4) ≡ 22
_ = refl

------------------------------------------------------------------
-- §3  THE DUPLICATION WITNESS — why the payload-list clause is a `⊔`
--
-- NOT A CROSSING.  This asks whether what a step function EMITS is
-- bounded by the expression that emitted it, which is the one
-- comparison the `*All` burst arm turns on.
--
-- Under a SUMMING list clause the answer is no, and the witness is a
-- step function that hands its own input observable to an `ofᵉ` list
-- TWICE: the emitter measures 2, what it emits measures 3, and the
-- emitted inner's own depth is 2 — so the measure was over the depth
-- by exactly the duplication.  A `⊔` is the honest reading, because
-- `depthWalk` walks a payload list rather than concatenating it.
--
-- LOAD-BEARING, and permanently: the row comparing the two sides is
-- 2 ≡ 2 under the `⊔` and 3 ≡ 2 under a sum, so it is the row that
-- fails the day the summing clause comes back.
------------------------------------------------------------------

dupF : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

inner₁ : Val Γ₀ (obs natᵗ)
inner₁ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

emitter : Closed Γ₀ (obs natᵗ)
emitter = mapᵉ dupF (ofᵉ (strmᵗ inner₁ ∷ []))

emitted : Val Γ₀ (obs natᵗ)
emitted = applyFn dupF inner₁

topD : Closed Γ₀ natᵗ
topD = mergeAllᵉ emitter

_ : nestDᵉ 1 emitter ≡ 2
_ = refl

_ : nestDᵉ 1 emitted ≡ 2
_ = refl

_ : nestDᵉ 1 emitted ≡ nestDᵉ 1 emitter
_ = refl

_ : depthE (gasN 30) emitted rootPath 0 0
                 (sched-init emitted slots₀) (st-init emitted)
               ≡ 2
_ = refl

_ : nestDᵉ 1 topD ≡ 3
_ = refl

_ : depthE (gasN 30) topD rootPath 0 0
           (sched-init topD slots₀) (st-init topD)
         ≡ nestDᵉ 1 topD
_ = refl

------------------------------------------------------------------
-- §4  THE GATE TRUNCATES, and this is where the two generations of
--     the measure disagree
--
-- LOAD-BEARING: the clause reads a `deferᵉ` as zero rather than
-- passing its subject through, because the `μ` clause of `depthE`
-- recurses on the UNFOLDING and a gate-passing measure doubles per
-- unfold.  The row pins that `depthE` agrees at the gate, so the
-- truncation costs no tightness where it is taken.  It would fail if
-- `depthE` charged a deferred subject anything at all.
------------------------------------------------------------------

gated : Closed Γ₀ natᵗ
gated = mergeAllᵉ (deferᵉ (prog 4 12))

_ : nestDᵉ 12 gated ≡ 1
_ = refl

_ : depthE (gasN 70) gated rootPath 0 0
             (sched-init gated slots₀) (st-init gated)
           ≡ nestDᵉ 12 gated
_ = refl
