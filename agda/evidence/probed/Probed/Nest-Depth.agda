------------------------------------------------------------------
-- TARGET: emit-map
--
-- RETARGETED WHEN THE FACE SPLIT.  `depth-all-bound` is gone: its outer
-- arm is proven inside the assembly's own induction and its burst arm is
-- the leaf named above.  A `⊔` sits under a bound exactly when both arms
-- do, so these rows were always evidence about both — what is left to be
-- evidence FOR is the half still open.
--
-- THE CANDIDATE MEASURE FOR THE RESTATEMENT, instantiated before any of
-- it is written into `src`.  The PREDECESSOR of this face — the form with
-- no nesting term, which is what `Refuted.Depth-Nest`'s witness type
-- states — is refuted because its cap is linear in the syntax while
-- `depthE` grows in `wraps × ticks`, and the width family cannot supply
-- the product either — `width-route-absurd` refutes all four measures at
-- once, because a wrap layer multiplies width by one.  So the
-- restatement needs a NEW measure, and this file is the cheap test of
-- one before a mutual block is touched on the strength of a guess.
--
-- THE MEASURE, read off the mechanism rather than fitted: a `*All` layer
-- is worth one `suc`, because that is what `depthFrame` at `thru-outer`
-- charges; a `scanᵉ` is worth its SOURCE'S PAYLOAD COUNT times its step
-- function's layers, because the accumulator is re-wrapped once per
-- delivered payload and `depthFrame … (scan-f …)` charges the emissions
-- nothing (`burst-scf-zero`).  That is the `length vals * suc (sizeᵗ fn)`
-- shape `scanFrame-caps` already pays, arriving at the depth face.
--
-- LOAD-BEARING, and in the strongest form available: the rows do not ask
-- the measure to DOMINATE the depth, they ask it to EQUAL it, at both
-- crossings the refutation walks — 49 at four wraps over twelve ticks
-- and 204 at seven over twenty-nine.  A measure off by anything at all,
-- in either direction, fails these rows, and the two rows are 4·12+1 and
-- 7·29+1 so no single constant can satisfy both.  `flatRow` is the
-- non-degeneracy row: at zero wraps the product collapses and the
-- measure must fall back to 1, which is what says the other two rows are
-- reading the product and not the program's size.
--
-- SHAPES NOT COVERED, and they are the reason this stays evidence: only
-- `mergeAllᵉ` (no concat/switch/exhaust layer, whose queueing
-- `nodesNestMax` charges separately); only one scan, so a scan nested
-- inside another scan's step function is untested and is exactly where a
-- product of THREE factors would show up; no `input`/slot descent, so
-- the connect arc is unmeasured here and `slotsNestBelow` is the term
-- that would carry it; and no post-cascade state.
--
-- §3 IS A DIFFERENT KIND OF ROW and is described where it sits: not a
-- crossing of the measure against the depth, but the witness that killed
-- the SUM form of the list clause, kept as the row that fails the day
-- anyone puts the sum back.
------------------------------------------------------------------
module Probed.Nest-Depth where

open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; zero; suc)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec  using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; fstᵗ; varᵗ;
  ofᵉ; scanᵉ; mapᵉ; mergeAllᵉ; applyFn)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Path; root; sched-init; st-init)
-- THE MEASURE ITSELF, from `src` — these rows are evidence about the
-- definition the proof uses, not about a local copy of it
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (depthCap)

------------------------------------------------------------------
-- the harness: Refuted.Depth-Nest's family, which is where the
-- crossings were measured
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
-- §1  THE MEASURE PREDICTS THE DEPTH EXACTLY, at both crossings
------------------------------------------------------------------

-- LOAD-BEARING: 4·12+1, and the depth side is the 49 that refutes the
-- predecessor of the face this file targets.
lowRow : depthE (gasN 70) (rootProg 4 12) rootPath 0 0
           (sched-init (rootProg 4 12) slots₀) (st-init (rootProg 4 12))
         ≡ nestDᵉ slots₀ (rootProg 4 12)
lowRow = refl

-- LOAD-BEARING: 7·29+1, and the depth side is the 204 that refutes
-- `depth-capped`'s three-cSize interface at 201.  No constant satisfies
-- this row and the one above at once.
highRow : depthE (gasN 215) (rootProg 7 29) rootPath 0 0
            (sched-init (rootProg 7 29) slots₀) (st-init (rootProg 7 29))
          ≡ nestDᵉ slots₀ (rootProg 7 29)
highRow = refl

-- LOAD-BEARING, as the non-degeneracy row: zero wraps collapses the
-- product, so a measure reading the program's SIZE rather than its
-- layer product cannot also pass this.
flatRow : nestDᵉ slots₀ (rootProg 0 5) ≡ 1
flatRow = refl

-- and the two products in closed form, so the rows above are legible as
-- arithmetic and not only as agreement
lowVal : nestDᵉ slots₀ (rootProg 4 12) ≡ 49
lowVal = refl

highVal : nestDᵉ slots₀ (rootProg 7 29) ≡ 204
highVal = refl

-- AND THE SAME TWO ROWS READ OFF THE STATEMENT THAT IS OPEN.  The cap
-- the target's face is stated over is read off NESTING throughout and
-- reads no state at all, so at a root path over a context with no slots
-- it is `nestDᵉ` and nothing else — which makes the two rows above the
-- cap's own crossings rather than a measure's, and makes them
-- EQUALITIES of the cap with the depth.  These rows are what say the
-- cap has no slack at all on this family: it is not that the bound
-- holds, it is that one more unit of depth anywhere would break it.
lowCap : depthE (gasN 70) (rootProg 4 12) rootPath 0 0
           (sched-init (rootProg 4 12) slots₀) (st-init (rootProg 4 12))
         ≡ depthCap (rootProg 4 12) rootPath
             (sched-init (rootProg 4 12) slots₀)
lowCap = refl

highCap : depthE (gasN 215) (rootProg 7 29) rootPath 0 0
            (sched-init (rootProg 7 29) slots₀) (st-init (rootProg 7 29))
          ≡ depthCap (rootProg 7 29) rootPath
              (sched-init (rootProg 7 29) slots₀)
highCap = refl

------------------------------------------------------------------
-- §2  A SCAN INSIDE A SCAN'S STEP FUNCTION — the third factor
--
-- §1's shapes leave one question that decides the whole currency: is the
-- product degree TWO, or does it compound?  A degree-2 product is
-- polynomial in the syntax and a `cSize · cSize` cap would hold; an
-- unbounded degree is exponential, and no fixed-degree product can.
--
-- The outer scan's step function here RUNS AN INNER SCAN seeded by the
-- old accumulator, so the inner scan's `w · k` layers are themselves
-- re-applied once per outer payload.  The measure predicts `j · k · w`
-- and the rows ask `depthE` whether it agrees.
------------------------------------------------------------------

Step₂ : Set
Step₂ = Fn Γ₀ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

acc₂ : Step₂
acc₂ = fstᵗ (varᵗ (here refl))

wraps₂ : ℕ → Step₂ → Step₂
wraps₂ zero    t = t
wraps₂ (suc m) t = strmᵗ (mergeAllᵉ (ofᵉ (wraps₂ m t ∷ [])))

-- the outer step: an inner scan whose SEED is the incoming accumulator
innerStep : ℕ → ℕ → Step
innerStep w k =
  strmᵗ (mergeAllᵉ
    (scanᵉ (wraps₂ w acc₂) (fstᵗ (varᵗ (here refl))) (ofᵉ (nats k))))

prog₂ : ℕ → ℕ → ℕ → Closed Γ₀ (obs natᵗ)
prog₂ w k j = scanᵉ (innerStep w k) seedᵗ (ofᵉ (nats j))

rootProg₂ : ℕ → ℕ → ℕ → Closed Γ₀ natᵗ
rootProg₂ w k j = mergeAllᵉ (prog₂ w k j)

-- LOAD-BEARING, and it is the row the currency turns on.  The inner
-- scan yields an `obs`, so flattening it back costs one layer and the
-- inner step is worth `suc (k · w)`; the outer scan re-applies that once
-- per payload, so the prediction is `j · (k · w + 1) + 1 = 22`.  A
-- degree-2 measure cannot produce it.
deepVal : nestDᵉ slots₀ (rootProg₂ 2 3 3) ≡ 22
deepVal = refl

deepRow : depthE (gasN 90) (rootProg₂ 2 3 3) rootPath 0 0
            (sched-init (rootProg₂ 2 3 3) slots₀) (st-init (rootProg₂ 2 3 3))
          ≡ nestDᵉ slots₀ (rootProg₂ 2 3 3)
deepRow = refl

------------------------------------------------------------------
-- §3  THE DUPLICATION WITNESS — why the list clause is a `⊔`
--
-- THIS SECTION IS NOT A CROSSING.  §1 and §2 ask whether the measure
-- equals the depth; this one asks the ONE question the target's
-- statement turns on, which is a comparison between two expressions
-- rather than between a measure and a run: is what a step function
-- EMITS bounded by the expression that emitted it?
--
-- It was a refutation first.  Under a SUMMING `nestDᵗˢ` the answer is
-- NO, and the witness is nothing exotic: a step function that hands its
-- own input observable to an `ofᵉ` list TWICE.  The emitter measured 2
-- and what it emitted measured 3, while the emitted inner's own DEPTH
-- was 2 — so the measure was over the depth by exactly the duplication,
-- and the leaf the `*All` burst arm needs was false as stated.
--
-- The repair was to the MEASURE, not to the statement: `nestDᵗˢ` takes a
-- `⊔` where `depthWalk` takes a `⊔`, which is the honest reading of the
-- mechanism (a list of payloads is walked, not concatenated) and makes
-- the cap strictly smaller everywhere.  Every row in §1 and §2 is
-- unmoved by it, because their `ofᵉ` lists are singletons or carry
-- payloads of nesting 0, where a max and a sum agree.
--
-- LOAD-BEARING, and permanently so: `emittedCap` is an equality between
-- the two sides the leaf compares, at the program that refuted the sum.
-- It is 2 ≡ 2 under the `⊔` and 3 ≡ 2 under a sum, so it is the row that
-- fails the day the summing clause comes back — which is the only thing
-- standing between that clause and a leaf that reads as provable.
------------------------------------------------------------------

-- a step function that hands its input to an `ofᵉ` list TWICE
dupF : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
dupF = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

-- the payload it is applied to, itself one `*All` layer deep
inner₁ : Val Γ₀ (obs natᵗ)
inner₁ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

-- the emitter: `dupF` mapped over a source carrying that payload
emitter : Closed Γ₀ (obs natᵗ)
emitter = mapᵉ dupF (ofᵉ (strmᵗ inner₁ ∷ []))

-- and what it emits, which is what the leaf must bound
emitted : Val Γ₀ (obs natᵗ)
emitted = applyFn dupF inner₁

topD : Closed Γ₀ natᵗ
topD = mergeAllᵉ emitter

-- the two sides in closed form, so the row below is legible as
-- arithmetic: the duplication is invisible to a max and worth one full
-- layer to a sum
emitterND : nestDᵉ slots₀ emitter ≡ 2
emitterND = refl

emittedND : nestDᵉ slots₀ emitted ≡ 2
emittedND = refl

-- LOAD-BEARING, and this is the row: 2 ≡ 2 under the `⊔`, 3 ≡ 2 under a
-- sum.  Nothing else in this tree fails when the list clause regresses.
emittedCap : nestDᵉ slots₀ emitted ≡ nestDᵉ slots₀ emitter
emittedCap = refl

-- AND THE EMITTED INNER'S OWN DEPTH, which is what says the finding was
-- the measure's and not the mechanism's: the run agrees with the `⊔`.
emittedDepth : depthE (gasN 30) emitted rootPath 0 0
                 (sched-init emitted slots₀) (st-init emitted)
               ≡ 2
emittedDepth = refl

-- LOAD-BEARING as the containment row: the top of the same program is
-- one layer up from the emitter, and the cap meets its depth exactly
-- there — so the refutation above was a defect in the route through the
-- payload, never slack in the cap.
topND : nestDᵉ slots₀ topD ≡ 3
topND = refl

topRow : depthE (gasN 30) topD rootPath 0 0
           (sched-init topD slots₀) (st-init topD)
         ≡ nestDᵉ slots₀ topD
topRow = refl
