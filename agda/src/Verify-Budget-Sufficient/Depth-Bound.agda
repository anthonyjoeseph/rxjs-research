------------------------------------------------------------------
-- THE DEPTH OBLIGATION, STATED (2026-08-03).
--
-- `sub-charge` (Caps-Bridge.agda) bounds a subscribe's growth index by
-- `opIterD … (depthE g b κ bid now sched st) …` — a receipt in terms of
-- the depth mirror at the call's own arguments.  For the receipt to be
-- SPENDABLE the depth must be bounded by something entry-computable,
-- and the naive candidates are dead: `depthE ≤ capsBase` is FALSE
-- (machine-refuted 2026-08-09 — scan accumulators deepen per fold
-- while capsBase gains +1 per arrival),
-- and any UNCONDITIONAL `depthE ≤ capsH` dies the same way against an
-- adversarial stored state.  The honest statement conditions on the
-- state being bounded — which is exactly the hypothesis every consumer
-- already holds, as `capsOK?`.
--
-- THE SHAPE (validated with C = 0 by
-- Depth-Compositional-Probe (DELETED; git history), whose header traces every
-- clause of the depth mirror to one of these three channels):
--
--     depthE g b κ bid now sched st
--       ≤ sizeᵉ b + pathLen κ + storeNestMax sched st
--
-- No tower arithmetic anywhere: `capsH`/`blowH` enter only through the
-- consumer's own monotone plumbing, never through this bound.  The
-- probe's residual is honest and recorded there: its evaluator-driving
-- mechanism goes geometric past k ≈ 4 / N ≈ 10, so the k = 7/9/12 zone
-- is covered by the STRUCTURE of the eventual proof (each mirror
-- clause bounded by the matching size sum), not by rows.
--
-- Outside-in: `depth-capped` below is the ASSEMBLY over two pieces
-- whose shapes were pinned by this consumer before either was ground.
--
--   · `depth-compositional` — LIVES IN Depth-Compositional.agda (with
--     the `storeNestMax` measure it is stated over): an assembly over
--     the census's three BUCKET-(d) postulates, structurally recursive
--     on the expression.
--   · `storeNest-capped` — PROVEN below: an inversion of `capsOK?`'s
--     conjuncts — `stBounded?`'s boundedNode clauses ARE
--     `nodeNestMax ≤ᵇ cSize` read as a test, and the slot half is
--     `slotsNestMax ≤ slotsSize` (a shared slot's def is one summand
--     of its size) chained with the consumer-supplied
--     `slotsSize ≤ cSize`.
------------------------------------------------------------------

module Verify-Budget-Sufficient.Depth-Bound where

open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≤ᵇ_; _⊔_; z≤n)
open import Data.Nat.Properties using (≤-trans; +-mono-≤; n≤1+n; ≤-refl; ⊔-lub; ≤ᵇ⇒≤)
open import Data.Bool    using (Bool; true)
open import Data.List    using (List; []; _∷_; foldr)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Gas; Tick; Id)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; scan-st;
                                take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                Path)
open import Rx.Slots using (scripted; shared; Slot; Slots; slotSize; slotsSize)

-- the wet family (pathLen, from .Measures) and the caps face (Caps,
-- capsOK?), each imported below from the module that defines it
open import Verify-Budget-Sufficient.Measures using
  (boundedNode; pathLen; stB-nodes; sum-tab-mono; ∧-true; szB)
open import Verify-Budget-Sufficient.Caps using
  (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-parts)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

-- `storeNestMax` and `depth-compositional` LANDED 2026-08-06: the
-- measure and the compositional bound moved to their own module
-- (Depth-Compositional — an assembly over the census's three named
-- BUCKET-(d) postulates plus the burst-zero/installNode kit), because
-- that module defines what this one consumes and the reverse import
-- would be a cycle.  The 2026-08-05 census findings travelled with it.
open import Verify-Budget-Sufficient.Depth-Compositional
  using (nodeNestMax; nodesNestMax; slotNest; slotsNestSum; storeNestMax;
         depth-compositional)
open import Decide using (T-to)

------------------------------------------------------------------
-- `storeNest-capped` — PROVEN.  The `⊔` splits, and each half is an
-- inversion of a `capsOK?` conjunct: the node half through
-- `stBounded?`'s own `boundedNode` test (whose two live clauses ARE
-- `nodeNestMax`'s), the slot half through `slotNest ≤ slotSize`
-- pointwise plus max-of-tabulate ≤ sum-of-tabulate.
--
-- Both helpers below are generic, and `foldr-⊔-bounded` would serve
-- other callers from `.Measures`.  They stay HERE deliberately: moving
-- them down the chain would dirty Measures and force a recheck of
-- Caps-Face + Subscribe-Face + Wet (~45 min) to buy nothing today.
-- Move one down when a second consumer actually appears.
--
-- Note `tabulate-⊔≤-sum` is stated for any pointwise-dominated pair
-- rather than "f is a summand of g" — `scripted`'s `slotNest = 0` is
-- not a summand of anything, it is merely `≤ slotSize`.
------------------------------------------------------------------

foldr-⊔-bounded : ∀ {A : Set} (B : ℕ) (f : A → ℕ) (p : A → Bool) →
  (∀ x → p x ≡ true → f x ≤ B) →
  (xs : List A) → all p xs ≡ true → foldr (λ x acc → f x ⊔ acc) 0 xs ≤ B
foldr-⊔-bounded B f p dom []       h = z≤n
foldr-⊔-bounded B f p dom (x ∷ xs) h
  with ∧-true (p x) (all p xs) h
... | px , pxs = ⊔-lub (dom x px) (foldr-⊔-bounded B f p dom xs pxs)

node-nest-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → nodeNestMax ns ≤ B
node-nest-bounded B (scan-st _)      h = z≤n
node-nest-bounded B (concat-st q _ _) h =
  foldr-⊔-bounded B sizeᵉ (λ o → sizeᵉ o ≤ᵇ B)
    (λ o ho → ≤ᵇ⇒≤ (sizeᵉ o) B (T-to ho)) q h
node-nest-bounded B (take-st _)      h = z≤n
node-nest-bounded B (merge-st _ _)   h = z≤n
node-nest-bounded B (switch-st _ _)  h = z≤n
node-nest-bounded B (exhaust-st _ _) h = z≤n

nodesNestMax-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  nodesNestMax nodes ≤ B
nodesNestMax-bounded B nodes h =
  foldr-⊔-bounded B (λ kv → nodeNestMax (proj₂ kv))
    (λ kv → boundedNode B (proj₂ kv))
    (λ kv → node-nest-bounded B (proj₂ kv)) nodes h

slotNest-≤-slotSize : ∀ {n} {Γ : Ctx n} {k t} (s : Slot Γ k t) →
  slotNest s ≤ slotSize s
slotNest-≤-slotSize (scripted _) = z≤n
slotNest-≤-slotSize (shared _)   = ≤-refl

-- SUM MONOTONICITY, and it was ALREADY PROVEN one module down:
-- `sum-tab-mono` in `.Measures`.  `slotsNestSum` became a sum when the
-- max was refuted (Refuted.Depth-Chain), and this is the whole cost of
-- that on the cap side — the local max-of-tabulate ≤ sum-of-tabulate
-- lemma with its two `⊔-lub` arms is gone, replaced by a lemma the
-- chain below already had.
slots-nest-≤-size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) →
  slotsNestSum sl ≤ slotsSize sl
slots-nest-≤-size {n} sl =
  sum-tab-mono {n} (λ i → slotNest (sl i)) (λ i → slotSize (sl i))
    (λ i → slotNest-≤-slotSize (sl i))

storeNest-capped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  slotsSize (Sched.slots sched) ≤ Caps.cSize c →
  storeNestMax sched st ≤ Caps.cSize c
storeNest-capped c sched st cap slB =
  ⊔-lub (≤-trans (slots-nest-≤-size (Sched.slots sched)) slB)
        (nodesNestMax-bounded (Caps.cSize c) (EvalSt.nodes st)
          (stB-nodes (Caps.cSize c) sched st (proj₁ (capsOK?-parts c sched st cap))))

------------------------------------------------------------------
-- THE ASSEMBLY — the entry-computable cap, under exactly the
-- hypotheses `sub-charge` already carries (at c := frameStep j c
-- there; `Caps.cSize` is all this reads, so any level's caps fit).
-- This is what turns `sub-charge`'s `opIterD … depthE …` receipt into
-- a number the instant's fuel can dominate, tower-free.
------------------------------------------------------------------

-- REFUTED 2026-08-21 (Refuted.Depth-Nest, `depth-capped-absurd`): FALSE,
-- and this one names the repair.  The `3 · cSize` is a CONSTANT multiple
-- while `depth-compositional`'s gap under it is a PRODUCT, so taking
-- `cSize` at exactly `sizeᵉ b` — all the hypotheses demand — crosses at
-- seven wraps over twenty-nine ticks: 204 against 201.
--
-- THE DEFECT IS THE LEVEL, NOT THE ARITHMETIC.  `capsOK?` is checked at
-- the ENTRY state and the conclusion is about a depth reached much
-- later; the deeply nested value is a scan's stored accumulator, which
-- `stBounded?` → `boundedNode` bounds by `cSize` — so the hypothesis
-- holds where it is checked (empty nodes) and fails where it is spent.
-- Everywhere else this face reports GROWTH, `frameStep j ↦ frameStep
-- (j + j′)`, and `sub-charge` already produces such a `j′` over exactly
-- this burst.  This is the one statement that reads a level it does not
-- report.
--
-- The CALL SITE is not where it fails: `Caps-Bridge` applies it at
-- `baseCaps e ins`, whose `cSize` reads `entryCeil` rather than
-- bracketing it, on the stated grounds that the static width measures
-- tower in the syntax.  The statement is false because it admits caps
-- its caller never passes.
--
-- WHAT THE CONSUMER ACTUALLY WANTS IS SLACK, AND THAT IS THE GOOD NEWS.
-- The only consumer is `depthE≤capsH-root`, whose conclusion is
-- `≤ capsH e ins 0` — and `capsH m 0` is `blowH m`, which carries
-- `2 * poolCount (towerℕ m) m`.  So the target is astronomically true
-- and every crossing above lives in the ROUTE, not the goal.  The header
-- below this one advertises that route as "tower-free"; tower-free is
-- precisely what a product cannot be.
--
-- DEAD ROUTE 2026-08-21: BOUND THE DEPTH BY THE GAS.  It is the obvious
-- repair and it is true — every `suc` in the depth family (`depthFrame`
-- at a thru-outer, `depthFinC` at a drain) is followed by a
-- `depthInner`/`depthConn` peel before another can occur, so
-- `depthE g … ≤ <gas length>` needs only the lexicographic induction
-- this face already performs.  It CANNOT CHAIN: `budgetAt-gs-pad`
-- (Burst-Walk) gives `budgetAt e sl id ≡ gs (gasPad k (gasTower
-- (3 + capsHgo (capsBase e sl) (suc id))))`, a tower of height one
-- capsH-step ABOVE `capsH e sl id`.  So the gas is strictly the wrong
-- side of the goal, and a true lemma buys nothing.  Do not re-derive it.
--
-- THE WIDTH ROUTE IS DEAD, AND IT IS THE ONE THAT LOOKS ALIVE.
-- `Rx.Frame-Width`'s `innWⱽ` and `pmIⱽ` each carry an exponential at a
-- `scanᵉ` — `(pmIᵗⱽ … f ⊔ 1) ^ (outWⱽ … e)`, a per-fold multiplier
-- raised to the source's payload count — which reads, from the clause
-- alone, exactly like the mechanism refuted above, and `Wᴱ` bundles all
-- four measures under one dominating `M` that `Caps-Face/Part2` supplies
-- as `iterFold S (sizeᵉ e) M`.  Every step of that reading is true and
-- the route still does not exist: the exponential's BASE is
-- `pmIᵗⱽ … 0 f ⊔ 1`, and a step function that re-wraps its accumulator
-- has `pmIᵗⱽ … 0 f ≡ 1`, because one wrap layer's `outWⱽ` is
-- `1 * innWⱽ (ofᵉ (t ∷ []))` — it multiplies by one and adds nothing.
-- `1 ^ k` is 1, and the family is blind to the wrap count entirely.
--
-- REFUTED 2026-08-21 (Refuted.Depth-Nest, `width-route-absurd`), and
-- against the MAX of all four at once, so no reshuffling of them
-- survives: 24 against a depth of 49, with the 24 being `2 · k` and
-- carrying no `w`.  This is what the measures are for — width is how
-- many payloads travel abreast, and a wrap adds one layer to a single
-- payload, which is the other axis.  Do not re-derive it from the scan
-- clause; the clause is not the base.
--
-- AND THE COUNT IS NAMED, not left to be chosen.  `frameStep j c`'s
-- `cWid` field IS `iterFold (cSize c) j (cWid c)`, so "which fold" is
-- "which level", and the scan frame's own receipt fixes it:
-- `scanFrame-caps` charges `length vals * suc (sizeᵗ fn)` — burst
-- cardinality times step size, this witness's `k · w` with both factors
-- named — and the size and width faces each read their bound at exactly
-- that count.  The depth face is the outlier reading a linear cap where
-- its siblings read a fold count.
--
-- THE BOUND MAY NOT BE TOWER-VALUED, and that is the constraint that
-- makes this a choice rather than a shrug.  The consumers spend the
-- depth bound as a free parameter — `subscribeE-inner-nodry` takes
-- `dep` and feeds it through `opIterD` into a LEVEL — so enlarging it
-- costs no signature but buys levels, and levels exponentiate.  Handing
-- them a tower would demand tower-many stories, which is the height
-- budget `Caps`'s own header defends when it forbids `cWid` from
-- re-entering the delivery count.  A fold count is not tower-valued.
depth-capped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  slotsSize (Sched.slots sched) ≤ Caps.cSize c →
  sizeᵉ b ≤ Caps.cSize c →
  suc (pathLen κ) ≤ Caps.cSize c →
  depthE g b κ bid now sched st
    ≤ Caps.cSize c + Caps.cSize c + Caps.cSize c
depth-capped c g b κ bid now sched st cap slB szB pκ =
  ≤-trans (depth-compositional g b κ bid now sched st)
          (+-mono-≤ (+-mono-≤ szB (≤-trans (n≤1+n (pathLen κ)) pκ))
                    (storeNest-capped c sched st cap slB))
