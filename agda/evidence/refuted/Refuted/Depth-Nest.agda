-- SUBSCRIBE-TIME DEPTH IS NOT BOUNDED BY PROGRAM SYNTAX.  A `scanᵉ`
-- whose step function wraps its own accumulator gains nesting levels
-- PER TICK, so the depth grows in `wraps × ticks` while every syntactic
-- right-hand side grows in `wraps + ticks`.  A sum cannot dominate a
-- product, so neither `depth-all-bound` nor `depth-compositional`
-- itself is true as stated — nor, one level up, `depth-capped`, whose
-- `3 · cSize` is a CONSTANT multiple of a bound the same product
-- outruns.
--
-- AND THE THIRD WITNESS IS THE ONE THAT NAMES THE REPAIR.
-- `depth-capped` checks `capsOK?` at the ENTRY state and concludes about
-- a depth reached much later.  The deeply nested value here is the
-- scan's stored ACCUMULATOR, and `capsOK?`'s `stBounded?` reaches
-- `boundedNode`, which tests `sizeᵛ t v ≤ᵇ cSize` for exactly a
-- `scan-st`.  So the hypothesis is satisfied where it is CHECKED and
-- violated where it is SPENT: at the entry state the nodes are empty and
-- any caps pass, while by the twenty-ninth tick the accumulator is an
-- order of magnitude past `cSize`.  Everywhere else the caps face
-- already handles this by reporting GROWTH — a subscribe returns
-- `frameStep j ↦ frameStep (j + j′)`, and `sub-charge` produces exactly
-- such a `j′` over exactly this burst.  The depth face is the one place
-- that reads a level it does not report, and that is the defect rather
-- than the arithmetic.
--
-- THE MECHANISM, and it is the finding rather than the witness.
--
--   (1) `depthE` of a `scanᵉ` charges its emissions NOTHING.  The frame
--       is `scan-f`, `depthFrame` of a `scan-f` is 0, and
--       `burst-scf-zero` is proven.  So a scan is a free generator of
--       nested observables.
--   (2) A scan's state type may BE an observable, and its step function
--       may put the old accumulator inside a new one.  `w` merge/of
--       layers per step means emission `k` is nested `w · k` deep, from
--       syntax that does not grow with `k` at all.
--   (3) Nesting is exactly what `depthE` charges: one `suc` per
--       `mergeAllᵉ` layer, through `depthFrame`'s thru-outer arc.
--   (4) The syntax pays 4 per wrap and 1 per listed source value, so
--       `sizeᵉ b` is `4w + k + 9` — a SUM in the same two variables the
--       depth multiplies.
--
-- THIS IS `Refuted.Depth-Chain` ONE AXIS OVER.  There the left side grew
-- in the chain LENGTH while the right grew in one def's SIZE; here the
-- left grows in `w · k` while the right grows in `w + k`.  Both are the
-- same defect: a right-hand side stated in a currency the left side does
-- not spend.  The chain finding forced the slot half from a max into a
-- sum, and a sum was enough for it.  No syntactic term is enough for
-- this one.
--
-- BOTH SLOPES WERE MEASURED BEFORE THEY WERE CROSSED, which is what
-- makes this a mechanism finding and not a lucky program:
--
--     w   k    sizeᵉ b    depth      cap
--     1   3       16          4       17
--     3   5       26         16       27
--     4  12       37         49       38     ← crossed
--
-- The middle row is the one that identifies the mechanism: moving both
-- axes at once multiplies the left and adds to the right.  The third
-- needs no bigger step function than the second — four wraps instead of
-- three — and no source values that were not already listable.
--
-- WHAT THIS SAYS ABOUT THE REPAIR, and it is a design question rather
-- than a route.  The quantity actually spent is the NESTING OF A VALUE
-- REACHABLE AT SUBSCRIBE TIME, and `sizeᵛ (obs t) v` IS `sizeᵉ v`, so
-- the caps face already bounds it — `valCaps?` tests
-- `sizeᵛ u v ≤ᵇ Caps.cSize c`, and `sub-charge` already delivers
-- `burstCaps?` over exactly the burst this refutation reads.  So the
-- currency that works is the CAPS currency, which grows along the run
-- through `frameStep`, and not any function of the program text.  That
-- makes the repair a restatement of the depth face over `Caps`, and
-- CLAUDE.md's licence for adding a hypothesis is precisely this: the
-- unconditional form has been refuted.
--
-- STATED AS HYPOTHESES, because `depth-compositional` is a REAL BODY
-- resting on `depth-all-bound` — so at the moment this file was written
-- the postulate set was inconsistent, and a refutation that imported
-- either statement would die with the repair.  Same reason
-- `Refuted.Depth-Chain` states its two.
--
-- SUPERSEDES nothing.  `Refuted.Depth-Chain` kills the max currency for
-- the SLOT half and is repaired inside the syntactic currency;
-- `Refuted.Depth-Conn` kills a free-def quantification.  This one says
-- no syntactic currency can work at all.
module Refuted.Depth-Nest where

open import Data.Bool  using (false; true)
open import Data.Empty using (⊥)
open import Data.List  using (List; []; _∷_)
open import Data.Nat   using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-reflexive)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec   using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ;
  fstᵗ; varᵗ; ofᵉ; mergeAllᵉ; scanᵉ; sizeᵉ)
open import Rx.Frame-Width using (outWᵉ; innWᵉ; dWᵉ; pmIᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator using (EvalSt; Sched; Path; NodeState; AllOp; mergeᵒ;
  merge-st; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthAll)
open import Verify-Budget-Sufficient.Depth-Compositional using (depthCapN;
  maxInputᵉ; storeNestMax)

gasN : ℕ → Gas
gasN zero    = g0
gasN (suc m) = gs (gasN m)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

----------------------------------------------------------------------
-- THE INSTRUMENT.  `wraps w` puts `w` merge/of layers around the
-- accumulator and `nats k` lists `k` synchronous source values, so the
-- two axes move independently and the slopes above are attributable.
----------------------------------------------------------------------

Step : Set
Step = Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)

accᵗ : Step
accᵗ = fstᵗ (varᵗ (here refl))

wraps : ℕ → Step → Step
wraps zero    t = t
wraps (suc m) t = strmᵗ (mergeAllᵉ (ofᵉ (wraps m t ∷ [])))

nats : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
nats zero    = []
nats (suc m) = nat̂ m ∷ nats m

seedᵗ : Tm Γ₀ [] [] [] (obs natᵗ)
seedᵗ = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

prog : ℕ → ℕ → Closed Γ₀ (obs natᵗ)
prog w k = scanᵉ (wraps w accᵗ) seedᵗ (ofᵉ (nats k))

-- the merge that CONSUMES the scan: the free generator only costs
-- anything where something subscribes to what it emits
rootProg : ℕ → ℕ → Closed Γ₀ natᵗ
rootProg w k = mergeAllᵉ (prog w k)

initSt₀ : NodeState Γ₀
initSt₀ = merge-st 0 false

----------------------------------------------------------------------
-- THE CROSSING at w = 4, k = 12.  Gas is 70, comfortably past the 48
-- levels the twelfth emission carries, so no figure here is a value
-- truncated by exhausted fuel.
----------------------------------------------------------------------

schedN : Sched Γ₀
schedN = sched-init (rootProg 4 12) slots₀

stN : EvalSt (rootProg 4 12)
stN = st-init (rootProg 4 12)

depthN : depthAll (gasN 70) mergeᵒ initSt₀ (prog 4 12)
           (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedN stN ≡ 49
depthN = refl

capN : depthCapN {e = rootProg 4 12} (suc (sizeᵉ (prog 4 12)))
         (maxInputᵉ (prog 4 12)) (root {Γ = Γ₀} {t = natᵗ}) schedN stN ≡ 38
capN = refl

-- the PARENT's two sides at the merge that consumes the scan.  `depthE`
-- of a `mergeAllᵉ` IS the `depthAll` above, so the leaf's refutation and
-- the assembly's are the same measurement read at two indices — which is
-- the cheaper half being the leaf, exactly as CLAUDE.md's rule about
-- probing an assembly's conclusion says.
depthP : depthE (gasN 70) (rootProg 4 12) (root {Γ = Γ₀} {t = natᵗ})
           0 0 schedN stN ≡ 49
depthP = refl

parentP : sizeᵉ (rootProg 4 12) + pathLen (root {Γ = Γ₀} {t = natᵗ})
            + storeNestMax schedN stN ≡ 38
parentP = refl

----------------------------------------------------------------------
-- THE WITNESSES
----------------------------------------------------------------------

depth-all-bound-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
     (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthAll g op initSt b κ bid now sched st
       ≤ depthCapN (suc (sizeᵉ b)) (maxInputᵉ b) κ sched st) → ⊥
depth-all-bound-absurd h =
  ≤⇒≤ᵇ (subst₂ _≤_ depthN capN
          (h (gasN 70) mergeᵒ initSt₀ (prog 4 12) root 0 0 schedN stN))

depth-compositional-sum-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g b κ bid now sched st
       ≤ sizeᵉ b + pathLen κ + storeNestMax sched st) → ⊥
depth-compositional-sum-absurd h =
  ≤⇒≤ᵇ (subst₂ _≤_ depthP parentP
          (h (gasN 70) (rootProg 4 12) root 0 0 schedN stN))

----------------------------------------------------------------------
-- THE SECOND CROSSING, and it is the same arithmetic one level up.
-- `depth-capped` is the CAPS-CONDITIONED interface the rest of the
-- proof spends, and it looked safe: at the first witness its
-- `3 · cSize` gives 114 against a depth of 49.  But the multiplier is a
-- CONSTANT and the gap is a product, so the margin is spent by moving
-- the same two axes further.  The only lower bound its hypotheses put on
-- `cSize` is `sizeᵉ b`, so `cSize` may be taken at exactly `sizeᵉ b`,
-- and then seven wraps over twenty-nine ticks gives 204 against 201.
--
-- ITS CALL SITE IS NOT WHERE IT FAILS.  `Caps-Bridge` applies it at
-- `c := baseCaps e ins`, whose `cSize` reads `entryCeil` — a ceiling the
-- caps recurrence reads directly rather than bracketing, on the stated
-- grounds that the static width measures TOWER in the syntax and no
-- closed bracket worth proving exists.  This is that same fact arriving
-- for DEPTH: the statement is false because it is quantified over any
-- `c` its four hypotheses admit, and those hypotheses bound `cSize`
-- below by a syntactic sum.
----------------------------------------------------------------------

schedQ : Sched Γ₀
schedQ = sched-init (rootProg 7 29) slots₀

stQ : EvalSt (rootProg 7 29)
stQ = st-init (rootProg 7 29)

-- `cSize` at exactly `sizeᵉ b`, which is all the hypotheses demand
capsQ : Caps
capsQ = caps 67 67 67

okQ : capsOK? capsQ schedQ stQ ≡ true
okQ = refl

sizeQ : sizeᵉ (rootProg 7 29) ≡ 67
sizeQ = refl

depthQ : depthE (gasN 215) (rootProg 7 29) (root {Γ = Γ₀} {t = natᵗ})
           0 0 schedQ stQ ≡ 204
depthQ = refl

three : Caps.cSize capsQ + Caps.cSize capsQ + Caps.cSize capsQ ≡ 201
three = refl

depth-capped-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (c : Caps) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
     (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
     capsOK? c sched st ≡ true →
     slotsSize (Sched.slots sched) ≤ Caps.cSize c →
     sizeᵉ b ≤ Caps.cSize c →
     suc (pathLen κ) ≤ Caps.cSize c →
     depthE g b κ bid now sched st
       ≤ Caps.cSize c + Caps.cSize c + Caps.cSize c) → ⊥
depth-capped-absurd h =
  ≤⇒≤ᵇ (subst₂ _≤_ depthQ three
          (h capsQ (gasN 215) (rootProg 7 29) root 0 0 schedQ stQ
             okQ z≤n (≤-reflexive sizeQ) (s≤s z≤n)))

------------------------------------------------------------------
-- §D  THE WIDTH ROUTE IS DEAD, AND THIS IS WHY IT LOOKED ALIVE
--
-- `Rx.Frame-Width`'s `innWⱽ` and `pmIⱽ` each carry an EXPONENTIAL at a
-- `scanᵉ` — `(pmIᵗⱽ … f ⊔ 1) ^ outWⱽ … e`, a per-fold multiplier raised
-- to the source's payload count — and that reads, from the clause
-- alone, exactly like the mechanism §A–§C refute.  It is not.  The
-- exponential's BASE is `pmIᵗⱽ … 0 f ⊔ 1`, and a step function that
-- merely re-wraps its accumulator has `pmIᵗⱽ … 0 f ≡ 1`: one wrap layer
-- is `strmᵗ (mergeAllᵉ (ofᵉ (t ∷ [])))`, whose `outWⱽ` is
-- `1 * innWⱽ (ofᵉ (t ∷ []))` — it MULTIPLIES BY ONE and adds nothing.
-- So the base is 1, `1 ^ k` is 1, and the whole family is blind to `w`.
--
-- That is not an accident of these four measures; it is what they
-- measure.  Width is how many payloads travel abreast, and a wrap adds
-- DEPTH — one more layer on the same single payload.  `widthMax` below
-- is the max of all four at once, so the row refutes the entire route
-- and not one candidate: 24 against a depth of 49, and the 24 is `2 * k`
-- with no `w` in it at all.
--
-- LOAD-BEARING.  Every summand is computed, not degenerate: `outWᵉ` is
-- 24 and grows with `k`, so the row fails the moment any measure here
-- learns to see a wrap.  What makes it decisive is the ⊔: a bound by
-- ANY function of these four is a bound by their max up to
-- monotonicity, so no reshuffling of them survives.
--
-- WHAT SURVIVES is the SHAPE, and it is already charged elsewhere:
-- `scanFrame-caps` pays a scan frame `length vals * suc (sizeᵗ fn)` —
-- payload count times step size, this witness's `k · w` with both
-- factors named.  The depth face needs a measure of that shape; what it
-- may not do is read one off the width family, which does not have it.
------------------------------------------------------------------

widthMax : ∀ {n} {Γ : Ctx n} {t} → Slots Γ → Closed Γ t → ℕ
widthMax {n = n} sl e =
  outWᵉ n sl e ⊔ innWᵉ n sl e ⊔ dWᵉ n sl e ⊔ pmIᵉ n sl 0 e

widthN : widthMax slots₀ (rootProg 4 12) ≡ 24
widthN = refl

width-route-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e′ : Closed Γ t} {u}
     (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
     (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e′) →
     depthAll g op initSt b κ bid now sched st ≤ widthMax sl (mergeAllᵉ b))
  → ⊥
width-route-absurd h =
  ≤⇒≤ᵇ (subst₂ _≤_ depthN widthN
          (h (gasN 70) mergeᵒ initSt₀ (prog 4 12) root 0 0 slots₀ schedN stN))
