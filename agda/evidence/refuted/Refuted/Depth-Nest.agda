-- SUBSCRIBE-TIME DEPTH IS NOT BOUNDED BY PROGRAM SYNTAX.  A `scanᵉ`
-- whose step function wraps its own accumulator gains nesting levels
-- PER TICK, so the depth grows in `wraps × ticks` while every syntactic
-- right-hand side grows in `wraps + ticks`.  A sum cannot dominate a
-- product, so neither `depth-all-bound` nor `depth-compositional`
-- itself is true as stated.
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

open import Data.Bool  using (false)
open import Data.Empty using (⊥)
open import Data.List  using (List; []; _∷_)
open import Data.Nat   using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec   using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ;
  fstᵗ; varᵗ; ofᵉ; mergeAllᵉ; scanᵉ; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (EvalSt; Sched; Path; NodeState; AllOp; mergeᵒ;
  merge-st; root; sched-init; st-init)
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
