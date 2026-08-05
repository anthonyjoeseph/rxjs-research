------------------------------------------------------------------
-- THE DEPTH OBLIGATION, STATED (PROOF-STATE.md Task #13).
--
-- `sub-charge` (Caps-Bridge.agda) bounds a subscribe's growth index by
-- `opIterD … (depthE g b κ bid now sched st) …` — a receipt in terms of
-- the depth mirror at the call's own arguments.  For the receipt to be
-- SPENDABLE the depth must be bounded by something entry-computable,
-- and the naive candidates are dead: `depthE ≤ capsBase` is FALSE
-- (machine-refuted, agda/probe/Depth-Blowup-Probe.agda — scan
-- accumulators deepen per fold while capsBase gains +1 per arrival),
-- and any UNCONDITIONAL `depthE ≤ capsH` dies the same way against an
-- adversarial stored state.  The honest statement conditions on the
-- state being bounded — which is exactly the hypothesis every consumer
-- already holds, as `capsOK?`.
--
-- THE SHAPE (validated with C = 0 by
-- agda/probe/Depth-Compositional-Probe.agda, whose header traces every
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
-- Outside-in: `depth-capped` below is the ASSEMBLY — a real definition
-- consuming the two postulated pieces — so the pieces' shapes are
-- pinned by their consumer before either is ground.
--
--   · `depth-compositional` — structural induction over the mirror's
--     clauses (Caps-Depth.agda), mirroring the probe's channel trace:
--     `depthSlot` charges the shared def to `slotsNestMax`,
--     `depthFin`'s concat queue and `depthBurst`'s stepFrame read
--     charge to `nodesNestMax`, every other clause is covered by the
--     syntax/path summands.
--   · `storeNest-capped` — an inversion of `capsOK?`'s conjuncts:
--     `stBounded?`'s boundedNode clauses ARE `nodeNestMax ≤ᵇ cSize`
--     read as a test, and the slot half is `slotsNestMax ≤ slotsSize`
--     (a shared slot's def is one summand of its size) chained with
--     the consumer-supplied `slotsSize ≤ cSize`.
------------------------------------------------------------------

module Verify-Budget-Sufficient.Depth-Bound where

open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤-trans; +-mono-≤; n≤1+n)
open import Data.Bool    using (true)
open import Data.List    using (List; foldr; tabulate)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Gas; Tick; Id)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; scripted; shared;
                                NodeId; NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                Path; slotsSize)

-- the wet family (pathLen via Wet → … → Measures) and the caps face
-- (Caps, capsOK? via Subscribe-Face → Caps-Face), both public chains
open import Verify-Budget-Sufficient.Wet
open import Verify-Budget-Sufficient.Subscribe-Face
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

------------------------------------------------------------------
-- `storeNestMax` — the state's contribution to subscribe-time depth,
-- ported from Depth-Compositional-Probe § A (the validated measure).
-- The node half is `boundedNode`'s own two live clauses (Measures.agda)
-- turned from a `≤ᵇ B` test into a `⊔`; the slot half charges shared
-- defs, the one channel `stBounded?` deliberately excludes (slot defs
-- are fixed syntax within one run, but `depthSlot` reads them).
------------------------------------------------------------------

nodeNestMax : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNestMax (scan-st {t} v)       = sizeᵛ t v
nodeNestMax (concat-st {t} q _ _) = foldr (λ o acc → sizeᵉ o ⊔ acc) 0 q
nodeNestMax (take-st _)           = 0
nodeNestMax (merge-st _ _)        = 0
nodeNestMax (switch-st _ _)       = 0
nodeNestMax (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesNestMax = foldr (λ kv acc → nodeNestMax (proj₂ kv) ⊔ acc) 0

slotNest : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotNest (shared d)   = sizeᵉ d
slotNest (scripted _) = 0

slotsNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestMax {n} sl = foldr _⊔_ 0 (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestMax (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

------------------------------------------------------------------
-- the two pieces, postulated with their consumer already written below
------------------------------------------------------------------

postulate
  -- structural induction over the depth mirror; C = 0 per the probe
  depth-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g b κ bid now sched st
      ≤ sizeᵉ b + pathLen κ + storeNestMax sched st

  -- inversion of capsOK?'s stBounded? conjunct + the slots chain
  storeNest-capped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    slotsSize (Sched.slots sched) ≤ Caps.cSize c →
    storeNestMax sched st ≤ Caps.cSize c

------------------------------------------------------------------
-- THE ASSEMBLY — the entry-computable cap, under exactly the
-- hypotheses `sub-charge` already carries (at c := frameStep j c
-- there; `Caps.cSize` is all this reads, so any level's caps fit).
-- This is what turns `sub-charge`'s `opIterD … depthE …` receipt into
-- a number the instant's fuel can dominate, tower-free.
------------------------------------------------------------------

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
