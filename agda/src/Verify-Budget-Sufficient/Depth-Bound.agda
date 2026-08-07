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

open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; _⊔_; z≤n)
open import Data.Nat.Properties using (≤-trans; +-mono-≤; n≤1+n; ≤-refl;
                                       ⊔-lub; m≤m+n; m≤n+m; ≤ᵇ⇒≤)
open import Data.Bool    using (Bool; true)
open import Data.List    using (List; []; _∷_; foldr; tabulate; all; sum)
open import Data.Fin     using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Gas; Tick; Id)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ; sizeᵛ)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; scripted; shared;
                                NodeId; NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                Path; slotsSize; slotSize)

-- the wet family (pathLen via Wet → … → Measures) and the caps face
-- (Caps, capsOK? via Subscribe-Face → Caps-Face), both public chains
open import Verify-Budget-Sufficient.Wet
open import Verify-Budget-Sufficient.Subscribe-Face
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

-- `storeNestMax` and `depth-compositional` LANDED 2026-08-06: the
-- measure and the compositional bound moved to their own module
-- (Depth-Compositional — an assembly over the census's three named
-- BUCKET-(d) postulates plus the burst-zero/installNode kit), because
-- that module defines what this one consumes and the reverse import
-- would be a cycle.  The 2026-08-05 census findings travelled with it.
open import Verify-Budget-Sufficient.Depth-Compositional
  using (nodeNestMax; nodesNestMax; slotNest; slotsNestMax; storeNestMax;
         depth-compositional)

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
node-nest-bounded B (scan-st {t} v)   h = ≤ᵇ⇒≤ (sizeᵛ t v) B (T-to h)
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

slotNest-≤-slotSize : ∀ {n} {Γ : Ctx n} {t} (s : Slot Γ t) →
  slotNest s ≤ slotSize s
slotNest-≤-slotSize (scripted _) = z≤n
slotNest-≤-slotSize (shared _)   = ≤-refl

tabulate-⊔≤-sum : ∀ {n} (f g : Fin n → ℕ) → (∀ i → f i ≤ g i) →
  foldr _⊔_ 0 (tabulate f) ≤ sum (tabulate g)
tabulate-⊔≤-sum {zero}  f g dom = z≤n
tabulate-⊔≤-sum {suc n} f g dom =
  ⊔-lub (≤-trans (dom fzero)
                 (m≤m+n (g fzero) (sum (tabulate (λ i → g (fsuc i))))))
        (≤-trans (tabulate-⊔≤-sum (λ i → f (fsuc i)) (λ i → g (fsuc i))
                                  (λ i → dom (fsuc i)))
                 (m≤n+m (sum (tabulate (λ i → g (fsuc i)))) (g fzero)))

slots-nest-≤-size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) →
  slotsNestMax sl ≤ slotsSize sl
slots-nest-≤-size {n} sl =
  tabulate-⊔≤-sum {n} (λ i → slotNest (sl i)) (λ i → slotSize (sl i))
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
