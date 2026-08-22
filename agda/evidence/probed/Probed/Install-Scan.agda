-- TARGET: installScan-depth-bound
--
-- THE REGION ITS OWN RECEIPT NAMED AS UNCOVERED.  The surviving receipt
-- reads "NOT COVERED: shared-slot inner b, post-cascade state, b with
-- recursive depthE > 0", and the earlier probe could not have covered
-- them: it ran in `Ctx 0`, where there is no slot to share.  Two
-- reasons that gap is worth closing now rather than later — this leaf
-- REPLACED a statement that was outright false
-- (`storeNestMax-installScan`), and the shared-slot shape is exactly
-- what refuted its sibling on this row (Refuted.Depth-Chain).
--
-- THE FALSITY SHAPE, stated so the rows can be read against it.  The
-- left side is `depthE` at the POST-INSTALL state, whose store contains
-- `nodeNestMax (scan-st v) = sizeᵛ v`; the right side names only the
-- ENTRY store, so `v` appears nowhere in it.  If any arc on the
-- subscribe side were charged to the stored accumulator, a large enough
-- `v` would cross a bound that cannot grow with it.  The claim is
-- install-invariance, resting on `depthFrame (scan-f …) = 0`
-- definitionally.
--
-- SO THE ROWS VARY `v` AND NOTHING ELSE, over a `b` that genuinely
-- reads the store: `input` at the top of a four-link slot chain, which
-- is the shape whose arcs ADD.
--
-- THE RESULT — a confidence receipt, and the leak channel was open when
-- it was taken.  Varying only the accumulator:
--
--                     small v      big v
--   sizeᵛ v                  1         41
--   node half of store       1         41
--   post-install store      22         41
--   depth                    4          4
--
--   entry store 22   ⇒   right-hand side = 1 + (1 + 0) + 22 = 24
--
-- The third row is what makes the fourth mean something: the store the
-- left side is evaluated against EXCEEDS, by 19, the entry store the
-- right side names, so anything charged to the accumulator would have
-- been unpayable.  Nothing was charged — the depth is the four-link
-- walk, and the scan frame contributes 0.  Gas-stable at 20 and at 60,
-- which rules out a figure truncated by exhausted fuel reading as
-- invariance.
--
-- COVERED: shared-slot inner `b`; `b` with recursive `depthE` > 0 (it
-- is 4, not 0); an accumulator whose own measure dominates the entry
-- store.  NOT COVERED: post-cascade state, and a `concat-st` node
-- (whose `nodeNestMax` is a `⊔` over a queue rather than one value, so
-- it varies along an axis these rows do not touch).
module Probed.Install-Scan where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp  using (Ctx; Closed; Exp; Fn; Val; natᵗ; obs; _×ᵗ_; nat̂; emptyᵉ; mergeAllᵉ; ofᵉ; strmᵗ; fstᵗ; varᵗ;
  input; evalTm; sizeᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; root; sched-init; st-init; scan-st; scan-f; mintNode; installNode; _↠_)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax;
  depthCap;
  nodesNestMax)

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- a three-link slot chain: the arcs that ADD
baseᶜ : Closed Γ₄ natᵗ
baseᶜ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

k0 : Closed Γ₄ natᵗ
k0 = mergeAllᵉ (ofᵉ (strmᵗ (input fz) ∷ []))

k1 : Closed Γ₄ natᵗ
k1 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs fz)) ∷ []))

k2 : Closed Γ₄ natᵗ
k2 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs fz))) ∷ []))

slots₄ : Slots Γ₄
slots₄ fz                = shared baseᶜ {ok = tt}
slots₄ (fs fz)           = shared k0 {ok = tt}
slots₄ (fs (fs fz))      = shared k1 {ok = tt}
slots₄ (fs (fs (fs fz))) = shared k2 {ok = tt}

topᶠ : Fin 4
topᶠ = fs (fs (fs fz))

-- `b`, at the top of the chain, so the subscribe side really descends
-- through the store rather than returning 0 the way `emptyᵉ` did
bᶜ : Closed Γ₄ natᵗ
bᶜ = input topᶠ

-- the accumulator, at two sizes.  `obs`-typed so `sizeᵛ` can be large:
-- a nat literal's value is a constant and could not move the row.
smallObs : Exp Γ₄ [] [] [] (obs natᵗ)
smallObs = emptyᵉ

-- 40 layers, chosen so `sizeᵛ` of the accumulator EXCEEDS the entry
-- store's own figure.  Below that threshold the `⊔` in `storeNestMax`
-- swallows the node half and the varying row cannot detect anything:
-- an 11-layer first attempt measured 22/22 on both sides for exactly
-- that reason.
bigObs : Exp Γ₄ [] [] [] (obs natᵗ)
bigObs = m (m (m (m (m (m (m (m (m (m
         (m (m (m (m (m (m (m (m (m (m
         (m (m (m (m (m (m (m (m (m (m
         (m (m (m (m (m (m (m (m (m (m emptyᵉ)))))))))))))))))))))))))))))))))))))))
  where
    m : ∀ {t} → Exp Γ₄ [] [] [] (obs t) → Exp Γ₄ [] [] [] t
    m = mergeAllᵉ

vSmall : Val Γ₄ (obs (obs natᵗ))
vSmall = evalTm (strmᵗ smallObs)

vBig : Val Γ₄ (obs (obs natᵗ))
vBig = evalTm (strmᵗ bigObs)

-- the scan function is irrelevant to `depthE` and supplied only so the
-- frame can be built: `Fn` is a `Tm` with the argument in scope
fᶜ : Fn Γ₄ [] [] [] (obs (obs natᵗ) ×ᵗ natᵗ) (obs (obs natᵗ))
fᶜ = fstᵗ (varᵗ (here refl))

rootProg : Closed Γ₄ (obs (obs natᵗ))
rootProg = emptyᵉ

sched : Sched Γ₄
sched = sched-init rootProg slots₄

nid : _
nid = proj₁ (mintNode sched)

sched′ : Sched Γ₄
sched′ = proj₂ (mintNode sched)

st : EvalSt rootProg
st = st-init rootProg

stSmall : EvalSt rootProg
stSmall = installNode nid (scan-st vSmall) st

stBig : EvalSt rootProg
stBig = installNode nid (scan-st vBig) st

g20 : Gas
g20 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

g60 : Gas
g60 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs 
      (g0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      )))

-- DEGENERATE, and labelled so: these two only establish that the row
-- below has something to detect.  They would hold whatever `depthE`
-- did.
_ : sizeᵛ (obs (obs natᵗ)) vSmall ≡ 1
_ = refl

_ : sizeᵛ (obs (obs natᵗ)) vBig ≡ 41
_ = refl

-- LOAD-BEARING, and these are the rows that give the varying pair
-- below something to detect: the node half of the post-install store
-- moves with `v`, and after the resize it moves far enough to survive
-- the `⊔` against the slot chain.
_ : nodesNestMax (EvalSt.nodes stSmall) ≡ 1
_ = refl

_ : nodesNestMax (EvalSt.nodes stBig) ≡ 41
_ = refl

-- LOAD-BEARING.  The post-install store the left side is evaluated
-- against, versus the ENTRY store the right side names.  The big row
-- must exceed the entry figure or the statement is not being stressed.
_ : storeNestMax sched′ stSmall ≡ 22
_ = refl

_ : storeNestMax sched′ stBig ≡ 41
_ = refl

_ : storeNestMax sched st ≡ 22
_ = refl

-- LOAD-BEARING, and this is the row the leaf lives on: the two differ
-- in `v` and nothing else.  WHAT WOULD MAKE THEM FAIL: any subscribe-
-- side arc charged to the stored accumulator, which would make the big
-- row exceed the small one and then exceed a bound that never mentions
-- `v`.
_ : depthE g20 bᶜ (scan-f fᶜ nid ↠ root) 0 0 sched′ stSmall ≡ 4
_ = refl

_ : depthE g20 bᶜ (scan-f fᶜ nid ↠ root) 0 0 sched′ stBig ≡ 4
_ = refl

-- LOAD-BEARING against the classic false green: a figure TRUNCATED by
-- exhausted gas would also fail to move with `v`, and would read
-- exactly like install-invariance.  Tripling the gas leaves it where it
-- was, so the 4 is the walk's own length and not the fuel's.
_ : depthE g60 bᶜ (scan-f fᶜ nid ↠ root) 0 0 sched′ stBig ≡ 4
_ = refl

-- LOAD-BEARING: the statement's own right-hand side, at the entry
-- store, so a crossing reads as two numbers rather than an inference.
-- Restated over the CAP with the rest of the bound: the `⊔` with the
-- node half now sits OUTSIDE, which is what makes the entry store's
-- masking of the accumulator visible here as well.
_ : depthCap bᶜ (scan-f fᶜ nid ↠ (root {Γ = Γ₄} {t = obs (obs natᵗ)}))
      sched st ≡ 24
_ = refl
