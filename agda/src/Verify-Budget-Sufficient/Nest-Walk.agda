-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; _++_; foldr)
open import Data.Nat using (ℕ; _+_; _⊔_; _≤_)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; +-identityʳ; +-assoc; +-monoˡ-≤; m≤m⊔n)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Rx.Prim using (Tick; Id; Source; Gas; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_;
   map-f; scan-f; take-f; from-inner; thru-outer;
   foldPath; dispatchShare; stepFrame)
open import Verify-Budget-Sufficient.Nest-Store using (nodeNest; pathNestD)

-- THE TWO MEASURES THE WALK MOVES TOGETHER.  A frame's node stores what
-- the frame emits -- a `scan`'s accumulator IS its output -- so charging
-- the nodes map and the values in flight separately pays the same wrap
-- twice, and the path measure charges it once.  Reading them under one
-- `⊔` is what makes the frame clause telescope.
nodesMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

nestDᵛˢ : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → ℕ
nestDᵛˢ {u = u} = foldr (λ v acc → nestDᵛ u v ⊔ acc) 0

-- ONE FRAME'S SHARE OF THE PATH MEASURE, split out so the frame clause
-- can spend it.  It is `pathNestD`'s own step and nothing else, which
-- the equation below is the whole proof of.
frameNestD : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameNestD (map-f f)         = nestDᵗ f
frameNestD (scan-f f _)      = nestDᵗ f
frameNestD (take-f _)        = 0
frameNestD (from-inner _ _ _) = 0
frameNestD (thru-outer _ _)  = 1

pathNestD-cons : ∀ {n} {Γ : Ctx n} {s u t} (f : Frame Γ s u) (p : Path Γ u t) →
  pathNestD (f ↠ p) ≡ frameNestD f + pathNestD p
pathNestD-cons (map-f f)          p = refl
pathNestD-cons (scan-f f _)       p = refl
pathNestD-cons (take-f _)         p = refl
pathNestD-cons (from-inner _ _ _) p = refl
pathNestD-cons (thru-outer _ _)   p = refl

-- ONE FRAME'S STORE GROWTH, AND ITS EMISSION'S, UNDER ONE CHARGE.  The
-- frame installs or updates at most its own node and hands the walk
-- what it emitted, and both are the frame's function applied to what it
-- was given -- so the pair moves together by the frame's own wrap.
-- Stating it as one `⊔` rather than two bounds is not presentation: a
-- `scan` deepens its accumulator and emits that same accumulator, so
-- two separate charges pay for one wrap twice and the path measure only
-- ever charges it once.
--
-- PROBED: `Probed.Cascade-Chain-Count` reads the walk this leaf and its
--   sibling compose into -- `chainStep`, whose bound follows from the
--   two of them -- by `refl` at the crossing width and on four further
--   families, including the only one in reach whose stored value is
--   observable-typed, so that the left side can move at all.  It also
--   pins the CASCADE-level conclusion above that, at the same shapes
--   and with the chain list DUPLICATED, where the max climbs one a copy.
--   And it pins a path built rather than run, carrying a `scan` frame
--   whose wrap the program never mentions: that row is what a
--   program-denominated charge fails and this one clears, and it is
--   evidence about the frame charge specifically.  Every row runs the
--   EVALUATOR against the composed bound, so a red one refutes this
--   leaf or its sibling.  NOT covered: `Γ₂` alone, at one slot shape.
postulate
  stepFrame-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now f p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals) + frameNestD f

-- THE SHARE SINK, WHICH IS WHERE THE PATH MEASURE HAS NOTHING LEFT TO
-- SPEND.  `pathNestD` charges a `share-sink` zero, so the fan-out has
-- to leave the two measures exactly where it found them -- and it fans
-- the SAME values into every registration on the share, so what makes
-- that true is that the registrations touch DISJOINT nodes: each walk
-- reads its own subscription's state, so a `⊔` over the lot is a `⊔`
-- and not a sum.  An induction over the admitted list cannot see that,
-- because its own hypothesis is stated against the running state and so
-- accumulates one sibling's growth into the next one's budget.  That is
-- the whole of what is postulated here, and it is why this leaf is not
-- the walk's third clause.
--
-- PROBED: `Probed.Cascade-Chain-Count`, jointly with `stepFrame-nodes`
--   and through the same rows -- the receipt is written out there.  Not
--   one of those families reaches a `share-sink` mid-chain, so what the
--   rows cover here is that the walk clears its bound WITHOUT this arm
--   ever firing, which is coverage of the sibling and not of this one.
postulate
  dispatchShare-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    nodesMax (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals)

-- THE WALK ITSELF, WHICH IS NOW A TELESCOPE.  Each frame spends its own
-- term of `pathNestD` and hands the rest of the path a state and a
-- value list already charged for; the root spends nothing because it
-- only emits, and the share sink spends nothing because the measure
-- gives it nothing to spend.
foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ (nodesMax st ⊔ nestDᵛˢ vals) + pathNestD path
foldPath-nodes sf gas id now envSrc root vals evs fin sched st =
  ≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))
          (≤-reflexive (sym (+-identityʳ _)))
foldPath-nodes sf gas id now envSrc (share-sink i) vals evs fin sched st =
  ≤-trans (dispatchShare-nodes sf gas id now i vals fin sched st)
          (≤-reflexive (sym (+-identityʳ _)))
foldPath-nodes sf gas id now envSrc (f ↠ p) vals evs fin sched st =
  ≤-trans (foldPath-nodes sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁)
    (≤-trans (+-monoˡ-≤ (pathNestD p)
                        (stepFrame-nodes sf id now f p vals fin sched st))
    (≤-trans (≤-reflexive (+-assoc (nodesMax st ⊔ nestDᵛˢ vals)
                                   (frameNestD f) (pathNestD p)))
             (≤-reflexive (cong ((nodesMax st ⊔ nestDᵛˢ vals) +_)
                                (sym (pathNestD-cons f p))))))
  where
  step  = stepFrame sf id now f p vals fin sched st
  vals′ = proj₁ step
  evs′  = proj₁ (proj₂ step)
  fin′  = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))
