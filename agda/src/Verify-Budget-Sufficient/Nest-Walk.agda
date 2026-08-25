-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldr)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤;
   *-identityˡ; *-monoˡ-≤; *-monoʳ-≤;
   m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Prim using (Tick; Id; Source; Gas; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; Fn; _×ᵗ_; obs; sizeᵗ; applyFn)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_;
   map-f; scan-f; take-f; from-inner; thru-outer;
   foldPath; dispatchShare; stepFrame; shareGo; shareAdmit; shareLatch; RegId;
   NodeId; AllOp)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Nest-Store using
  (nodeNest; pathNestD; pathNestF; frameNestF; 1≤frameNestF; nest-telescope; nestUnit)

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
frameNestD (map-f f)          = nestDᵗ f
frameNestD (scan-f f _)       = nestDᵗ f
frameNestD (take-f _)         = 0
frameNestD (from-inner _ _ _) = 0
frameNestD (thru-outer _ _)   = 1

pathNestD-cons : ∀ {n} {Γ : Ctx n} {s u t} (f : Frame Γ s u) (p : Path Γ u t) →
  pathNestD (f ↠ p) ≡ frameNestD f + pathNestD p
pathNestD-cons (map-f _)          p = refl
pathNestD-cons (scan-f _ _)       p = refl
pathNestD-cons (take-f _)         p = refl
pathNestD-cons (from-inner _ _ _) p = refl
pathNestD-cons (thru-outer _ _)   p = refl

-- APPLYING A STEP FUNCTION COSTS ITS OWN SYNTAX TIMES A FACTOR, and the
-- factor is the whole content: substituting a value into a term wraps
-- it by the term's own nesting once per OCCURRENCE, not once.  Two to
-- the size dominates that, since occurrences are bounded by size and
-- nesting a binder raises the power rather than the base.
--
-- TWIN: `applyFn-iterSize` — the same substitution over the same
--   `evalWith` induction on the SIZE face, proven, clause for clause;
--   its sibling `applyFn-iterFold` is the width face of it.  Both are
--   multiplicative for exactly this reason, which is what makes the
--   additive form below a mis-reading of the precedent rather than a
--   simplification of it.
-- REFUTED: `Refuted.Apply-Fn-Nest` kills the additive form — two
--   against one, at a step function naming its payload on both sides
--   of one `mapᵉ`.
postulate
  applyFn-nest : ∀ {n} {Γ : Ctx n} {s u}
    (fn : Fn Γ [] [] [] s u) (v : Val Γ s) →
    nestDᵛ u (applyFn fn v) ≤ 2 ^ sizeᵗ fn * (nestDᵗ fn + nestDᵛ s v)

-- and the same over a burst, which is the map frame's actual argument
mapVals-nest : ∀ {n} {Γ : Ctx n} {s u}
  (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
  nestDᵛˢ (map (applyFn fn) vals) ≤ 2 ^ sizeᵗ fn * (nestDᵗ fn + nestDᵛˢ vals)
mapVals-nest fn []           = z≤n
mapVals-nest {u = u} fn (v ∷ vs) =
  ⊔-lub (≤-trans (applyFn-nest fn v)
                 (*-monoʳ-≤ (2 ^ sizeᵗ fn)
                    (+-monoʳ-≤ (nestDᵗ fn) (m≤m⊔n (nestDᵛ _ v) (nestDᵛˢ vs)))))
        (≤-trans (mapVals-nest fn vs)
                 (*-monoʳ-≤ (2 ^ sizeᵗ fn)
                    (+-monoʳ-≤ (nestDᵗ fn) (m≤n⊔m (nestDᵛ _ v) (nestDᵛˢ vs)))))

-- ONE FRAME, AND THE `⊔` IS WHY THIS IS ONE STATEMENT RATHER THAN TWO.
-- A frame moves its own node and the values it hands on TOGETHER, by
-- its own wrap: a `scan` stores the accumulator it emits, so a bound on
-- the node that did not also bound the emission would be spent by the
-- next frame and a bound on the emission alone would not survive the
-- store.  Charging the pair against the pair is what lets the walk
-- above telescope with nothing left over at either end.
--
-- AND THE FIVE FRAMES ARE FIVE DIFFERENT FACTS, which is why the arms
-- are named separately below rather than left inside one statement: the
-- map frame is a substitution lemma, the scan frame is that plus the
-- store it makes, the take frame is a filter and must be free, and the
-- two *All frames are the subscribe machinery, where a frame reaches
-- the walk again through an inner.  Only the two that SUBSTITUTE carry
-- the factor; the other three are charged one, and `frameNestF` is
-- where that split is written down.
postulate
  stepFrame-nodes-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (nid : NodeId) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (scan-f fn nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ 2 ^ sizeᵗ fn * ((nodesMax st ⊔ nestDᵛˢ vals) + nestDᵗ fn)

  stepFrame-nodes-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (nid : NodeId) (p : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (take-f nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals)

  stepFrame-nodes-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp)
    (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (from-inner op allNid inst) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals)

  stepFrame-nodes-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (p : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (thru-outer op nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals) + 1

stepFrame-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  let r = stepFrame sf id now f p vals fin sched st in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ frameNestF f * ((nodesMax st ⊔ nestDᵛˢ vals) + frameNestD f)
stepFrame-nodes sf id now (map-f fn) p vals fin sched st =
  ⊔-lub (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _)) up)
        (≤-trans (mapVals-nest fn vals)
                 (*-monoʳ-≤ (2 ^ sizeᵗ fn)
                    (≤-trans (≤-reflexive (+-comm (nestDᵗ fn) (nestDᵛˢ vals)))
                             (+-monoˡ-≤ (nestDᵗ fn)
                                        (m≤n⊔m (nodesMax st) (nestDᵛˢ vals))))))
  where
  X : ℕ
  X = (nodesMax st ⊔ nestDᵛˢ vals) + nestDᵗ fn
  up : X ≤ 2 ^ sizeᵗ fn * X
  up = ≤-trans (≤-reflexive (sym (*-identityˡ X)))
               (*-monoˡ-≤ X (1≤frameNestF (map-f fn)))
stepFrame-nodes sf id now (scan-f fn nid) p vals fin sched st =
  stepFrame-nodes-scan sf id now fn nid p vals fin sched st
stepFrame-nodes sf id now (take-f nid) p vals fin sched st =
  ≤-trans (≤-trans (stepFrame-nodes-take sf id now nid p vals fin sched st)
                   (m≤m+n _ 0))
          (≤-reflexive (sym (*-identityˡ _)))
stepFrame-nodes sf id now (from-inner op allNid inst) p vals fin sched st =
  ≤-trans (≤-trans (stepFrame-nodes-inner sf id now op allNid inst p vals fin sched st)
                   (m≤m+n _ 0))
          (≤-reflexive (sym (*-identityˡ _)))
stepFrame-nodes sf id now (thru-outer op nid) p vals fin sched st =
  ≤-trans (stepFrame-nodes-thru sf id now op nid p vals fin sched st)
          (≤-reflexive (sym (*-identityˡ _)))

-- THE SHARE SINK, WHICH IS WHERE THE PATH MEASURE HAS NOTHING LEFT TO
-- SPEND, and the whole reason the walk is charged a UNIT on top of its
-- path.  The sink fans the arriving values into every registration on
-- the share, and each of those walks a path that lives in the REGISTRY
-- rather than in the chain being charged -- so the wraps it spends are
-- invisible to `pathNestD`, which charges a sink zero.
--
-- WHAT THE UNIT BUYS, and it is not a constant chosen to fit.  A shared
-- def may only reference inputs strictly below its own index, so the
-- shares a fan-out can reach form a strict descent through the slot
-- vector; the wraps it can spend are therefore the DEFS' wraps, summed,
-- which is `slotsNestSum` and so sits inside one unit however deeply
-- the shares nest.
--
-- AND WHAT IS ACTUALLY HARD is not the ceiling but the fan-out's shape:
-- the registrations touch DISJOINT nodes, so the nodes map moves by the
-- deepest of them and not by their sum.  An induction over the admitted
-- list cannot see that -- its hypothesis is stated against the running
-- state, so one sibling's growth lands in the next one's base -- which
-- is what keeps this a leaf rather than a fold like the walk above it.
--
-- AND THE FOLD IS WHERE IT IS HARD, WHICH IS WHY THIS IS THE LEAF.  Each
-- admitted registration walks its own path and stores at its own node,
-- so the map moves by the DEEPEST of them; but a fold's hypothesis is
-- stated against the running state, so one sibling's growth lands in the
-- next one's base and an n-registration share is charged n paths.  The
-- measurement says it does not stack -- three against six where the
-- naive fold would predict a multiple.
--
-- DEAD ROUTE: strengthening the fold to a PRESERVATION -- carry a
--   ceiling `K`, show each step re-establishes it, which is how the caps
--   face avoids exactly this stacking with a pointwise predicate over
--   the nodes map instead of a MAX.  It does not close here: a step also
--   REGISTERS the inners it subscribes, so the premise bounding the
--   registry's own wraps has to be re-established at the grown registry,
--   and that quantity provably grows -- it is what the parent charges a
--   whole width factor for.  A preservation over the nodes map alone is
--   not enough, and one over the store is false.
-- REFUTED: `Refuted.Share-Sink-Nodes` kills the unit-free form of the
--   statement below, three against one, and against two when the whole
--   store measure is charged in place of the nodes map.
postulate
  shareGo-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    nodesMax (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals) + nestUnit e sl

-- AND THE SINK ITSELF IS THREE ARMS OVER THAT FOLD, none of which
-- touches the nodes map: out of dispatch gas the state is returned
-- untouched, and the finishing arm latches the share's source into the
-- dying and completed ledgers, which are not the map.  So the whole of
-- the sink's growth is the fold's, and the leaf is the fold.
dispatchShare-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  nodesMax (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
    ≤ (nodesMax st ⊔ nestDᵛˢ vals) + nestUnit e sl
dispatchShare-nodes sl sf zero id now i vals fin sched st hsl =
  ≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _)
dispatchShare-nodes sl sf (suc gas) id now i vals false sched st hsl =
  shareGo-nodes sl sf gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sched st hsl
dispatchShare-nodes sl sf (suc gas) id now i vals true sched st hsl =
  shareGo-nodes sl sf gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) hsl

-- THE WALK ITSELF, WHICH IS A TELESCOPE.  Each frame spends its own term
-- of `pathNestD` and hands the rest of the path a state and a value list
-- already charged for; the root spends nothing because it only emits,
-- and the sink spends the unit the path measure cannot give it.  The
-- unit is charged ONCE for the whole walk rather than once per frame,
-- which is what the additive shape of the two leaves buys.
foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ)
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ pathNestF path * ((nodesMax st ⊔ nestDᵛˢ vals) + (pathNestD path + nestUnit e sl))
foldPath-nodes sl sf gas id now envSrc root vals evs fin sched st hsl =
  ≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes sl sf gas id now envSrc (share-sink i) vals evs fin sched st hsl =
  ≤-trans (dispatchShare-nodes sl sf gas id now i vals fin sched st hsl)
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} sl sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl =
  ≤-trans (foldPath-nodes sl sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
             (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl))
    (≤-trans (*-monoʳ-≤ (pathNestF p)
                (+-monoˡ-≤ (pathNestD p + U)
                           (stepFrame-nodes sf id now f p vals fin sched st)))
    (≤-trans (nest-telescope (frameNestF f) (pathNestF p) B (frameNestD f)
                             (pathNestD p + U) (1≤frameNestF f))
             (≤-reflexive
               (cong (λ z → frameNestF f * pathNestF p * (B + z))
                     (trans (sym (+-assoc (frameNestD f) (pathNestD p) U))
                            (cong (_+ U) (sym (pathNestD-cons f p))))))))
  where
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestUnit e sl
  step   = stepFrame sf id now f p vals fin sched st
  vals′  = proj₁ step
  evs′   = proj₁ (proj₂ step)
  fin′   = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))
