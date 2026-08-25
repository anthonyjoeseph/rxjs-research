-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤;
   *-assoc; *-comm; m^n>0;
   *-identityˡ; *-identityʳ; *-zeroʳ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; +-mono-≤;
   *-distribˡ-+; ^-zeroˡ; +-identityʳ;
   m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub; ⊔-assoc; ⊔-mono-≤)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Tick; Id; Source; Gas; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; Fn; _×ᵗ_; obs; sizeᵗ; applyFn; _≟ᵗ_)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_;
   map-f; scan-f; take-f; from-inner; thru-outer;
   foldPath; dispatchShare; stepFrame; shareGo; shareAdmit; shareLatch; RegId;
   NodeId; AllOp; NodeState; scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
   lookupNode; setNode; scanVals)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps using (1≤pow≤)
open import Verify-Budget-Sufficient.Nest-Store using
  (nodeNest; pathNestD; pathNestF; frameNestF; 1≤frameNestF; nest-telescope; nestUnit;
   nest-inflate; pow-grow¹; pow-distrib-*)
open import Verify-Budget-Sufficient.Nest-Subst using (applyFn-nest)

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

-- and the same over a burst, which is the map frame's actual argument
abstract
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

-- THE NODE TABLE IS A `⊔`-FOLD, so a write moves it by at most what was
-- written and a read is dominated by it.  Two one-screen inductions over
-- the association list, and between them the only two facts the scan arm
-- needs about the store -- it reads its accumulator out and writes the
-- next one back, and nothing else in the table moves.
nodesFold : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesFold = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0

abstract
  setNode-nodes : ∀ {n} {Γ : Ctx n} (nid : NodeId) (ns : NodeState Γ)
    (nodes : List (NodeId × NodeState Γ)) →
    nodesFold (setNode nid ns nodes) ≤ nodeNest ns ⊔ nodesFold nodes
  setNode-nodes nid ns []             = ≤-refl
  setNode-nodes nid ns ((k , s′) ∷ r) with k ≡ᵇ nid
  ... | true  = ⊔-mono-≤ ≤-refl (m≤n⊔m (nodeNest s′) (nodesFold r))
  ... | false =
    ⊔-lub (≤-trans (m≤m⊔n (nodeNest s′) (nodesFold r))
                   (m≤n⊔m (nodeNest ns) (nodeNest s′ ⊔ nodesFold r)))
          (≤-trans (setNode-nodes nid ns r)
                   (⊔-mono-≤ ≤-refl (m≤n⊔m (nodeNest s′) (nodesFold r))))

abstract
  lookupNode-nodes : ∀ {n} {Γ : Ctx n} (nid : NodeId) (ns : NodeState Γ)
    (nodes : List (NodeId × NodeState Γ)) →
    lookupNode nid nodes ≡ just ns → nodeNest ns ≤ nodesFold nodes
  lookupNode-nodes nid ns ((k , s′) ∷ r) h with k ≡ᵇ nid | h
  ... | true  | refl = m≤m⊔n (nodeNest ns) (nodesFold r)
  ... | false | h′   = ≤-trans (lookupNode-nodes nid ns r h′)
                               (m≤n⊔m (nodeNest s′) (nodesFold r))

-- THE ITERATION, AND IT IS THE WHOLE CONTENT OF THE SCAN ARM.  A scan
-- feeds its own output back in, so the step function's factor is spent
-- once per value and its own nesting is piled on once per value:
-- `x ↦ F * (x ⊔ V + D)` iterated k times.  What the burst exponent buys
-- is that this closes at `F ^ k * (X + k * D)` -- one power and one
-- multiple, both read off the same k -- which is why the charge is
-- stated that way for every frame rather than only for this one.
abstract
  scanVals-nest : ∀ {n} {Γ : Ctx n} {s u} (W : ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (acc : Val Γ u) (vals : List (Val Γ s)) →
    length vals ≤ W →
    (nestDᵛˢ (proj₁ (scanVals fn acc vals))
       ⊔ nestDᵛ u (proj₂ (scanVals fn acc vals)))
      ≤ (2 ^ sizeᵗ fn) ^ W * ((nestDᵛ u acc ⊔ nestDᵛˢ vals) + W * nestDᵗ fn)
  scanVals-nest {u = u} W fn acc [] hlen =
    ≤-trans (⊔-lub z≤n (≤-trans (m≤m⊔n (nestDᵛ u acc) 0)
                                (m≤m+n (nestDᵛ u acc ⊔ 0) (W * nestDᵗ fn))))
            (≤-trans (≤-reflexive (sym (*-identityˡ Y)))
                     (*-monoˡ-≤ Y (1≤pow≤ (2 ^ sizeᵗ fn) W (m^n>0 2 (sizeᵗ fn)))))
    where
    Y : ℕ
    Y = (nestDᵛ u acc ⊔ 0) + W * nestDᵗ fn
  scanVals-nest {Γ = Γ} {s = s} {u = u} (suc W) fn acc (v ∷ vs) (s≤s hlen) =
    ≤-trans (≤-reflexive (⊔-assoc A′ (nestDᵛˢ outs) (nestDᵛ u last)))
            (⊔-lub head-fits tail-fits)
    where
    F D A V VS X Z A′ : ℕ
    acc′ : Val Γ u
    outs : List (Val Γ u)
    last : Val Γ u
    F   = 2 ^ sizeᵗ fn
    D   = nestDᵗ fn
    A   = nestDᵛ u acc
    V   = nestDᵛ s v
    VS  = nestDᵛˢ vs
    X   = A ⊔ (V ⊔ VS)
    Z   = X + suc W * D
    acc′ = applyFn fn (acc , v)
    A′  = nestDᵛ u acc′
    outs = proj₁ (scanVals fn acc′ vs)
    last = proj₂ (scanVals fn acc′ vs)
    1≤F : 1 ≤ F
    1≤F = m^n>0 2 (sizeᵗ fn)
    av≤X : A ⊔ V ≤ X
    av≤X = ⊔-lub (m≤m⊔n A (V ⊔ VS))
                 (≤-trans (m≤m⊔n V VS) (m≤n⊔m A (V ⊔ VS)))
    -- one application, charged against the burst's own base
    A′≤ : A′ ≤ F * (X + D)
    A′≤ = ≤-trans (applyFn-nest fn (acc , v))
                  (*-monoʳ-≤ F (≤-trans (+-monoʳ-≤ D av≤X)
                                        (≤-reflexive (+-comm D X))))
    head-fits : A′ ≤ F ^ suc W * Z
    head-fits =
      ≤-trans A′≤
        (*-mono-≤ (pow-grow¹ F (suc W) 1≤F (s≤s z≤n))
                  (+-monoʳ-≤ X (m≤m+n D (W * D))))
    -- and the rest of the fold, one shorter and one factor cheaper
    step : (A′ ⊔ VS) + W * D ≤ F * Z
    step =
      ≤-trans (+-mono-≤ (⊔-lub A′≤
                               (≤-trans (≤-trans (m≤n⊔m V VS) (m≤n⊔m A (V ⊔ VS)))
                                        (≤-trans (m≤m+n X D)
                                                 (≤-trans (≤-reflexive (sym (*-identityˡ (X + D))))
                                                          (*-monoˡ-≤ (X + D) 1≤F)))))
                        (≤-trans (≤-reflexive (sym (*-identityˡ (W * D))))
                                 (*-monoˡ-≤ (W * D) 1≤F)))
              (≤-reflexive (trans (sym (*-distribˡ-+ F (X + D) (W * D)))
                                  (cong (F *_) (+-assoc X D (W * D)))))
    tail-fits : nestDᵛˢ outs ⊔ nestDᵛ u last ≤ F ^ suc W * Z
    tail-fits =
      ≤-trans (scanVals-nest W fn acc′ vs hlen)
              (≤-trans (*-monoʳ-≤ (F ^ W) step)
                       (≤-reflexive (trans (sym (*-assoc (F ^ W) F Z))
                                           (cong (_* Z) (*-comm (F ^ W) F)))))

-- A FACTOR OF AT LEAST ONE IS FREE, and the four arms where the scan's
-- node is absent or mistyped need nothing else: they emit nothing and
-- store nothing, so the whole charge is slack.
abstract
  pow-grow : ∀ (F W Y : ℕ) → 1 ≤ F → Y ≤ F ^ W * Y
  pow-grow F W Y 1≤F =
    ≤-trans (≤-reflexive (sym (*-identityˡ Y)))
            (*-monoˡ-≤ Y (1≤pow≤ F W 1≤F))

abstract
  scan-stuck : ∀ {n} {Γ : Ctx n} {s u} (W : ℕ) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (M VS : ℕ) → M ⊔ 0 ≤ (2 ^ sizeᵗ fn) ^ W * ((M ⊔ VS) + W * nestDᵗ fn)
  scan-stuck W fn M VS =
    ≤-trans (⊔-lub (≤-trans (m≤m⊔n M VS) (m≤m+n (M ⊔ VS) (W * nestDᵗ fn))) z≤n)
            (pow-grow (2 ^ sizeᵗ fn) W ((M ⊔ VS) + W * nestDᵗ fn)
                      (m^n>0 2 (sizeᵗ fn)))

-- A SCAN ARM IS ITS NODE AND ITS OUTPUT AT ONCE, which is why the store
-- lemmas above sit beside the iteration rather than anywhere else: the
-- accumulator written back IS the last value emitted, so the `⊔` the
-- statement is phrased over is the one the fold already computes.  The
-- accumulator read out is under the table it was read from, which is
-- what lets the iteration start from the same `⊔` the conclusion does.
abstract
  stepFrame-nodes-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (nid : NodeId) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    length vals ≤ W →
    let r = stepFrame sf id now (scan-f fn nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (2 ^ sizeᵗ fn) ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * nestDᵗ fn)
  stepFrame-nodes-scan {Γ = Γ} {u = u} W sf id now fn nid p vals fin sched st hlen
    with lookupNode nid (EvalSt.nodes st) in eq
  ... | nothing                  = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ... | just (take-st _)         = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ... | just (mergeAll-st _ _ _ _) = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ... | just (switch-st _ _)     = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ... | just (exhaust-st _ _)    = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ... | just (scan-st {w} a) with w ≟ᵗ u
  ...   | no _     = scan-stuck W fn (nodesMax st) (nestDᵛˢ vals)
  ...   | yes refl =
    ⊔-lub (≤-trans (setNode-nodes nid (scan-st last) (EvalSt.nodes st))
                   (⊔-lub (≤-trans (m≤n⊔m (nestDᵛˢ outs) (nestDᵛ u last)) fold-fits)
                          (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))
                                            (m≤m+n (nodesMax st ⊔ nestDᵛˢ vals)
                                                   (W * nestDᵗ fn)))
                                   (pow-grow (2 ^ sizeᵗ fn) W _
                                             (m^n>0 2 (sizeᵗ fn))))))
          (≤-trans (m≤m⊔n (nestDᵛˢ outs) (nestDᵛ u last)) fold-fits)
    where
    outs : List (Val Γ u)
    last : Val Γ u
    outs = proj₁ (scanVals fn a vals)
    last = proj₂ (scanVals fn a vals)
    fold-fits : nestDᵛˢ outs ⊔ nestDᵛ u last
                  ≤ (2 ^ sizeᵗ fn) ^ W
                      * ((nodesMax st ⊔ nestDᵛˢ vals) + W * nestDᵗ fn)
    fold-fits =
      ≤-trans (scanVals-nest W fn a vals hlen)
              (*-monoʳ-≤ ((2 ^ sizeᵗ fn) ^ W)
                 (+-monoˡ-≤ (W * nestDᵗ fn)
                    (⊔-mono-≤ (lookupNode-nodes nid (scan-st a) (EvalSt.nodes st) eq)
                              ≤-refl)))

postulate
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
    (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (p : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    1 ≤ W → length vals ≤ W →
    let r = stepFrame sf id now (thru-outer op nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals) + W

-- THE TWO SHAPES A UNIT FACTOR TAKES ONCE THE BURST IS IN THE
-- EXPONENT, which is all that separates the three frames that charge
-- nothing from the one that charges a wrap.
abstract
  one-pow : ∀ (W Y : ℕ) → Y ≤ 1 ^ W * Y
  one-pow W Y = ≤-reflexive (sym (trans (cong (_* Y) (^-zeroˡ W)) (*-identityˡ Y)))

abstract
  zero-charge : ∀ (W X : ℕ) → X ≤ 1 ^ W * (X + W * 0)
  zero-charge W X =
    ≤-trans (≤-trans (≤-reflexive (sym (+-identityʳ X)))
                     (≤-reflexive (cong (X +_) (sym (*-zeroʳ W)))))
            (one-pow W (X + W * 0))

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
--
-- AND THE BURST IS IN THE EXPONENT BECAUSE ONE OF THE TWO THREADS.  A
-- map applies its step function to each value INDEPENDENTLY and the
-- results are read by `⊔`, so one factor covers a burst of any length
-- -- `mapVals-nest` is the proof, and it needs no bound.  A scan
-- applies it to the PREVIOUS output, so a burst of k spends the factor
-- k times and piles k copies of the function's own nesting onto the
-- accumulator.  Charging every arm `F ^ W` against `X + W * D` is what
-- makes one shape serve both: the three that charge nothing are
-- unaffected, the map arm has slack, and the scan arm is tight.
--
-- REFUTED: `Refuted.Scan-Fold-Burst` kills the burst-free form, 65
--   against 64, at the smallest step function that deepens its own
--   accumulator; the gap is unbounded in the burst, so no constant
--   repairs it, and `scanVals-nest` is the iteration that replaced it.
abstract
  stepFrame-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    1 ≤ W → length vals ≤ W →
    let r = stepFrame sf id now f p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
  stepFrame-nodes W sf id now (map-f fn) p vals fin sched st 1≤W hlen =
    ⊔-lub (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _)) up)
          (≤-trans (mapVals-nest fn vals)
                   (*-mono-≤ (pow-grow¹ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn)) 1≤W)
                      (≤-trans (≤-reflexive (+-comm (nestDᵗ fn) (nestDᵛˢ vals)))
                               (+-mono-≤ (m≤n⊔m (nodesMax st) (nestDᵛˢ vals))
                                         (nest-inflate W (nestDᵗ fn) 1≤W)))))
    where
    X : ℕ
    X = (nodesMax st ⊔ nestDᵛˢ vals) + W * nestDᵗ fn
    up : X ≤ (2 ^ sizeᵗ fn) ^ W * X
    up = ≤-trans (≤-reflexive (sym (*-identityˡ X)))
                 (*-monoˡ-≤ X (1≤pow≤ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn))))
  stepFrame-nodes W sf id now (scan-f fn nid) p vals fin sched st 1≤W hlen =
    stepFrame-nodes-scan W sf id now fn nid p vals fin sched st hlen
  stepFrame-nodes W sf id now (take-f nid) p vals fin sched st 1≤W hlen =
    ≤-trans (stepFrame-nodes-take sf id now nid p vals fin sched st)
            (zero-charge W _)
  stepFrame-nodes W sf id now (from-inner op allNid inst) p vals fin sched st 1≤W hlen =
    ≤-trans (stepFrame-nodes-inner sf id now op allNid inst p vals fin sched st)
            (zero-charge W _)
  stepFrame-nodes W sf id now (thru-outer op nid) p vals fin sched st 1≤W hlen =
    ≤-trans (stepFrame-nodes-thru W sf id now op nid p vals fin sched st 1≤W hlen)
            (≤-trans (≤-reflexive (cong (_ +_) (sym (*-identityʳ W))))
                     (one-pow W (_ + W * 1)))

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
-- THE BURST BOUND, ALONG THE RUN.  A frame's charge has to see how many
-- times it fires, and a path's burst is not a syntactic quantity: only a
-- THRU frame can hand on more values than it took, and how many is what
-- the inners it subscribes happen to emit.  So the walk takes the bound
-- as a hypothesis shaped like its own recursion -- each stage's value
-- list under `W`, the next stage's list read off the frame that just
-- ran -- and the consumer discharges it where the width face is, which
-- is where a burst is capped at all.
burstsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (p : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
burstsOK W sf id now root           vals fin sched st = length vals ≤ W
burstsOK W sf id now (share-sink _) vals fin sched st = length vals ≤ W
burstsOK W sf id now (f ↠ p)        vals fin sched st =
  (length vals ≤ W)
  × burstsOK W sf id now p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
  where step = stepFrame sf id now f p vals fin sched st

foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W →
  burstsOK W sf id now path vals fin sched st →
  nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ pathNestF path ^ W
      * ((nodesMax st ⊔ nestDᵛˢ vals) + W * (pathNestD path + nestUnit e sl))
foldPath-nodes W sl sf gas id now envSrc root vals evs fin sched st hsl 1≤W hb =
  ≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
          (one-pow W _)
foldPath-nodes {e = e} W sl sf gas id now envSrc (share-sink i) vals evs fin sched st hsl 1≤W hb =
  ≤-trans (dispatchShare-nodes sl sf gas id now i vals fin sched st hsl)
          (≤-trans (+-monoʳ-≤ (nodesMax st ⊔ nestDᵛˢ vals)
                              (nest-inflate W (nestUnit e sl) 1≤W))
                   (one-pow W _))
foldPath-nodes {e = e} W sl sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl 1≤W hb =
  ≤-trans (foldPath-nodes W sl sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
             (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl)
             1≤W (proj₂ hb))
    (≤-trans (*-monoʳ-≤ (pathNestF p ^ W)
                (+-monoˡ-≤ (W * (pathNestD p + U))
                           (stepFrame-nodes W sf id now f p vals fin sched st
                              1≤W (proj₁ hb))))
    (≤-trans (nest-telescope (frameNestF f ^ W) (pathNestF p ^ W) B
                             (W * frameNestD f) (W * (pathNestD p + U))
                             (1≤pow≤ (frameNestF f) W (1≤frameNestF f)))
             (≤-reflexive
               (cong₂ _*_ (sym (pow-distrib-* W (frameNestF f) (pathNestF p)))
                          (cong (B +_) charge)))))
  where
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestUnit e sl
  step   = stepFrame sf id now f p vals fin sched st
  vals′  = proj₁ step
  evs′   = proj₁ (proj₂ step)
  fin′   = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))

  charge : W * frameNestD f + W * (pathNestD p + U) ≡ W * (pathNestD (f ↠ p) + U)
  charge =
    trans (sym (*-distribˡ-+ W (frameNestD f) (pathNestD p + U)))
          (cong (W *_)
            (trans (sym (+-assoc (frameNestD f) (pathNestD p) U))
                   (cong (_+ U) (sym (pathNestD-cons f p)))))
