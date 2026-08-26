-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Bool.ListAction using (any; all)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤; n≤1+n; m≤n+m; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤; *-assoc; *-comm; m^n>0;
  *-identityˡ; *-identityʳ; *-zeroʳ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; +-mono-≤; *-distribˡ-+;
  ^-zeroˡ; +-identityʳ; m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub; ⊔-assoc; ⊔-mono-≤)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Tick; Id; Source; Gas; g0; gs; InstEvent; value)
open import Rx.Exp using (Ctx; Closed; Val; Fn; Exp; Tm; _×ᵗ_; natᵗ; obs; sizeᵗ; applyFn; _≟ᵗ_; evalTm; syncSizeᵉ;
  syncSizeᵗ; syncSizeᵗˢ; syncSizeᵛ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵗˢ; nestDᵛ; nestDᵉ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; foldPath; dispatchShare; stepFrame; shareGo; shareAdmit; shareLatch; RegId;
  NodeId; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeState; scan-st; take-st; takeVals; mergeAll-st;
  switch-st; exhaust-st; lookupNode; setNode; scanVals; innerFinish; aliveThroughᶠ;
  mergeAllDrain; subscribeInner; hasRoom; subscribeE; splitBurst; Stream; mintNode;
  installNode; pushBurst; oneShotBurst; splitEvents)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps using (1≤pow≤; Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?; widLive; widNode; regsSz?; nestValOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (capsOK?-parts)
open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; ≤ᵇ-true; T-to; ≡ᵇ→≡)
open import Verify-Budget-Sufficient.Measures using (pathLen; boundedLive; boundedNode; all-impl; ∧-true; syncSize-unfoldμ)
open import Verify-Budget-Sufficient.Nest-Store using
  (nodeNest; pathNestD; pathNestF; frameNestF; 1≤frameNestF; nest-telescope; nestUnit;
   nest-inflate; pow-grow¹; pow-distrib-*)
open import Verify-Budget-Sufficient.Nest-Subst using (applyFn-nest; evalTm-nest-sync; nestD-unfoldμ)
  renaming (pow-grow to pow-grow-both)
open import Verify-Budget-Sufficient.Nest-Cap using
  (nestB; nestB-mono; nestB-base; nestB-frame; nestFac; 1≤nestFac; nestU; nestU-base; nestB-at)
open import Verify-Budget-Sufficient.Nest-Burst using
  (descW; innerW; drainW; innerW-gs; drainW-here; drainW-tail; descW-take; descW-map; descW-mu)

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

-- AND OVER A ONE-SHOT'S PAYLOADS, where nothing is substituted IN and
-- the charge is read off the terms alone.  The list combines by `⊔`
-- while its sync size combines by `+`, so one exponent covers every
-- element.
abstract
  ofVals-nest-sync : ∀ {n} {Γ : Ctx n} {u}
    (ts : List (Tm Γ [] [] [] u)) →
    nestDᵛˢ (map (λ tm → evalTm tm) ts) ≤ 2 ^ syncSizeᵗˢ ts * nestDᵗˢ ts
  ofVals-nest-sync []       = z≤n
  ofVals-nest-sync (y ∷ ys) =
    ⊔-lub (≤-trans (evalTm-nest-sync y)
                   (pow-grow-both (syncSizeᵗ y) (syncSizeᵗ y + syncSizeᵗˢ ys) _ _
                     (m≤m+n (syncSizeᵗ y) (syncSizeᵗˢ ys))
                     (m≤m⊔n (nestDᵗ y) (nestDᵗˢ ys))))
          (≤-trans (ofVals-nest-sync ys)
                   (pow-grow-both (syncSizeᵗˢ ys) (syncSizeᵗ y + syncSizeᵗˢ ys) _ _
                     (m≤n+m (syncSizeᵗˢ ys) (syncSizeᵗ y))
                     (m≤n⊔m (nestDᵗ y) (nestDᵗˢ ys))))

-- AND WHAT A ONE-SHOT'S BURST SPLITS TO IS ITS PAYLOAD LIST, VERBATIM.
-- The `init`, the `close` and the `complete` are bookkeeping, so the
-- value side of the split is exactly what went in -- which is what lets
-- the head above read its conclusion off the terms rather than off the
-- stream.
abstract
  splitEvents-vals : ∀ {n} {Γ : Ctx n} {u} {A : Set}
    (vals : List (Val Γ u)) (es : List (InstEvent (Val Γ u))) →
    proj₁ (splitEvents {A = A} (map value vals ++ es))
      ≡ vals ++ proj₁ (splitEvents {A = A} es)
  splitEvents-vals []         es = refl
  splitEvents-vals (v ∷ vals) es = cong (v ∷_) (splitEvents-vals vals es)

  oneShot-vals : ∀ {n} {Γ : Ctx n} {u} {A : Set}
    (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) →
    proj₁ (splitBurst {A = A} (proj₁ (oneShotBurst vals id sched))) ≡ vals
  oneShot-vals vals id sched =
    trans (cong (_++ []) (splitEvents-vals vals _))
          (trans (cong (_++ []) (++-identityʳ vals)) (++-identityʳ vals))

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

-- ONE NODE'S NESTING, ZERO WHERE THE TABLE HAS NO SUCH NODE.  The
-- maximum over the table is the honest bound for a walk that may write
-- anywhere; it is a gross over-reading for a frame that reads exactly
-- ONE accumulator, and that gap is what would put an incoming store
-- inside a bound whose whole job is to mention none.
nodeNestAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → NodeId → EvalSt e → ℕ
nodeNestAt nid st = maybe nodeNest 0 (lookupNode nid (EvalSt.nodes st))

abstract
  -- a write moves any one reading by at most what was written,
  -- which is `setNode-nodes` at a point
  lookupNode-set-at : ∀ {n} {Γ : Ctx n} (j nid : NodeId) (ns : NodeState Γ)
    (nodes : List (NodeId × NodeState Γ)) →
    maybe nodeNest 0 (lookupNode j (setNode nid ns nodes))
      ≤ nodeNest ns ⊔ maybe nodeNest 0 (lookupNode j nodes)
  lookupNode-set-at j nid ns [] with nid ≡ᵇ j
  ... | true  = m≤m⊔n _ _
  ... | false = z≤n
  lookupNode-set-at j nid ns ((k , s′) ∷ r) with k ≡ᵇ nid in eq
  ... | true rewrite ≡ᵇ→≡ k nid eq with nid ≡ᵇ j
  ...   | true  = m≤m⊔n _ _
  ...   | false = m≤n⊔m _ _
  lookupNode-set-at j nid ns ((k , s′) ∷ r) | false
    with k ≡ᵇ j
  ...   | true  = m≤n⊔m _ _
  ...   | false = lookupNode-set-at j nid ns r

  nodeNestAt-set : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (j nid : NodeId) (ns : NodeState Γ) (st : EvalSt e) →
    nodeNestAt j (installNode nid ns st) ≤ nodeNest ns ⊔ nodeNestAt j st
  nodeNestAt-set j nid ns st = lookupNode-set-at j nid ns (EvalSt.nodes st)

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

-- A PREFIX CANNOT BE DEEPER THAN THE LIST, and `takeVals` returns a
-- prefix.  The induction is on the budget rather than the list because
-- that is what `takeVals` recurses on, and its `suc zero` clause drops
-- the whole tail in one step -- which is the clause that would fail were
-- the measure a sum rather than a `⊔`.
abstract
  takeVals-nest : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vals : List (Val Γ s)) →
    nestDᵛˢ (proj₁ (takeVals k vals)) ≤ nestDᵛˢ vals
  takeVals-nest zero          vals     = z≤n
  takeVals-nest (suc k)       []       = z≤n
  takeVals-nest (suc zero)    (v ∷ vs) = ⊔-mono-≤ ≤-refl z≤n
  takeVals-nest (suc (suc k)) (v ∷ vs) = ⊔-mono-≤ ≤-refl (takeVals-nest (suc k) vs)

-- THE ONE FRAME THAT CANNOT DEEPEN ANYTHING, and both halves of the `⊔`
-- say why separately.  `takeVals` forwards a PREFIX of what it was
-- handed, so no value it emits was built here; and the only node it
-- writes is a `take-st`, which is a counter -- `nodeNest` reads it zero,
-- so the table it leaves is bounded by the table it found whichever
-- branch the cut flag takes.  The cutting branch also rewrites the
-- registry and the live list, and neither is anything `nodesMax` reads.
abstract
  stepFrame-nodes-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (nid : NodeId) (p : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (take-f nid) p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ (nodesMax st ⊔ nestDᵛˢ vals)
  stepFrame-nodes-take sf id now nid p vals fin sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing               = ⊔-lub (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) z≤n
  ... | just (scan-st _)      = ⊔-lub (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) z≤n
  ... | just (mergeAll-st _ _ _ _) = ⊔-lub (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) z≤n
  ... | just (switch-st _ _)  = ⊔-lub (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) z≤n
  ... | just (exhaust-st _ _) = ⊔-lub (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) z≤n
  ... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
  ... | true  = ⊔-mono-≤ (setZero zero) (takeVals-nest k vals)
    where
    setZero : ∀ (m : ℕ) →
      nodesFold (setNode nid (take-st m) (EvalSt.nodes st)) ≤ nodesMax st
    setZero m = ≤-trans (setNode-nodes nid (take-st m) (EvalSt.nodes st))
                        (⊔-lub z≤n ≤-refl)
  ... | false = ⊔-mono-≤ (setZero (proj₁ (proj₂ (takeVals k vals))))
                         (takeVals-nest k vals)
    where
    setZero : ∀ (m : ℕ) →
      nodesFold (setNode nid (take-st m) (EvalSt.nodes st)) ≤ nodesMax st
    setZero m = ≤-trans (setNode-nodes nid (take-st m) (EvalSt.nodes st))
                        (⊔-lub z≤n ≤-refl)

-- THE SLOTS TERM IS PAID ONCE PER FRAME AND EVERY FRAME BUT ONE HAS NO
-- USE FOR IT, so it enters as pure slack for four of the five arms.
-- What forces it into the shared statement is the fifth: a `from-inner`
-- charges no wrap at all, so its arm has no term to widen and the
-- summand is the only place a slot's nesting can come from.
abstract
  -- THE FLATTENED FACTOR IS THE ONLY BASE LEFT, and it is the one the
  -- walk above this module carries: a descent charged per level spends a
  -- power of the per-frame factor, and the frame layer receives it
  -- whole.  Neither step needs anything of the base but positivity, so
  -- these are the same proofs with the base named rather than built.
  addN : ∀ (S W X U : ℕ) → nestFac S W * X ≤ nestFac S W * (X + U)
  addN S W X U = *-monoʳ-≤ (nestFac S W) (m≤m+n X U)

  raiseN : ∀ (S W X U : ℕ) → X ≤ nestFac S W * (X + U)
  raiseN S W X U =
    ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ X)))
                     (*-monoˡ-≤ X (1≤nestFac S W)))
            (addN S W X U)

-- THE OUTER WRAP TAKES OBSERVABLES AND SUBSCRIBES THEM, which is why
-- this arm is charged a FACTOR and not a unit.  `pathNestD` charges the
-- frame the `suc` a `*All` layer adds -- exactly right for the LAYER,
-- and silent about what the layer DOES.  `thruWalk` subscribes each
-- observable it is handed, so the values leaving the frame are an
-- inner's emissions, and a subscription SUBSTITUTES: the emitted depth
-- is the argument's depth times the number of times the step function
-- names its payload.  Multiplicative, so no summand is the shape.
--
-- AND THE FACTOR COMES FROM THE CAP BECAUSE THE FRAME CANNOT CARRY IT.
-- A frame holds an op and node ids and no syntax, so no function of it
-- can see what the subscription will substitute; the occurrence count is
-- bounded by two to the substituted function's SIZE.  But `capsOK?`
-- bounds the STATE and the arriving values are not in it, so the cap has
-- to be imposed on them separately -- which is what the `valCaps?`
-- premise does, and why the caps hypothesis alone is not enough.
--
-- AND THE INNER ARM IS THE SAME STATEMENT AT THE OTHER `*All` FRAME.
-- Both re-enter the subscribe machinery and both were charged as though
-- they forwarded, so one repair covers two arms.
--
-- REFUTED: `Refuted.Thru-Subscribe-Nest` kills the per-value form,
--   eighty against forty-one, at a payload forty layers deep; the gap
--   is that depth, so no constant per value closes it.  The same
--   witness kills the ASSEMBLY at this frame, whose charge at the
--   smallest admissible width IS this bound.
-- REFUTED: `Refuted.Thru-Subscribe-Nest` kills the caps-scaled form at
--   the same eighty against forty-one, because `capsOK? (caps 0 0 0)`
--   holds at the state it is asked about -- one ordinary installed node
--   and nothing else -- so the factor is one and the caps premise buys
--   the statement nothing at all.  The same file pins `valCaps?` FALSE
--   at the arriving value, which is the premise that does buy it.
-- REFUTED: `Refuted.Thru-Scan-Burst-Nest` kills the FLAT factor, at a
--   cold scripted slot whose sync list is charged to neither side: the
--   frame's own burst doubles the delivered depth per value while the
--   cap and the incoming state stay fixed, so the crossing arrives at
--   sixteen thousand three hundred and eighty-three against eight
--   thousand one hundred and ninety-two -- one value earlier, the two
--   sides are eight thousand one hundred and ninety-one against the same
--   eight thousand one hundred and ninety-two.  That is why the factor
--   is a power in the OUTPUT burst and the length premise is stated.
-- PROBED: `Probed.Subscribe-Nest` clears the burst-powered form at the
--   same witness and the same tight cap, at the width this statement's
--   own hypotheses pin -- `1 ≤ W`, one value in, one value back.  The
--   crossing is the row that could have failed: eighty delivered
--   against forty-one at a factor of one, which is the first refutation
--   above, and against eighty-two at a factor of two, while the cap the
--   value's size grants is a hundred and seventy-three.  Not covered:
--   the BURST axis -- the frame hands back a single value there, so the
--   second copy of the base is slack, and the refutation directly above
--   is what covers that axis instead.
postulate
  stepFrame-nodes-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (W : ℕ) (sl : Slots Γ)
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (p : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    1 ≤ W → length vals ≤ W → capsOK? c sched st ≡ true →
    all (valCaps? c sl (obs u)) vals ≡ true →
    let r = stepFrame sf id now (thru-outer op nid) p vals fin sched st in
    length (proj₁ r) ≤ W →
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ nestFac (Caps.cSize c) W * ((nodesMax st ⊔ nestDᵛˢ vals) + W)

-- A QUEUE'S NESTING, THE SAME `⊔`-FOLD `nodeNest` READS OFF A PARKED
-- `mergeAll-st`, named so a statement about the drain can say what it
-- was handed without naming the node it came out of.
queueNest : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} → List (Exp Γ Δᵍ Δ Θ u) → ℕ
queueNest = foldr (λ o acc → nestDᵉ o ⊔ acc) 0

-- APPENDING TWO VALUE LISTS IS A `⊔`, which is what makes the drain's
-- concatenation cost nothing: a fold of maxima over a concatenation is
-- the maximum of the two folds.
abstract
  nestDᵛˢ-++ : ∀ {n} {Γ : Ctx n} {u} (xs ys : List (Val Γ u)) →
    nestDᵛˢ (xs ++ ys) ≤ nestDᵛˢ xs ⊔ nestDᵛˢ ys
  nestDᵛˢ-++ []       ys = m≤n⊔m 0 (nestDᵛˢ ys)
  nestDᵛˢ-++ {u = u} (x ∷ xs) ys =
    ≤-trans (⊔-mono-≤ (≤-refl {nestDᵛ u x}) (nestDᵛˢ-++ xs ys))
            (≤-reflexive (sym (⊔-assoc (nestDᵛ u x) (nestDᵛˢ xs) (nestDᵛˢ ys))))

-- THE CAPS PREMISE THIS FACE CARRIES, AND IT IS DELIBERATELY WEAKER
-- THAN THE CAPS FACE'S.  A scan installs the EVALUATED seed, and
-- `boundedNode` reads a scan node at the stored value's SIZE while the
-- premise available at that head bounds the seed's TERM size.
-- Evaluation grows size, so no head can re-establish `capsOK?` for its
-- child at the cap it was entered at, and stepping the cap the way the
-- caps face does is not available here -- the grant is keyed on
-- `cSize`, so a stepped cap is a larger grant and the parent owes the
-- smaller one.
--
-- Exempting the scan node is the repair, and it costs nothing HERE:
-- this face measures DEPTH, and the one place a stored accumulator is
-- read -- the frame-level scan bound -- reads it through
-- `lookupNode-nodes` at its depth, never at its size or its width.
-- What the exemption leaves standing is the flatten queue, which is
-- the conjunct the *All heads actually spend.
--
-- Weakening a HYPOTHESIS strengthens every statement it appears in, so
-- the boundary runs one way only: a caller holding the caps face's own
-- predicate hands it in through `capsOK?⇒nest`, and nothing converts
-- back.
-- REFUTED: `Refuted.Scan-Seed-Caps` is the crossing, at the smallest
--   cap the head's premise admits.
nodeSzᴺ? : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → Bool
nodeSzᴺ? B (scan-st _)                = true
nodeSzᴺ? B (take-st _)                = true
nodeSzᴺ? B (mergeAll-st lim act q od) = boundedNode B (mergeAll-st lim act q od)
nodeSzᴺ? B (switch-st _ _)            = true
nodeSzᴺ? B (exhaust-st _ _)           = true

nodeWidᴺ? : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
nodeWidᴺ? W sl (scan-st _)                = true
nodeWidᴺ? W sl (take-st _)                = true
nodeWidᴺ? W sl (mergeAll-st lim act q od) = widNode W sl (mergeAll-st lim act q od)
nodeWidᴺ? W sl (switch-st _ _)            = true
nodeWidᴺ? W sl (exhaust-st _ _)           = true

nestStB? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → ℕ → Sched Γ → EvalSt e → Bool
nestStB? B sched st =
  all (boundedLive B) (Sched.live sched)
  ∧ all (λ kv → nodeSzᴺ? B (proj₂ kv)) (EvalSt.nodes st)

nestCapsOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → Caps → Sched Γ → EvalSt e → Bool
nestCapsOK? c sched st =
  nestStB? (Caps.cSize c) sched st
  ∧ regsSz? (Caps.cSize c) (EvalSt.registry st)
  ∧ all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched)
  ∧ all (λ kv → nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
        (EvalSt.nodes st)
  ∧ (length (EvalSt.registry st) ≤ᵇ Caps.cReg c)

-- the five conjuncts back out, with their result types pinned so the
-- booleans `∧-true` splits on are determined
nestCapsOK?-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  nestCapsOK? c sched st ≡ true →
    (nestStB? (Caps.cSize c) sched st ≡ true)
  × (regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true)
  × (all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched) ≡ true)
  × (all (λ kv → nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
         (EvalSt.nodes st) ≡ true)
  × ((length (EvalSt.registry st) ≤ᵇ Caps.cReg c) ≡ true)
nestCapsOK?-parts c sched st h with ∧-true _ _ h
... | h0 , r1 with ∧-true _ _ r1
... | h1 , r2 with ∧-true _ _ r2
... | h2 , r3 with ∧-true _ _ r3
... | h3 , h4 = h0 , h1 , h2 , h3 , h4

nodeSzᴺ?-weaken : ∀ {n} {Γ : Ctx n} (B : ℕ) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → nodeSzᴺ? B ns ≡ true
nodeSzᴺ?-weaken B (scan-st _)          h = refl
nodeSzᴺ?-weaken B (take-st _)          h = refl
nodeSzᴺ?-weaken B (mergeAll-st _ _ _ _) h = h
nodeSzᴺ?-weaken B (switch-st _ _)      h = refl
nodeSzᴺ?-weaken B (exhaust-st _ _)     h = refl

nodeWidᴺ?-weaken : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ns : NodeState Γ) →
  widNode W sl ns ≡ true → nodeWidᴺ? W sl ns ≡ true
nodeWidᴺ?-weaken W sl (scan-st _)          h = refl
nodeWidᴺ?-weaken W sl (take-st _)          h = refl
nodeWidᴺ?-weaken W sl (mergeAll-st _ _ _ _) h = h
nodeWidᴺ?-weaken W sl (switch-st _ _)      h = refl
nodeWidᴺ?-weaken W sl (exhaust-st _ _)     h = refl

capsOK?⇒nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → nestCapsOK? c sched st ≡ true
capsOK?⇒nest c sched st h =
    ∧-intro (∧-intro (proj₁ hL)
                     (all-impl _ _
                        (λ kv → nodeSzᴺ?-weaken (Caps.cSize c) (proj₂ kv))
                        (EvalSt.nodes st) (proj₂ hL)))
    (∧-intro h1
    (∧-intro h2
    (∧-intro (all-impl _ _
                (λ kv → nodeWidᴺ?-weaken (Caps.cWid c) (Sched.slots sched)
                          (proj₂ kv))
                (EvalSt.nodes st) h3)
             h4)))
  where
  P  = capsOK?-parts c sched st h
  h0 = proj₁ P
  hL = ∧-true _ _ h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- minting an instance id touches the node counter and nothing this
-- predicate reads
nestCapsOK?-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (k : NodeId) (sched : Sched Γ) (st : EvalSt e) →
  nestCapsOK? c sched st ≡ true →
  nestCapsOK? c (record sched { nextNode = k }) st ≡ true
nestCapsOK?-nextNode c k sched st h = h

setNode-nodeSzᴺ? : ∀ {n} {Γ : Ctx n} (B : ℕ)
  (nid : NodeId) (ns : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
  nodeSzᴺ? B ns ≡ true →
  all (λ kv → nodeSzᴺ? B (proj₂ kv)) nodes ≡ true →
  all (λ kv → nodeSzᴺ? B (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-nodeSzᴺ? B nid ns []             bn h = ∧-intro bn refl
setNode-nodeSzᴺ? B nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (∧-trueʳ h)
... | false = ∧-intro (∧-trueˡ h) (setNode-nodeSzᴺ? B nid ns r bn (∧-trueʳ h))

setNode-nodeWidᴺ? : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ)
  (nid : NodeId) (ns : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
  nodeWidᴺ? W sl ns ≡ true →
  all (λ kv → nodeWidᴺ? W sl (proj₂ kv)) nodes ≡ true →
  all (λ kv → nodeWidᴺ? W sl (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-nodeWidᴺ? W sl nid ns []             bn h = ∧-intro bn refl
setNode-nodeWidᴺ? W sl nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (∧-trueʳ h)
... | false = ∧-intro (∧-trueˡ h)
                      (setNode-nodeWidᴺ? W sl nid ns r bn (∧-trueʳ h))

nestCapsOK?-setNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  nodeSzᴺ? (Caps.cSize c) ns ≡ true →
  nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  nestCapsOK? c sched st ≡ true →
  nestCapsOK? c sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) ≡ true
nestCapsOK?-setNode c nid ns sched st bn wn inv =
    ∧-intro (∧-intro (proj₁ hL)
                     (setNode-nodeSzᴺ? (Caps.cSize c) nid ns (EvalSt.nodes st) bn
                        (proj₂ hL)))
    (∧-intro h1
    (∧-intro h2
    (∧-intro (setNode-nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) nid ns
                (EvalSt.nodes st) wn h3)
             h4)))
  where
  P  = nestCapsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true _ _ h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))


-- AND THE CAPS THE DRAIN SPENDS, HANDED AT EVERY STATE IT PASSES
-- THROUGH, for the reason `capsWalkOK` is shaped that way one face over:
-- a subscription installs nodes the caps did not previously have to
-- cover, so the bundle is not preserved at a fixed `c` and re-deriving
-- the caps face's frame counter in a second currency is the alternative
-- nobody wants.  Recursion on the QUEUE is what lets the drain's own
-- induction take its hypothesis apart.
capsDrainOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) → Set
capsDrainOK c sl sf allNid κ id now lim act [] sched st =
  (Sched.slots sched ≡ sl) × (nestCapsOK? c sched st ≡ true)
capsDrainOK {s = s} c sl sf allNid κ id now lim act (o ∷ q) sched st =
  (Sched.slots sched ≡ sl) × (nestCapsOK? c sched st ≡ true)
  × (nestValOK? c (obs s) o ≡ true)
  × capsDrainOK c sl sf allNid κ id now lim
      (if proj₁ (proj₂ (proj₂ (proj₂ r))) then act else suc act) q
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
  where r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st

-- THE SUBSCRIPTION'S OWN DESCENT, AND IT IS NOW A CASE SPLIT.  What was
-- one postulate over the whole of `subscribeE` is a real body over one
-- leaf per head, so a leaf's FIT is tested the moment it is proven and
-- the three heads that cost nothing -- an empty source, a dry unfold, a
-- `deferᵉ` whose only node is an empty queue -- are proven here rather
-- than assumed alongside the rest.
--
-- THE FACTOR IS KEYED ON THE BURST THE DESCENT HANDS BACK, WHICH IS
-- WHAT SPENDING IT ONCE GETS WRONG.  A subscribe frame can deliver a
-- whole burst, and a `scanᵉ` refolds its accumulator once per value of
-- one, so the demand is a factor per VALUE against a grant read off
-- syntax no burst enlarges.  So the exponent is the emitted burst's
-- length and one copy for the descent itself, and the length enters as
-- a premise -- the frame face's own idiom, where a step's charge is
-- already a power in the width it was handed rather than a constant.
--
-- AND THE STORE IS CARRIED BY A JOIN RATHER THAN MULTIPLIED INTO.
-- What a subscription installs is read off the expression, whose depth
-- `B` bounds, and off the slots, which the unit covers -- so the store
-- the caller handed in reappears under a `⊔` beside a grant that
-- mentions it nowhere.  That is what stops the factor compounding once
-- per queued inner: independent inners write independent nodes and
-- combine by max, while a grant multiplied into the store would raise
-- the drain to a tower in the queue's length.

-- THE FILTER'S AND THE SUBSTITUTING HEAD'S CAPS INVERSION, which is the
-- one premise of the shared statement that does not simply transfer.
-- Either wrapper is one node bigger than its source, so the cap survives
-- being narrowed to the source -- and the descent below needs it there,
-- since that is what it subscribes.
abstract
  nestValOK?-size : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
    (o : Closed Γ u) →
    nestValOK? c (obs u) o ≡ true → syncSizeᵉ o ≤ Caps.cSize c
  nestValOK?-size c o h = ≤ᵇ⇒≤ _ _ (T-to h)

  nestValOK?-map : ∀ {n} {Γ : Ctx n} {s u} (c : Caps)
    (f : Fn Γ [] [] [] s u) (b : Closed Γ s) →
    nestValOK? c (obs u) (mapᵉ f b) ≡ true →
    nestValOK? c (obs s) b ≡ true
  nestValOK?-map {s = s} c f b h =
    ≤ᵇ-true (syncSizeᵛ (obs s) b) (Caps.cSize c)
      (≤-trans (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f)) (n≤1+n _))
               (≤ᵇ⇒≤ _ _ (T-to h)))

  nestValOK?-take : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
    (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) →
    nestValOK? c (obs u) (takeᵉ cnt b) ≡ true →
    nestValOK? c (obs u) b ≡ true
  nestValOK?-take {u = u} c cnt b h =
    ≤ᵇ-true (syncSizeᵛ (obs u) b) (Caps.cSize c)
      (≤-trans (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ cnt)) (n≤1+n _))
               (≤ᵇ⇒≤ _ _ (T-to h)))

-- AND THE FILTER FRAME'S PUSH, WHICH MUST BE FREE.  A `take-f` writes a
-- decremented counter and forwards or drops, so it neither substitutes
-- into a value nor stores one -- the node's own nesting is zero and no
-- value leaves deeper than it arrived.  Stated as two
-- separate facts because that is what the head above spends: the values
-- are a prefix of what arrived and the table is the table that arrived,
-- and neither half is bounded by the other.
--
-- TWIN: `pushBurst-caps` is this induction walked -- the same fold over
--   the same emit list, threading the same evolving state and spending
--   a per-emit frame lemma at each step -- on the caps face, where it
--   is proven and carries an index the nest face does not need.
-- TWIN: `stepFrame-nodes-take` is the per-emit half, proven, and it
--   already says exactly what one filter frame costs: nothing.
postulate
  pushBurst-nest-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
    (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    let r = pushBurst g id now (take-f nid) κ str sched st in
    (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r)))
       ≤ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} str)))
    × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st)
    × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st)

-- AND THE SUBSTITUTING FRAME'S PUSH, WHICH IS WHERE THE FACTOR COMES
-- FROM.  A `map-f` applies its function to every value going past and
-- writes nothing, so the table is untouched and the values grow by
-- exactly one substitution -- the per-emit cost `mapVals-nest` already
-- charges, lifted across the fold.  The two halves are separate facts
-- for the same reason the filter frame's are: neither bounds the other.
--
-- REFUTED: `Refuted.Inner-Drain-Nest` kills the free form, eighty
--   against forty, at a queued `mapᵉ` whose step function names its
--   payload on both sides of the sum: `nestDᵉ` is additive there and
--   the substitution is not, so the emitted value is deeper than the
--   whole queue is charged.
-- REFUTED: `Refuted.Inner-Drain-Nest` also kills the repair this most
--   invites -- charging the arm the `nestUnit e sl` its own parent
--   already carries -- at a hundred and twenty against eighty-two,
--   with the queued observable AS the program so the unit is as large
--   as the currency admits.  A third occurrence of the payload in the
--   step function moves the emit and leaves the unit where it was, so
--   what is owed is a FACTOR in the substituted function's SIZE and
--   no summand in a depth currency is one.
-- REFUTED: `Refuted.Subscribe-Caps-Nest` kills taking the exponent
--   from the STORE's cap instead, sixteen delivered against a charge
--   of six at `st-init`, where the node table is empty and so
--   `capsOK? (caps 0 0 0)` holds outright and the factor collapses to
--   one.  Each stacked `mapᵉ` naming its payload twice doubles the
--   delivered depth and leaves the charge where it was -- eight, then
--   sixteen -- so the gap is unbounded rather than one crossing.  That
--   is what fixes the exponent here to the FUNCTION's own size.
-- TWIN: `mapVals-nest` is the per-emit half at the full measure,
--   proven, with the fold the same walk `pushBurst-caps` already makes
--   over the same list; the factor's SYNC denomination is the probed
--   re-run of that per-emit induction, not a new shape.
-- PROBED: `Probed.Subscribe-Nest` reaches this leaf through the head
--   above rather than directly -- the head is a real body now, so the
--   only map-specific thing its rows can still be measuring is this
--   factor -- on exactly the family that refuted every earlier form:
--   a stack of `mapᵉ` frames each naming its payload on both sides of
--   a sum, so the delivered depth doubles per layer, read at the
--   SMALLEST cap the `nestValOK?` premise admits.  What it measures
--   rather than asserts is the exponent SPENT: two of the three
--   programs cross, needing one bit and two against the twenty-one to
--   thirty-five the cap grants, and the demand rises by ONE per
--   stacked frame while the size it is read off rises by SEVEN -- so
--   the doubling is outrun with six of every seven bits unspent.  Not
--   covered: the FOLD, since every row hands back exactly one value,
--   pinned rather than assumed; and any cap above the value's own.
-- PROBED: `Probed.Sync-Factor` measures the factor's DENOMINATION --
--   whether the exponent can be read in `syncSizeᵗ` rather than
--   `sizeᵗ` -- at the duplicating family of `Refuted.Apply-Fn-Nest`
--   plus the rows that split the two currencies: the same duplication
--   under a `deferᵉ` gate contributes ZERO to the output's nesting,
--   pinned as an equality, and a mixed function prices exactly its
--   visible copy.  So substitution does not relocate content across a
--   defer gate on any row, and the sync-denominated bound holds where
--   the currencies disagree.  Not covered: `evalTm` at a closed seed,
--   and stacked substitutions, which the receipt above reaches only in
--   the full-size denomination.
postulate
  pushBurst-nest-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ u t) (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    let r = pushBurst g id now (map-f fn) κ str sched st in
    (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r)))
       ≤ 2 ^ syncSizeᵗ fn
         * (nestDᵗ fn + nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} str))))
    × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st)
    × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st)


-- THE STATEMENT, NAMED ONCE.  Every leaf below re-states it at one of
-- `subscribeE`'s heads, so writing the shared shape here is what keeps
-- the leaves comparable and lets the body read as a case split rather
-- than a wall of repeated telescopes.
--
-- AND THE WIDTH PREMISE IS ABOUT THE WHOLE DESCENT, NOT THE OUTPUT.
-- `descW` is the widest burst produced ANYWHERE under one subscribe,
-- which is a strictly stronger hypothesis than a bound on the burst
-- this call hands back and is what four of the five recursive heads
-- would have given for free either way.  The fifth is why it is stated
-- this way: a `take` DROPS, so the inner burst can be longer than the
-- one that leaves, and the induction wants the inner descent at the
-- INNER width while the conclusion is a power in that width.  Keying
-- the premise on the descent makes every head's transfer a projection
-- and costs the caller a measure it can compute.

-- AND THE GRANT SHRINKS WITH THE TERM WHILE THE STORE DOES NOT, WHICH
-- IS WHY THE CONCLUSION SPLITS.  Every head whose frame SUBSTITUTES
-- into the values passing through it -- the fold, the map, and the
-- three that drain a queue -- spends a frame lemma whose factor is a
-- power of the frame's own size, once per level; the filter head is
-- the exception, and the reason its clause closes, a frame that only
-- forwards or drops having factor one.  A grant naming nothing that
-- shrinks down the descent hands the child exactly what the parent
-- owes, leaving the factor nothing to be paid out of -- enlarging it
-- moves both sides together, and the spare `suc` buys one level
-- against a descent as deep as the term is.  So the grant is keyed to
-- `syncSizeᵉ o`, which shrinks at every subterm head exactly as the
-- full size does -- the two spines share every `suc` outside a
-- `deferᵉ` -- and, unlike the full size, is left EXACTLY IN PLACE by a
-- μ-unfolding (`syncSize-unfoldμ`), which is what lets the unfold head
-- descend at a strictly smaller key (`unfoldμ-shrinks`) instead of a
-- larger one.  The currency is honest for the factor too: what a
-- substitution charges is blind to defer-hidden bulk, and
-- `Probed.Sync-Factor` pins the hidden copy at zero.  The store cannot
-- be keyed the same way: a child under a smaller grant would need
-- `nodesMax` below a smaller number than the parent was handed, and
-- the store only grows as the walk proceeds.  Hence the split -- the
-- burst against a bound that shrinks and names no state at all, the
-- store against that bound joined with the store it started from.
--
-- AND THE STORE IS READ TWICE, ONCE COARSELY AND ONCE PER NODE.  The
-- maximum is what a caller wants when it is about to take a maximum
-- itself -- the drain, whose inners combine by join.  It is useless to
-- a head that reads ONE node: a threading frame's output depends on
-- its own accumulator and on nothing else in the table, so bounding
-- that accumulator by the table's maximum imports the incoming store
-- into a conclusion that must name no state.  The pointwise conjunct
-- is the same fact read at the node, and it is state-free exactly
-- where it is spent, because the node in question was minted by the
-- head that reads it.

NestAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Set
NestAt {Γ = Γ} {t = t} {e = e} c sl B W g o κ id now sched st =
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs _) o ≡ true →
  nestDᵉ o ≤ B →
  descW g o κ id now sched st ≤ W →
  let r = subscribeE g o κ id now sched st
      G = nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ o) in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ G)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ G)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st ⊔ G)

postulate
  -- THE SLOT HEADS, where a subscription reads the telescope rather
  -- than descending.  A hot slot emits bookkeeping and no values; a
  -- cold one emits its script, which is charged to the unit and not to
  -- the expression; a shared one connects and re-enters the walk.
  --
  -- REFUTED: `Refuted.Inner-Drain-Share-Nest` kills the caps-scaled
  --   form, forty delivered against a charge of ZERO, at a queue
  --   holding nothing but a reference to an observable-typed share.
  --   `nestDᵉ (input i)` is zero and rightly so -- the syntax of a slot
  --   reference says nothing about the slot -- and the node table does
  --   not read the slots either, so the charged side is empty and every
  --   factor is a multiple of nothing.  What that pins is the shape:
  --   the factor AND a slots summand, each of which is dead on its own.
  subscribeE-nest-slot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (i : Fin n)
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    NestAt c sl B W g (input i) κ id now sched st
  -- THE SCAN HEAD, WHICH IS WHERE THE BURST INDEX IS REALLY BET.  A
  -- scan's step function is written once and applied once per value of
  -- whatever burst arrives, so this is the head whose demand is a
  -- factor PER VALUE and the reason the exponent carries the length
  -- rather than a constant.
  --
  -- AND IT IS THE HEAD THE WEAKENED CAPS PREMISE WAS SHAPED FOR.  This
  -- is the only one that installs an EVALUATED value -- four install
  -- nothing, the filter head a counter `boundedNode` reads as bounded
  -- at every cap, the *All heads their own empty state -- and
  -- `nestCapsOK?` exempts a stored accumulator's size for exactly that
  -- reason, so the head recurses at the cap it was entered at.  The
  -- bound is untouched by any of it: an evaluated seed's DEPTH is what
  -- `evalTm-nest-sync` bounds, and the grant has room for it.
  --
  -- REFUTED: `Refuted.Scan-Burst-Nest` kills the un-indexed form
  --   outright, 16383 delivered against a charge of 12288, and the row
  --   one value shorter still holds -- so it is a crossing and not a
  --   scale error.  The step function names its accumulator in the two
  --   additive slots an inner `scanᵉ` offers, applied once per value of
  --   a burst that comes from a COLD SCRIPT: `sizeᵉ` cannot see a
  --   script and `slotNest` is zero at every scripted slot, so the
  --   burst is charged to neither the exponent nor the base while it
  --   doubles the delivered depth per value.  The same file measures
  --   the burst at fourteen values in ONE subscribe frame against a
  --   `pWᵛ` of one and an `entryCeil` of eight, which is why no wider
  --   reading of the ENTRY cap repairs it either.
  -- DEAD ROUTE: stepping the cap the way the caps face does -- a scan
  --   there reports `frameStep (j + j′)` and charges `j′` -- is dead
  --   HERE and not merely unproven, because the grant is keyed on
  --   `cSize`: a stepped cap is a LARGER key, hence a larger grant, and
  --   the parent owes the smaller one.
  -- PROBED: `Probed.Scan-Burst-Nest` reads that witness against THIS
  --   form, at the same cold script and the same tight size cap --
  --   fourteen values, 16383 delivered, green here and pinned `false`
  --   at index zero in the same file.  What the rows cannot do is
  --   refute it: the demand rises by ONE bit per value of the burst and
  --   the grant by twelve, so once the index IS the burst this family
  --   is carried with eleven bits per value unspent, which is a reading
  --   about the currency rather than a margin.  Not covered: the
  --   family's next crossing needs a script near twenty-six and an
  --   accumulator of some sixty-seven million nodes, so nothing here
  --   moves the index by more than one step.
  subscribeE-nest-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u) (b : Closed Γ s)
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestAt c sl B W g (scanᵉ f z b) κ id now sched st
  -- THE THREE `*All` HEADS, which differ only in the node state they
  -- install and are three statements for that reason alone: a mint, the
  -- outer's own descent, and the burst pushed back through a
  -- `thru-outer` frame, where the wrap re-enters the walk.
  --
  -- PROBED: `Probed.Subscribe-Nest-Wrap` is the first instantiation of
  --   any of the three, at `W = 0` -- the smallest grant the statement
  --   can be read at, so a green row is stronger than the head asks
  --   for -- with the cap at the value's own sync size, `B` at `nestDᵉ`
  --   exactly and the store `st-init`, both premises pinned by `refl`.
  --   Covered: the BURST conjunct, at two nested layers per head, each
  --   descent handing back two values.  NOT covered: the store halves,
  --   which are `0 ≤ _` in every program reachable at `root` from an
  --   empty table -- `nodeNest` is zero by definition on `switch-st`
  --   and `exhaust-st`, and `mergeAll-st` reads its PENDING list, which
  --   an unlimited merge never fills and a limited one over synchronous
  --   inners has drained by the time the descent returns.  So the drain
  --   the risk is named for is not reached here.  And the depth axis
  --   cannot refute: delivered nesting is exactly the layer count while
  --   the grant's base alone is 106 at one layer and grows four times
  --   faster, so the rows are DEGENERATE on the exponent.
  subscribeE-nest-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (lim : Maybe ℕ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestAt c sl B W g (mergeAllᵉ lim b) κ id now sched st
  -- The switch wrap, at its own initial state.
  -- PROBED: `Probed.Subscribe-Nest-Wrap`, whose coverage and its
  --   boundary are stated at `subscribeE-nest-merge` above.
  subscribeE-nest-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestAt c sl B W g (switchAllᵉ b) κ id now sched st
  -- The exhaust wrap, at its own initial state.
  -- PROBED: `Probed.Subscribe-Nest-Wrap`, whose coverage and its
  --   boundary are stated at `subscribeE-nest-merge` above.
  subscribeE-nest-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestAt c sl B W g (exhaustAllᵉ b) κ id now sched st

subscribeE-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  NestAt c sl B W g o κ id now sched st
subscribeE-nest c sl B W g (input i) κ id now sched st =
  subscribeE-nest-slot c sl B W g i κ id now sched st
subscribeE-nest {Γ = Γ} {t = t} {e = e} {u = u} c sl B W g (ofᵉ ts) κ id now sched st
  hsl hc hv hn hw =
  ≤-trans (≤-reflexive (cong (nestDᵛˢ {u = u})
             (oneShot-vals {A = Val Γ t} (map (λ tm → evalTm tm) ts) id sched)))
    (≤-trans (≤-trans (ofVals-nest-sync ts) (*-monoʳ-≤ (2 ^ syncSizeᵗˢ ts) hn))
      (≤-trans (*-monoʳ-≤ (2 ^ syncSizeᵗˢ ts)
                  (m≤m+n B (nestB (Caps.cSize c) W (nestUnit e sl) B 0)))
               (nestB-frame (Caps.cSize c) W (nestUnit e sl) B
                  0 (syncSizeᵗˢ ts) (syncSizeᵉ (ofᵉ ts))
                  (nestValOK?-size c (ofᵉ ts) hv) (s≤s z≤n))))
  , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest c sl B W g emptyᵉ κ id now sched st hsl hc hv hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest {e = e} c sl B W g (mapᵉ f b) κ id now sched st hsl hc hv hn hw =
  ≤-trans (proj₁ push)
    (≤-trans (*-monoʳ-≤ (2 ^ syncSizeᵗ f) (+-mono-≤ hfB (proj₁ IH)))
             (nestB-frame (Caps.cSize c) W (nestUnit e sl) B
                (syncSizeᵉ b) (syncSizeᵗ f) (syncSizeᵉ (mapᵉ f b)) hk hm))
  , ≤-trans (proj₁ (proj₂ push))
      (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow))
  , (λ j → ≤-trans (proj₂ (proj₂ push) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow)))
  where
  res = subscribeE g b (map-f f ↠ κ) id now sched st

  push = pushBurst-nest-map g id now f κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH = subscribeE-nest c sl B W g b (map-f f ↠ κ) id now sched st
         hsl hc (nestValOK?-map c f b hv)
         (≤-trans (m≤n+m (nestDᵉ b) (nestDᵗ f)) hn)
         (≤-trans (descW-map g f b κ id now sched st) hw)

  -- the function's own nesting is one summand of the head's, so the
  -- base the frame lemma adds is already paid for by the depth premise
  hfB : nestDᵗ f ≤ B
  hfB = ≤-trans (m≤m+n (nestDᵗ f) (nestDᵉ b)) hn

  -- and the frame is a strict subterm of the head, which is the level
  -- of the key this substitution spends
  hk : suc (syncSizeᵗ f) ≤ Caps.cSize c
  hk = ≤-trans (s≤s (m≤m+n (syncSizeᵗ f) (syncSizeᵉ b)))
               (nestValOK?-size c (mapᵉ f b) hv)

  hm : suc (syncSizeᵉ b) ≤ syncSizeᵉ (mapᵉ f b)
  hm = s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f))

  grow : nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ (mapᵉ f b))
  grow = nestB-mono (Caps.cSize c) W (nestUnit e sl) B
           (≤-trans (n≤1+n (syncSizeᵉ b)) hm)
subscribeE-nest {e = e} c sl B W g (takeᵉ cnt b) κ id now sched st hsl hc hv hn hw
  with evalTm cnt in eqc
... | zero  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
... | suc k =
  ≤-trans (proj₁ push) (≤-trans (proj₁ IH) grow)
  , ≤-trans (proj₁ (proj₂ push))
      (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ≤-trans (proj₂ (proj₂ push) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  res    = subscribeE g b (take-f nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (take-st (suc k)) sched₀ st refl refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  push = pushBurst-nest-take g id now nid κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH = subscribeE-nest c sl B W g b (take-f nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-take c cnt b hv) hn
         (≤-trans (descW-take g cnt b κ id now sched st k eqc) hw)

  -- the counter this head installs reads zero, so the table the child
  -- descends from is the table this head was handed
  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (take-st (suc k)) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (take-st (suc k)) st)
                    (⊔-lub z≤n ≤-refl)

  -- and a filter is bigger than what it filters, which is the whole of
  -- what this head spends to lift the child's grant to its own
  grow : nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ (takeᵉ cnt b))
  grow = nestB-mono (Caps.cSize c) W (nestUnit e sl) B
           (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ cnt)) (n≤1+n _))
subscribeE-nest c sl B W g (scanᵉ f z b) κ id now sched st =
  subscribeE-nest-scan c sl B W g f z b κ id now sched st
subscribeE-nest c sl B W g (mergeAllᵉ lim b) κ id now sched st =
  subscribeE-nest-merge c sl B W g lim b κ id now sched st
subscribeE-nest c sl B W g (switchAllᵉ b) κ id now sched st =
  subscribeE-nest-switch c sl B W g b κ id now sched st
subscribeE-nest c sl B W g (exhaustAllᵉ b) κ id now sched st =
  subscribeE-nest-exhaust c sl B W g b κ id now sched st
subscribeE-nest c sl B W g0 (μᵉ body) κ id now sched st hsl hc hv hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest {e = e} c sl B W (gs fuel) (μᵉ body) κ id now sched st hsl hc hv hn hw =
  ≤-trans (proj₁ IH) grow
  , ≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow)
  , (λ j → ≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow))
  where
  -- the evaluator spends one gas AT the μ and subscribes the unfolding,
  -- so the recursive call is the same subscription and the whole clause
  -- is the three premises re-established across the substitution
  IH = subscribeE-nest c sl B W fuel (unfoldμ body) κ id now sched st hsl hc
         (≤ᵇ-true (syncSizeᵉ (unfoldμ body)) (Caps.cSize c)
           (≤-trans (≤-reflexive (syncSize-unfoldμ body))
             (≤-trans (n≤1+n (syncSizeᵉ body))
                      (nestValOK?-size c (μᵉ body) hv))))
         (≤-trans (≤-reflexive (nestD-unfoldμ body)) hn)
         (≤-trans (descW-mu fuel body κ id now sched st) hw)

  -- and the grant widens by the μ node the unfolding drops, which is
  -- the ONE thing this head spends: the sync spine is what the key is
  -- read on, and the unfolding leaves it exactly where it was
  grow : nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ (unfoldμ body))
           ≤ nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ (μᵉ body))
  grow = nestB-mono (Caps.cSize c) W (nestUnit e sl) B
           (≤-trans (≤-reflexive (syncSize-unfoldμ body)) (n≤1+n _))
subscribeE-nest c sl B W g (varᵉ ()) κ id now sched st
subscribeE-nest c sl B W g (deferᵉ body) κ id now sched st hsl hc hv hn hw =
  z≤n
  , ≤-trans (setNode-nodes _ _ (EvalSt.nodes st)) (⊔-lub z≤n (m≤m⊔n _ _))
  , (λ j → ≤-trans (nodeNestAt-set j _ _ st) (⊔-lub z≤n (m≤m⊔n _ _)))

-- ONE SUBSCRIPTION, AND THE BOUND IS ABSOLUTE.  What the subscription
-- installs is read off `o`, whose depth the drain bounds by `B`, and off
-- the slots, which the unit covers -- so re-establishing the same bound
-- rather than one relative to the store handed in is exactly what stops
-- the factor compounding once per queued inner.  A relative form would
-- read `2 ^ cSize` times the PREVIOUS store and raise the drain's cost to
-- a tower in the queue's length, which is not what a queue of independent
-- inners costs.
subscribeInner-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs s) o ≡ true →
  nestDᵉ o ≤ B →
  innerW sf allNid κ id now o sched st ≤ W →
  let r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
      G = nestB (Caps.cSize c) W (nestUnit e sl) B (Caps.cSize c) in
  (nestDᵛˢ (proj₁ (proj₂ r)) ≤ G)
  × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ G)
  × (∀ (j : NodeId) →
       nodeNestAt j (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodeNestAt j st ⊔ G)
subscribeInner-nest c sl B W g0 allNid κ id now o sched st hsl hc hv hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeInner-nest {e = e} c sl B W (gs fuel) allNid κ id now o sched st hsl hc hv hn hw =
  ≤-trans (proj₁ IH) grow
  , ≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow)
  , (λ j → ≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow))
  where
  IH = subscribeE-nest c sl B W fuel o
         (from-inner mergeAllᵒ allNid (Sched.nextNode sched) ↠ κ) id now
         (record sched { nextNode = suc (Sched.nextNode sched) }) st hsl
         (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc) hv hn
         (≤-trans (innerW-gs fuel allNid κ id now o sched st) hw)

  -- the cap is what flattens the descent's own index here: an inner the
  -- caps premise admits is no larger than the cap, so the queue below
  -- can be walked at ONE exponent instead of one per element
  grow : nestB (Caps.cSize c) W (nestUnit e sl) B (syncSizeᵉ o)
           ≤ nestB (Caps.cSize c) W (nestUnit e sl) B (Caps.cSize c)
  grow = nestB-mono (Caps.cSize c) W (nestUnit e sl) B (nestValOK?-size c o hv)

-- THE DRAIN IS A WALK OVER THE QUEUE, and it costs what ONE subscription
-- costs.  `mergeAllDrain` recurses across the parked inners and
-- CONCATENATES, and both measures in the conclusion are `⊔`-folds, so the
-- queue combines by max and not by product -- which is why the bound
-- above can be re-established at every step instead of accumulating.
--
-- AND THE RESIDUAL QUEUE IS IN THE CONCLUSION, which is not decoration:
-- what the drain leaves parked is written straight back into the node
-- table by the frame above, so a bound that covers the emitted values
-- and the state but not the leftovers does not bound the table the
-- caller ends up with.
mergeAllDrain-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  capsDrainOK c sl sf allNid κ id now lim act q sched st →
  queueNest q ≤ B →
  drainW sf allNid κ id now q sched st ≤ W →
  let r = mergeAllDrain sf allNid κ id now lim act q sched st
      G = nestB (Caps.cSize c) W (nestUnit e sl) B (Caps.cSize c) in
  (nestDᵛˢ (proj₁ r) ≤ G)
  × ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
        ⊔ queueNest (proj₁ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ G)
mergeAllDrain-nest {e = e} c sl B W sf allNid κ id now lim act [] sched st hcd hq hw =
  z≤n , ⊔-lub (m≤m⊔n _ _) z≤n
mergeAllDrain-nest {e = e} c sl B W sf allNid κ id now lim act (o ∷ q) sched st hcd hq hw
  with hasRoom lim act
... | false =
  z≤n
  , ⊔-mono-≤ (≤-refl {nodesMax st})
             (≤-trans hq (nestB-base (Caps.cSize c) W (nestUnit e sl) B (Caps.cSize c)))
... | true  =
  ≤-trans (nestDᵛˢ-++ vs vs′) (⊔-lub (proj₁ SUB) (proj₁ IH))
  , ≤-trans (proj₂ IH) (⊔-lub (proj₁ (proj₂ SUB)) (m≤n⊔m (nodesMax st) _))
  where
  r₁    = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  vs    = proj₁ (proj₂ r₁)
  done  = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

  r₂    = mergeAllDrain sf allNid κ id now lim (if done then act else suc act) q sched₁ st₁
  vs′   = proj₁ r₂

  -- THE WIDTH SPLITS THE WAY THE QUEUE DOES, which is what lets ONE `W`
  -- serve the whole walk: `drainW` is a `⊔` over the queued inners at
  -- the states they are actually subscribed at, so the head's own
  -- descent and the tail's whole drain are each under the total and
  -- neither leg needs a width of its own.
  splitW : innerW sf allNid κ id now o sched st ≤ W
  splitW = ≤-trans (drainW-here sf allNid κ id now o q sched st) hw

  splitW′ : drainW sf allNid κ id now q sched₁ st₁ ≤ W
  splitW′ = ≤-trans (drainW-tail sf allNid κ id now o q sched st) hw

  SUB = subscribeInner-nest c sl B W sf allNid κ id now o sched st
          (proj₁ hcd) (proj₁ (proj₂ hcd)) (proj₁ (proj₂ (proj₂ hcd)))
          (≤-trans (m≤m⊔n (nestDᵉ o) (queueNest q)) hq) splitW

  IH = mergeAllDrain-nest c sl B W sf allNid κ id now lim
         (if done then act else suc act) q sched₁ st₁
         (proj₂ (proj₂ (proj₂ hcd)))
         (≤-trans (m≤n⊔m (nestDᵉ o) (queueNest q)) hq)
         splitW′

-- THE FINISH DISPATCH, AND ALL OF IT IS CHECKED.  `innerReact` reaches
-- here along exactly one route -- a `fin` whose inner is not held open
-- by a live registration -- so the frame's whole charge is this
-- statement's; and of the finish's own arms, every one but the
-- `mergeAllᵒ` drain either hands its inputs straight back or writes a
-- node whose `nodeNest` is zero, so the drain is the sole leaf and the
-- rest reduces.
innerFinish-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (sf : Gas) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (id : Id) (now : Tick)
  (vals : List (Val Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     drainW sf allNid p id now q sched st ≤ W) →
  let r = innerFinish sf op allNid inst p id now vals sched st
            (lookupNode allNid (EvalSt.nodes st)) in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ nestFac (Caps.cSize c) W * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))

innerFinish-nest {e = e} c sl W sf switchᵒ allNid inst p id now vals sched st hsl hc hdr hw
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)           = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)           = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st _ _ _ _) = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ _)      = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st nothing _) = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st (just c₀) od) with c₀ ≡ᵇ inst
...   | false = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
...   | true  =
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (switch-st nothing od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl)))

innerFinish-nest {e = e} c sl W sf exhaustᵒ allNid inst p id now vals sched st hsl hc hdr hw
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)           = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)           = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st _ _ _ _) = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st _ _)       = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ od)     =
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (exhaust-st false od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl)))

innerFinish-nest {e = e} {s = s} c sl W sf mergeAllᵒ allNid inst p id now vals sched st hsl hc hdr hw
  with lookupNode allNid (EvalSt.nodes st) in eq
... | nothing                = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)       = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)       = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st _ _)   = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ _)  = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
...   | yes refl =
  ⊔-lub (≤-trans (setNode-nodes allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′))
                 (≤-trans (⊔-lub (m≤n⊔m (nodesMax st′) (queueNest q′))
                                 (m≤m⊔n (nodesMax st′) (queueNest q′)))
                          drain≤))
        (≤-trans (nestDᵛˢ-++ vals vs)
                 (⊔-lub vals≤ (≤-trans (proj₁ DR) G≤)))
  where
  r   = mergeAllDrain sf allNid p id now lim (pred act) q sched st
  vs   = proj₁ r
  act′ = proj₁ (proj₂ (proj₂ r))
  q′   = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st′  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))

  qbnd : queueNest q ≤ nodesMax st
  qbnd = lookupNode-nodes allNid (mergeAll-st lim act q od) (EvalSt.nodes st) eq

  -- the drain's own width is what the caller pinned, at the queue the
  -- node table actually holds -- which is why the premise is quantified
  -- over that queue the way the caps bundle beside it already is
  dw : drainW sf allNid p id now q sched st ≤ W
  dw = hw lim act q od refl

  DR = mergeAllDrain-nest c sl (nodesMax st) W sf allNid p id now lim (pred act) q sched st
         (hdr lim act q od refl) qbnd dw

  base : (nodesMax st ⊔ nestDᵛˢ vals)
           ≤ nestFac (Caps.cSize c) W
               * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))
  base = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals)
                (nestU (Caps.cSize c) (nestUnit e sl))

  vals≤ = ≤-trans (m≤n⊔m (nodesMax st) (nestDᵛˢ vals)) base

  -- the drain hands up its grant at the SIZE cap, which is exactly
  -- where the flattened factor is definitionally what this face spends
  G≤ : nestB (Caps.cSize c) W (nestUnit e sl) (nodesMax st) (Caps.cSize c)
         ≤ nestFac (Caps.cSize c) W
             * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))
  G≤ = ≤-trans (nestB-at (Caps.cSize c) W (nestUnit e sl) (nodesMax st))
               (*-monoʳ-≤ (nestFac (Caps.cSize c) W)
                  (+-monoˡ-≤ (nestU (Caps.cSize c) (nestUnit e sl))
                             (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))))

  drain≤ = ≤-trans (proj₂ DR)
             (⊔-lub (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) base) G≤)

-- THE INNER RELEASE IS NOT A FREE FRAME, and the reason is structural
-- rather than arithmetic.  A `from-inner` at `fin` with no live
-- registration is exactly where `innerFinish` runs `mergeAllDrain`, and
-- the drain SUBSCRIBES a queued inner -- so the values leaving this
-- frame were produced by a subscription, not forwarded by a step.  The
-- arm is the subscribe face's descent arriving inside the walk, which
-- is why it cannot be paid by what the inner already was.
--
-- WHY THE CHARGE IS A PREMISE AND NOT A MEASURE.  A `from-inner`
-- carries an op and two node ids and no syntax, while the queue it
-- drains lives in the STATE -- so `frameNestF` cannot see what the
-- drain will substitute, however it is redefined.  The caps face never
-- had the gap: `frame-room` opens an allowance at BOTH boundaries that
-- traverse a payload list, the thru-outer over its value list and the
-- from-inner over the mergeAll queue, and only the nesting currency
-- read the second one as free.  So the factor arrives as `capsOK?`,
-- which bounds the size of every queued observable, and the arm is
-- charged two to that size -- the ceiling on how many times a step
-- function can name what it is substituting into.
--
-- WHAT INSTANTIATION CAN AND CANNOT SETTLE HERE, decided before any
-- sweep because the answer is readable off the types.  The emitted
-- depth is LINEAR in how many times the step function names its
-- payload, that count is at most the function's size, and the charge is
-- TWO to the size cap -- so the two sides are separated by an
-- exponential, and no program can cross it.  A sweep over
-- payload depth, occurrence count or queue length is unfalsifiable by
-- construction, however tight its rows read.
--
-- SO THE FACTOR'S OWN RISK IS STRUCTURAL AND IT IS NAMED: whether one
-- frame's drain can emit deeper than the factor times what it was
-- handed.  It cannot do so by COMPOUNDING -- `mergeAllDrain` recurses
-- across the queue and concatenates, and both measures in the
-- conclusion are `⊔`-folds, so the queue combines by max and not by
-- product -- which leaves the single subscription as the whole
-- question.  `applyFn-nest` (.Nest-Subst) is that question answered for
-- ONE substitution, at this exact factor and proven; what is owed is
-- that bound lifted through the descent the drain performs.
--
-- THE FRAME'S DISPATCH, AND IT IS CHECKED: the two routes that hand
-- their inputs straight back -- a step that is not a `fin`, and a
-- `fin` whose inner is still held open by a live registration -- are
-- discharged here, so what remains asserted is the finish alone.
stepFrame-nodes-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     drainW sf allNid p id now q sched st ≤ W) →
  let r = stepFrame sf id now (from-inner op allNid inst) p vals fin sched st in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ nestFac (Caps.cSize c) W * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))
stepFrame-nodes-inner {e = e} c sl W sf id now op allNid inst p vals false sched st hsl hc hdr hw =
  raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
stepFrame-nodes-inner {e = e} c sl W sf id now op allNid inst p vals true sched st hsl hc hdr hw
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | false = innerFinish-nest c sl W sf op allNid inst p id now vals sched st hsl hc hdr hw

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

-- THE DRAIN'S CAPS, HANDED AT THE ONE FRAME THAT CAN REACH IT.  Only a
-- `from-inner` runs `mergeAllDrain`, and only when the node it names is
-- a `mergeAll-st` -- so the obligation is stated as a function of the
-- lookup rather than of the frame, and every other frame carries
-- nothing.  Quantifying over the queue instead of reading it out is
-- what keeps this a plain premise a caller can discharge without
-- inspecting the table.
frameDrainOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (sl : Slots Γ) (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → Set
frameDrainOK c sl sf id now (map-f _)        p sched st = ⊤
frameDrainOK c sl sf id now (scan-f _ _)     p sched st = ⊤
frameDrainOK c sl sf id now (take-f _)       p sched st = ⊤
frameDrainOK c sl sf id now (thru-outer _ _) p sched st = ⊤
frameDrainOK {Γ = Γ} {u = u} c sl sf id now (from-inner op allNid inst) p sched st =
  ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    capsDrainOK c sl sf allNid p id now lim (pred act) q sched st

-- AND THE DRAIN'S WIDTH, CARRIED THE SAME WAY AND AT THE SAME ONE
-- FRAME.  It is a second predicate rather than a conjunct of the one
-- above because the two say different things about the same queue --
-- what the inners may reference, and how wide their descents may run --
-- and a site that wants either would otherwise have to take the pair
-- apart.
frameDrainW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (W : ℕ) (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) → Set
frameDrainW W sf id now (map-f _)        p sched st = ⊤
frameDrainW W sf id now (scan-f _ _)     p sched st = ⊤
frameDrainW W sf id now (take-f _)       p sched st = ⊤
frameDrainW W sf id now (thru-outer _ _) p sched st = ⊤
frameDrainW {Γ = Γ} {u = u} W sf id now (from-inner op allNid inst) p sched st =
  ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    drainW sf allNid p id now q sched st ≤ W

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
-- the walk again through an inner.  `frameNestF` charges the two that
-- SUBSTITUTE and reads the other three as one, which holds for take and
-- cannot hold at either *All arm -- a frame carries no syntax and the
-- subscribe machinery substitutes, so those two are paid instead by a
-- factor in the store's own size cap, uniform across all five arms and
-- spent by only two of them.  Their own headers carry why.
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
-- REFUTED: `Refuted.Inner-Drain-Nest` kills the caps-free form at the
--   from-inner frame, eighty against forty, where the charge reduces to
--   the state it started from and the drain under it subscribes.
-- REFUTED: `Refuted.Thru-Subscribe-Nest` kills it at the thru-outer
--   frame, eighty against forty-one, where the unit per value is spent
--   on a wrap and the values are an inner's emissions -- and kills the
--   caps-scaled repair at the same figures, the cap being satisfied by
--   a state the arriving values are no part of.
abstract
  stepFrame-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (W : ℕ) (sl : Slots Γ) (sf : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    1 ≤ W → length vals ≤ W → capsOK? c sched st ≡ true →
    all (valCaps? c sl s) vals ≡ true →
    frameDrainOK c sl sf id now f p sched st →
    frameDrainW W sf id now f p sched st →
    let r = stepFrame sf id now f p vals fin sched st in
    length (proj₁ r) ≤ W →
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ nestFac (Caps.cSize c) W
        * (frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
           + nestU (Caps.cSize c) (nestUnit e sl))
  stepFrame-nodes {e = e} c W sl sf id now (map-f fn) p vals fin sched st hsl 1≤W hlen hc hv hfd hfw hw =
    ≤-trans (⊔-lub (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _)) up)
          (≤-trans (mapVals-nest fn vals)
                   (*-mono-≤ (pow-grow¹ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn)) 1≤W)
                      (≤-trans (≤-reflexive (+-comm (nestDᵗ fn) (nestDᵛˢ vals)))
                               (+-mono-≤ (m≤n⊔m (nodesMax st) (nestDᵛˢ vals))
                                         (nest-inflate W (nestDᵗ fn) 1≤W))))))
            (raiseN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl)))
    where
    X : ℕ
    X = (nodesMax st ⊔ nestDᵛˢ vals) + W * nestDᵗ fn
    up : X ≤ (2 ^ sizeᵗ fn) ^ W * X
    up = ≤-trans (≤-reflexive (sym (*-identityˡ X)))
                 (*-monoˡ-≤ X (1≤pow≤ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn))))
  stepFrame-nodes {e = e} c W sl sf id now (scan-f fn nid) p vals fin sched st hsl 1≤W hlen hc hv hfd hfw hw =
    ≤-trans (stepFrame-nodes-scan W sf id now fn nid p vals fin sched st hlen)
            (raiseN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl)))
  stepFrame-nodes {e = e} c W sl sf id now (take-f nid) p vals fin sched st hsl 1≤W hlen hc hv hfd hfw hw =
    ≤-trans (≤-trans (stepFrame-nodes-take sf id now nid p vals fin sched st)
                     (zero-charge W _))
            (raiseN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl)))
  stepFrame-nodes {e = e} c W sl sf id now (from-inner op allNid inst) p vals fin sched st hsl 1≤W hlen hc hv hfd hfw hw =
    ≤-trans (stepFrame-nodes-inner c sl W sf id now op allNid inst p vals fin sched st
               hsl (capsOK?⇒nest c sched st hc) hfd hfw)
            (*-monoʳ-≤ (nestFac (Caps.cSize c) W)
              (+-monoˡ-≤ (nestU (Caps.cSize c) (nestUnit e sl)) (zero-charge W _)))
  stepFrame-nodes {e = e} c W sl sf id now (thru-outer op nid) p vals fin sched st hsl 1≤W hlen hc hv hfd hfw hw =
    ≤-trans (stepFrame-nodes-thru c W sl sf id now op nid p vals fin sched st
               hsl 1≤W hlen hc hv hw)
            (≤-trans (*-monoʳ-≤ (nestFac (Caps.cSize c) W)
              (≤-trans (≤-reflexive (cong (_ +_) (sym (*-identityʳ W))))
                       (one-pow W (_ + W * 1))))
              (addN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl))))

-- HOISTING THE SUBSTITUTION FACTOR PAST ONE FRAME'S CHARGE, which is
-- the only arithmetic the caps rider adds to the telescope.  The factor
-- multiplies what the frame emitted and nothing else, so paying it on
-- the path's remaining charge as well is slack -- and buying that slack
-- is what lets one factor per frame come out as a power of the path's
-- length rather than interleaving with the wrap product.
abstract
  fac-hoist : ∀ (F Y A Z : ℕ) → 1 ≤ F → Y * (F * A + Z) ≤ F * (Y * (A + Z))
  fac-hoist F Y A Z 1≤F =
    ≤-trans (*-monoʳ-≤ Y (+-monoʳ-≤ (F * A) (pow-grow F 1 Z 1≤F)))
      (≤-trans (≤-reflexive (cong (λ w → Y * (F * A + w))
                                  (trans (cong (_* Z) (*-identityʳ F)) refl)))
        (≤-trans (≤-reflexive (cong (Y *_) (sym (*-distribˡ-+ F A Z))))
                 (≤-reflexive (trans (sym (*-assoc Y F (A + Z)))
                                (trans (cong (_* (A + Z)) (*-comm Y F))
                                       (*-assoc F Y (A + Z)))))))

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
  × frameDrainW W sf id now f p sched st
  × burstsOK W sf id now p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
  where step = stepFrame sf id now f p vals fin sched st

-- THE HEAD OF A WALK'S BURST BOUND, WHICH EVERY SHAPE OF PATH CARRIES.
-- Each clause bounds the list it is handed before it says anything about
-- the rest of the walk, so the frame lemma's premise about what a frame
-- EMITS is already in hand one step down -- the walk's own recursion is
-- what supplies it, and no second hypothesis is owed.
burstsHead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (p : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  burstsOK W sf id now p vals fin sched st → length vals ≤ W
burstsHead W sf id now root           vals fin sched st h = h
burstsHead W sf id now (share-sink _) vals fin sched st h = h
burstsHead W sf id now (_ ↠ _)        vals fin sched st h = proj₁ h

-- AND THE DRAIN OBLIGATION AT THE SAME HEAD, projected out so the frame
-- lemma's premise comes off the walk's own recursion rather than being
-- owed a second time.
burstsDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
  (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  burstsOK W sf id now (f ↠ p) vals fin sched st →
  frameDrainW W sf id now f p sched st
burstsDrain W sf id now f p vals fin sched st h = proj₁ (proj₂ h)

-- AND THE CAPS THE TWO `*All` FRAMES SPEND, carried the same way and for
-- the same reason.  A frame that re-enters the subscribe machinery is
-- charged in the SIZE of what it substitutes, and that size lives in the
-- store rather than in the frame -- so the walk has to be handed the
-- store's bound at every state it passes through, not just at the one it
-- starts from.  Stating it by recursion on the path is what lets the
-- induction take its own hypothesis apart instead of re-deriving the
-- caps face's frame counter in a second currency.
capsWalkOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (sf : Gas) (id : Id) (now : Tick) (p : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
capsWalkOK c sl sf id now root           vals fin sched st = capsOK? c sched st ≡ true
capsWalkOK c sl sf id now (share-sink _) vals fin sched st = capsOK? c sched st ≡ true
capsWalkOK {u = u} c sl sf id now (f ↠ p) vals fin sched st =
  (capsOK? c sched st ≡ true)
  × (all (valCaps? c sl u) vals ≡ true)
  × frameDrainOK c sl sf id now f p sched st
  × capsWalkOK c sl sf id now p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
  where step = stepFrame sf id now f p vals fin sched st

foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W →
  burstsOK W sf id now path vals fin sched st →
  capsWalkOK c sl sf id now path vals fin sched st →
  nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ (nestFac (Caps.cSize c) W) ^ pathLen path
      * (pathNestF path ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (pathNestD path + suc (pathLen path) * nestU (Caps.cSize c) (nestUnit e sl))))
foldPath-nodes c W sl sf gas id now envSrc root vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c W sl sf gas id now envSrc (share-sink i) vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (≤-trans (dispatchShare-nodes sl sf gas id now i vals fin sched st hsl)
                   (≤-trans (+-monoʳ-≤ (nodesMax st ⊔ nestDᵛˢ vals)
                              (≤-trans (nestU-base (Caps.cSize c) (nestUnit e sl))
                               (≤-trans (nest-inflate W (nestU (Caps.cSize c) (nestUnit e sl)) 1≤W)
                                       (*-monoʳ-≤ W (≤-reflexive
                                         (sym (*-identityˡ (nestU (Caps.cSize c) (nestUnit e sl)))))))))
                            (one-pow W _)))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c W sl sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (foldPath-nodes c W sl sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
             (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl)
             1≤W (proj₂ (proj₂ hb)) (proj₂ (proj₂ (proj₂ hc))))
    (≤-trans (*-monoʳ-≤ (Q ^ pathLen p)
                (*-monoʳ-≤ (pathNestF p ^ W)
                  (+-monoˡ-≤ (W * (pathNestD p + L * U))
                             (stepFrame-nodes c W sl sf id now f p vals fin sched st
                                hsl 1≤W (proj₁ hb) (proj₁ hc) (proj₁ (proj₂ hc)) (proj₁ (proj₂ (proj₂ hc)))
                                (burstsDrain W sf id now f p vals fin sched st hb)
                                (burstsHead W sf id now p vals′ fin′ sched₁ st₁ (proj₂ (proj₂ hb)))))))
    (≤-trans (*-monoʳ-≤ (Q ^ pathLen p)
                (fac-hoist Q (pathNestF p ^ W) (A + U) (W * (pathNestD p + L * U))
                           1≤Q))
    (≤-trans (≤-reflexive (sym (*-assoc (Q ^ pathLen p) Q Inner)))
    (≤-trans (≤-reflexive (cong (_* Inner) (*-comm (Q ^ pathLen p) Q)))
             (*-monoʳ-≤ (Q ^ suc (pathLen p))
    (≤-trans (*-monoʳ-≤ (pathNestF p ^ W)
               (≤-trans (≤-reflexive (+-assoc A U (W * (pathNestD p + L * U))))
                        (+-monoʳ-≤ A widen)))
    (≤-trans (nest-telescope (frameNestF f ^ W) (pathNestF p ^ W) B
                             (W * frameNestD f) (W * (pathNestD p + L * U) + W * U)
                             (1≤pow≤ (frameNestF f) W (1≤frameNestF f)))
             (≤-reflexive
               (cong₂ _*_ (sym (pow-distrib-* W (frameNestF f) (pathNestF p)))
                          (cong (B +_) charge))))))))))
  where
  S      = Caps.cSize c
  Q      = nestFac S W
  1≤Q    = 1≤nestFac S W
  A      = frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
  Inner  = pathNestF p ^ W * ((A + nestU (Caps.cSize c) (nestUnit e sl))
                              + W * (pathNestD p + suc (pathLen p) * nestU (Caps.cSize c) (nestUnit e sl)))
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestU (Caps.cSize c) (nestUnit e sl)
  L      = suc (pathLen p)

  -- the frame's own summand is paid out of the extra `W * U` the path's
  -- coefficient gains at this level, and `1 ≤ W` is what makes it fit
  widen : U + W * (pathNestD p + L * U) ≤ W * (pathNestD p + L * U) + W * U
  widen = ≤-trans (≤-reflexive (+-comm U (W * (pathNestD p + L * U))))
                  (+-monoʳ-≤ (W * (pathNestD p + L * U))
                    (≤-trans (≤-reflexive (sym (*-identityˡ U)))
                             (*-monoˡ-≤ U 1≤W)))
  step   = stepFrame sf id now f p vals fin sched st
  vals′  = proj₁ step
  evs′   = proj₁ (proj₂ step)
  fin′   = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))

  charge : W * frameNestD f + (W * (pathNestD p + L * U) + W * U)
             ≡ W * (pathNestD (f ↠ p) + suc L * U)
  charge =
    trans (cong (W * frameNestD f +_)
            (sym (*-distribˡ-+ W (pathNestD p + L * U) U)))
    (trans (sym (*-distribˡ-+ W (frameNestD f) ((pathNestD p + L * U) + U)))
           (cong (W *_) inner))
    where
    inner : frameNestD f + ((pathNestD p + L * U) + U)
              ≡ pathNestD (f ↠ p) + (U + L * U)
    inner =
      trans (cong (frameNestD f +_)
              (trans (+-assoc (pathNestD p) (L * U) U)
                     (cong (pathNestD p +_) (+-comm (L * U) U))))
      (trans (sym (+-assoc (frameNestD f) (pathNestD p) (U + L * U)))
             (cong (_+ (U + L * U)) (sym (pathNestD-cons f p))))
