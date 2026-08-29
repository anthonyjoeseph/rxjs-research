-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Rx.Frame-Width using (pWᵉ; pWᵛ)
open import Data.List.Properties using (++-identityʳ; length-++)
open import Data.Bool.ListAction using (any; all)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤; n≤1+n; m≤n+m; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤; *-assoc; *-comm; m^n>0;
  *-identityˡ; *-identityʳ; *-zeroʳ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; +-mono-≤; *-distribˡ-+;
  ^-zeroˡ; +-identityʳ; m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub; ⊔-assoc; ⊔-mono-≤; ^-distribˡ-+-*; ^-monoˡ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)
open import Data.Bool using (T)
open import Data.Fin using (toℕ)

open import Rx.Prim using (Tick; Id; Source; Gas; g0; gs; InstEvent; InstEmit; value; hot; cold; _at_from_as_;
  subscribe; init; close; handoff; complete; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; Fn; Exp; Tm; Ty; _×ᵗ_; _+ᵗ_; unitᵗ; boolᵗ; natᵗ; obs; isData; sizeᵗ;
  applyFn; _≟ᵗ_; evalTm; syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ; syncSizeᵛ; input; ofᵉ; emptyᵉ; mapᵉ;
  takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ; inputsBelowᵉ)
open import Rx.Slots using (Slots; scripted; shared; slotsSize)
open import Rx.Clos-Size using (closSizeᵉ; closSizeᵗ; closSizeᵗˢ;
  syncSize≤closᵉ; syncSize≤closᵗ; syncSize≤closᵗˢ; closSize-unfoldμ)
open import Rx.Slot-Clos using (slotClos; slotClos-pos; slotClos-fix)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵗˢ; nestDᵛ; nestDᵉ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; foldPath; dispatchShare; stepFrame; shareGo; shareAdmit; shareLatch; RegId;
  NodeId; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeState; scan-st; take-st; takeVals;
  mergeAll-st; switch-st; exhaust-st; lookupNode; setNode; scanVals; takeDispatch; innerFinish;
  aliveThroughᶠ; mergeAllDrain; subscribeInner; hasRoom; mergeAllBump; switchKill; subscribeE;
  splitBurst; Stream; mintNode; installNode; pushBurst; oneShotBurst; splitEvents; thruConsume;
  thruWalk; thruWrap; retagEvents; subscribeSharedSlot; memberSource; mintSource;
  sharedConnect; sharedPlumb; burstCompleted; register; dropSource)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; subscribeE-keeps; stepFrame-keeps; thruConsume-keeps)
open import Verify-Budget-Sufficient.Caps using
  (_⊑ᶜ_; 1≤pow≤; arrCapAt; arrCapAt-⊑; Caps; frameStep; frameStep-reg-mono; iterSize-infl;
  iterSize-mono-count; capsAt; capsAt-base-size; 2≤capsAt-size; 1≤capsAt-reg)
open import Verify-Budget-Sufficient.Caps using (sizeCount)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthDisp; depthDrain; depthFin; depthFold; depthFrame; depthInner; depthE; depthReact;
  depthShareGo; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (burstCaps?; capsOK?; valCaps?; widNode; nestValOK?; pathSz?; slotsCaps?; slotsCaps?-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using (burstCaps?-widen; valCaps?-wid)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (capsOK?-parts; foldPath-slots; pathSz?-len;
  splitEvents-vals-caps; slotsCaps?-capsAt)
open import Verify-Budget-Sufficient.Node-Table using (lookupNode-setNode; lookupNode-setNode-other)
open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; ≤ᵇ-true; T-to; ≡ᵇ→≡)
open import Verify-Budget-Sufficient.Measures using (all-impl; all-++-intro; ∧-true; syncSize-unfoldμ; fᵢ≤sum-tab)
open import Verify-Budget-Sufficient.Nest-Store using
  (nodeNest; frameNestF; 1≤frameNestF; nest-telescope; nestUnit; nest-inflate; pow-grow¹;
  pow-distrib-*; slotNest; slotsNestSum)
open import Verify-Budget-Sufficient.Fan-Caps using (fanLen; fanSq; delSq; delSq-mono; delSq-monoᶜ; cSize≤delSq; fanLen-zero; fanSq-zero; fanLen-suc; fanSq-suc)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (deliverLen; deliverNestF; deliverNestD; admSz?; shareAdmit-len; shareAdmit-sz;
   deliverLen-path; deliverSzSum-path; deliverNestD-path; deliverNestF≡;
   pathSzSum-cap; pathNestD-len)
open import Verify-Budget-Sufficient.Nest-Subst using (applyFn-nest; applyFn-nest-sync; evalTm-nest-sync; nestD-unfoldμ)
  renaming (pow-grow to pow-grow-both)
open import Verify-Budget-Sufficient.Nest-Cap using
  (nestB; nestB-mono; arrD≤nestB; nestB-base; nestB-frame; nestB-unit; nestFac; 1≤nestFac; nestU;
  nestU-mono; pow-mono-exp; nestB-at; arrD; arrDW-mono; arrDW-pos; arrDW-key; arrDW-flat; arrDW-slot;
  nestB-monoS; nestFac-monoS;
  arrDW-frame; nestB-frame-dblW)
open import Verify-Budget-Sufficient.Nest-Burst using
  (descW; innerW; drainW; innerW-gs; drainW-here; drainW-tail; descW-take; descW-map; descW-mu;
  descW-merge; descW-switch; descW-exhaust; connW; connW-gs; descW-conn)

-- THE TWO MEASURES THE WALK MOVES TOGETHER.  A frame's node stores what
-- the frame emits -- a `scan`'s accumulator IS its output -- so charging
-- the nodes map and the values in flight separately pays the same wrap
-- twice, and the path measure charges it once.  Reading them under one
-- `⊔` is what makes the frame clause telescope.
nodesMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

nestDᵛˢ : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → ℕ
nestDᵛˢ {u = u} vs = foldr (λ v acc → nestDᵛ u v ⊔ acc) 0 vs

-- A SCRIPTED SLOT CANNOT DELIVER DEPTH, and the proof is its own
-- constructor: `isData` excludes `obs` outright, so `nestDᵛ` bottoms
-- out at every leaf of such a type and the two projections below are
-- the only reasoning the product and sum cases need.
ifData-l : ∀ (a b : Bool) → T (if a then b else false) → T a
ifData-l true  b ok = tt
ifData-l false b ()

ifData-r : ∀ (a b : Bool) → T (if a then b else false) → T b
ifData-r true  b ok = ok
ifData-r false b ()

nestDᵛ-data : ∀ {n} {Γ : Ctx n} (t : Ty) → T (isData t) → (v : Val Γ t) →
  nestDᵛ t v ≡ 0
nestDᵛ-data unitᵗ    ok v        = refl
nestDᵛ-data boolᵗ    ok v        = refl
nestDᵛ-data natᵗ     ok v        = refl
nestDᵛ-data (s ×ᵗ t) ok (a , b)  =
  cong₂ _⊔_ (nestDᵛ-data s (ifData-l (isData s) (isData t) ok) a)
            (nestDᵛ-data t (ifData-r (isData s) (isData t) ok) b)
nestDᵛ-data (s +ᵗ t) ok (inj₁ a) =
  nestDᵛ-data s (ifData-l (isData s) (isData t) ok) a
nestDᵛ-data (s +ᵗ t) ok (inj₂ b) =
  nestDᵛ-data t (ifData-r (isData s) (isData t) ok) b
nestDᵛ-data (obs t)  () v

nestDᵛˢ-data : ∀ {n} {Γ : Ctx n} {u} → T (isData u) →
  (vs : List (Val Γ u)) → nestDᵛˢ {Γ = Γ} vs ≡ 0
nestDᵛˢ-data ok []       = refl
nestDᵛˢ-data {u = u} ok (v ∷ vs) =
  cong₂ _⊔_ (nestDᵛ-data u ok v) (nestDᵛˢ-data ok vs)

-- ONE FRAME'S SHARE OF THE PATH MEASURE, split out so the frame clause
-- can spend it.  It is `pathNestD`'s own step and nothing else, which
-- the equation below is the whole proof of.
frameNestD : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameNestD (map-f f)          = nestDᵗ f
frameNestD (scan-f f _)       = nestDᵗ f
frameNestD (take-f _)         = 0
frameNestD (from-inner _ _ _) = 0
frameNestD (thru-outer _ _)   = 1

-- and the deliver measure's own step, which is the same equation at
-- every frame — only the sink clause separates the two measures
deliverNestD-cons : ∀ {n} {Γ : Ctx n} {s u t} (g : ℕ) (c : Caps)
  (f : Frame Γ s u) (p : Path Γ u t) →
  deliverNestD g c (f ↠ p) ≡ frameNestD f + deliverNestD g c p
deliverNestD-cons g c (map-f _)          p = refl
deliverNestD-cons g c (scan-f _ _)       p = refl
deliverNestD-cons g c (take-f _)         p = refl
deliverNestD-cons g c (from-inner _ _ _) p = refl
deliverNestD-cons g c (thru-outer _ _)   p = refl

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

  -- the same fold with the exponent read on the sync spine, which is
  -- the denomination the frame's own bound is stated in
  mapVals-nest-sync : ∀ {n} {Γ : Ctx n} {s u}
    (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
    nestDᵛˢ (map (applyFn fn) vals) ≤ 2 ^ syncSizeᵗ fn * (nestDᵗ fn + nestDᵛˢ vals)
  mapVals-nest-sync fn []           = z≤n
  mapVals-nest-sync {u = u} fn (v ∷ vs) =
    ⊔-lub (≤-trans (applyFn-nest-sync fn v)
                   (*-monoʳ-≤ (2 ^ syncSizeᵗ fn)
                      (+-monoʳ-≤ (nestDᵗ fn) (m≤m⊔n (nestDᵛ _ v) (nestDᵛˢ vs)))))
          (≤-trans (mapVals-nest-sync fn vs)
                   (*-monoʳ-≤ (2 ^ syncSizeᵗ fn)
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

  initHead-vals : ∀ {n} {Γ : Ctx n} {u} {A : Set}
    (vals : List (Val Γ u)) (i : Id) (s : Source) →
    proj₁ (splitBurst {A = A}
             (((init s ∷ map value vals) at i from s as subscribe) ∷ []))
      ≡ vals
  initHead-vals vals i s =
    trans (cong (_++ []) (trans (cong (λ z → proj₁ (splitEvents z))
                                      (sym (++-identityʳ (map value vals))))
                                (splitEvents-vals vals [])))
          (trans (cong (_++ []) (++-identityʳ vals)) (++-identityʳ vals))

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

  -- and the two injections, which is what a fold over the SPLIT list
  -- spends when its bound is read against the joined one
  nestDᵛˢ-++ˡ : ∀ {n} {Γ : Ctx n} {u} (xs ys : List (Val Γ u)) →
    nestDᵛˢ xs ≤ nestDᵛˢ (xs ++ ys)
  nestDᵛˢ-++ˡ []       ys = z≤n
  nestDᵛˢ-++ˡ {u = u} (x ∷ xs) ys =
    ⊔-mono-≤ (≤-refl {nestDᵛ u x}) (nestDᵛˢ-++ˡ xs ys)

  nestDᵛˢ-++ʳ : ∀ {n} {Γ : Ctx n} {u} (xs ys : List (Val Γ u)) →
    nestDᵛˢ ys ≤ nestDᵛˢ (xs ++ ys)
  nestDᵛˢ-++ʳ []       ys = ≤-refl
  nestDᵛˢ-++ʳ {u = u} (x ∷ xs) ys =
    ≤-trans (nestDᵛˢ-++ʳ xs ys) (m≤n⊔m (nestDᵛ u x) (nestDᵛˢ (xs ++ ys)))

-- THE CAPS PREMISE THIS FACE CARRIES, AND IT IS DELIBERATELY WEAKER
-- THAN THE CAPS FACE'S: it bounds the LIVE subscriptions' sizes and
-- the stored nodes' WIDTHS, and says nothing about a stored node's
-- SIZE.
--
-- Dropping the store's size conjunct is one fact and not two -- no
-- head of this face can re-establish it, and no head of this face
-- reads it.  It cannot be re-established because the only premise a
-- head holds about an arrival bounds the arrival's SYNC size, while
-- the store predicate reads its TERM size, and evaluation relates the
-- two in the wrong direction.  It is not read because this face
-- measures DEPTH: the one place a stored value is consulted -- the
-- frame-level scan bound -- goes through `lookupNode-nodes` at its
-- depth, and what the *All heads actually spend is the flatten
-- queue's WIDTH.
--
-- AND THE REGISTRY GOES FOR THE SAME REASON, one step further out.
-- The per-path size bound and the count against the registry cap are
-- both SIZE facts, so this face does not read them; and the connect
-- arm APPENDS to the registry, so no head that joins a share can
-- re-establish either.  The caps face pays for that append by moving
-- its cap -- `register-caps` concludes at `frameStep (suc j) c` where
-- it began at `frameStep j c` -- and this predicate is stated at a
-- flat `c` with no frame index to spend.  Carrying a conjunct nothing
-- reads and no head can restore is what made the slot handoff look
-- impossible; without them `register` preserves this predicate
-- outright, since it writes the registry and its counter and nothing
-- else.
--
-- Weakening a HYPOTHESIS strengthens every statement it appears in, so
-- the boundary runs one way only: a caller holding the caps face's own
-- predicate hands it in through `capsOK?⇒nest`, and nothing converts
-- back.
-- REFUTED: `Refuted.Scan-Seed-Caps` is the size crossing, at the
--   smallest cap the storing head's premise admits.
nodeWidᴺ? : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
nodeWidᴺ? W sl (scan-st _)                = true
nodeWidᴺ? W sl (take-st _)                = true
nodeWidᴺ? W sl (mergeAll-st lim act q od) = widNode W sl (mergeAll-st lim act q od)
nodeWidᴺ? W sl (switch-st _ _)            = true
nodeWidᴺ? W sl (exhaust-st _ _)           = true

-- ONLY THE NODES CONJUNCT, deliberately.  This predicate once carried
-- a full-size bound and a pending-width bound over the live list, and
-- BOTH were spent by nothing on this face: the one read anything here
-- performs is `nestCapsOK?-lookupWid`, on the node table.  Neither
-- dead conjunct was preservable from the walk's sync-denominated
-- premises -- a defer parks its own body as a pending payload at FULL
-- syntax size and FULL delivered width, while `nestValOK?`,
-- `nestClosOK?` and `descW` all read the defer as 1 -- and the proven
-- caps face pays those entries from a full-size budget and a
-- parked-width premise this face deliberately does not carry.
-- REFUTED: `Refuted.Defer-Park-Size` kills the family over the
--   size-carrying predicate, a defer at its own descent bound against
--   the evaluator's initial state.
-- REFUTED: `Refuted.Defer-Park-Width` kills it again over the
--   pending-width conjunct, the same program at unit width.
nestCapsOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → Caps → Sched Γ → EvalSt e → Bool
nestCapsOK? c sched st =
  all (λ kv → nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
      (EvalSt.nodes st)

nodeWidᴺ?-weaken : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ns : NodeState Γ) →
  widNode W sl ns ≡ true → nodeWidᴺ? W sl ns ≡ true
nodeWidᴺ?-weaken W sl (scan-st _)          h = refl
nodeWidᴺ?-weaken W sl (take-st _)          h = refl
nodeWidᴺ?-weaken W sl (mergeAll-st _ _ _ _) h = h
nodeWidᴺ?-weaken W sl (switch-st _ _)      h = refl
nodeWidᴺ?-weaken W sl (exhaust-st _ _)     h = refl

-- AND THE SAME READING WIDENS.  The node conjunct is one bound against
-- `cWid` and nothing else, so a bigger width is a weaker demand at
-- every arm -- which is what lets a walk that STEPS its cap hand its
-- table invariant to a reader standing further along.

-- THE PREMISES THE PROVEN CLIQUE READS AND THIS CONE DOES NOT, in one
-- name because they travel together: they are facts about the CAP and
-- the SLOTS, and the slots are fixed for a whole instant.  Bundling is
-- not cosmetic here: the alternative is four binders in every clause of
-- thirty heads, and the count is what makes such a sweep go wrong.
--
-- AND IT IS CARRIED AS AN INSTANCE, which is what makes the sweep a
-- signature edit rather than a clause edit -- no clause binds it and a
-- recursive call resolves it itself.  The CAP is not fixed along the
-- walk, so the transport below is the load-bearing half: every step of
-- the frame widens both numbers, and the bundle survives a widening
-- because each of its four conjuncts does.
record FaceOK {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) : Set where
  constructor faceOK
  field
    fSize : 2 ≤ Caps.cSize c
    fReg  : 1 ≤ Caps.cReg c
    fSlC  : slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true
    fSlSz : slotsSize sl ≤ Caps.cSize c

-- AND THE TRANSPORT IS SPENT BY HAND, NOT SEARCHED FOR.  An instance
-- keyed on the STEPPED cap cannot be resolved: `arrCapAt` is a defined
-- function, so matching a goal at `arrCapAt j c` against such a head
-- asks the unifier to invert it and it leaves metas instead.  So the
-- step is an ordinary lemma, applied explicitly at the handful of sites
-- that enter a callee at the stepped cap, and `faceHere` is what reads
-- the ambient bundle back out to feed it.
faceArr : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (j : ℕ) →
  FaceOK c sl → FaceOK (arrCapAt j c) sl
faceArr c sl j f =
  faceOK (≤-trans (FaceOK.fSize f) S≤) (FaceOK.fReg f)
    (slotsCaps?-widen (Caps.cSize c) (Caps.cSize (arrCapAt j c))
      (Caps.cWid c) (Caps.cWid c) sl S≤ ≤-refl (FaceOK.fSlC f))
    (≤-trans (FaceOK.fSlSz f) S≤)
  where
  S≤ : Caps.cSize c ≤ Caps.cSize (arrCapAt j c)
  S≤ = iterSize-infl (Caps.cSize c)
         (≤-trans (s≤s z≤n) (FaceOK.fSize f)) j (Caps.cSize c)

faceHere : ∀ {n} {Γ : Ctx n} {c : Caps} {sl : Slots Γ} →
  ⦃ FaceOK c sl ⦄ → FaceOK c sl
faceHere ⦃ f ⦄ = f

-- AND THE INSTANT'S OWN CAP CARRIES ALL FOUR ALREADY, which is what
-- makes this bundle free rather than a new obligation on the top line:
-- the cone's door out is entered at `capsAt`, where each conjunct is a
-- proven fact about that family and not a hypothesis anyone acquires.
faceAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  FaceOK (capsAt e sl id) sl
faceAt e sl id =
  faceOK (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)
    (slotsCaps?-capsAt e sl id)
    (≤-trans (m≤n+m (slotsSize sl) _) (capsAt-base-size e sl id))

capsOK?⇒nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → nestCapsOK? c sched st ≡ true
capsOK?⇒nest c sched st h =
    all-impl _ _
       (λ kv → nodeWidᴺ?-weaken (Caps.cWid c) (Sched.slots sched)
                 (proj₂ kv))
       (EvalSt.nodes st)
       (proj₁ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st h)))))


-- minting an instance id touches the node counter and nothing this
-- predicate reads
nestCapsOK?-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (k : NodeId) (sched : Sched Γ) (st : EvalSt e) →
  nestCapsOK? c sched st ≡ true →
  nestCapsOK? c (record sched { nextNode = k }) st ≡ true
nestCapsOK?-nextNode c k sched st h = h

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
  nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  nestCapsOK? c sched st ≡ true →
  nestCapsOK? c sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) ≡ true
nestCapsOK?-setNode c nid ns sched st wn inv =
  setNode-nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) nid ns
    (EvalSt.nodes st) wn inv

-- and the read the write law needs beside it: a node the table holds
-- already passed the width check the invariant folds over the table
nestCapsOK?-lookupWid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just ns →
  nestCapsOK? c sched st ≡ true →
  nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) ns ≡ true
nestCapsOK?-lookupWid {Γ = Γ} c nid ns sched st eq hc =
  go (EvalSt.nodes st) hc eq
  where
  go : (nodes : List (NodeId × NodeState Γ)) →
    all (λ kv → nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) (proj₂ kv)) nodes ≡ true →
    lookupNode nid nodes ≡ just ns →
    nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) ns ≡ true
  go [] h ()
  go ((k , s′) ∷ r) h e with k ≡ᵇ nid | e
  ... | true  | refl = ∧-trueˡ h
  ... | false | e′   = go r (∧-trueʳ h) e′


-- THE CAP READ AGAINST THE ARRIVAL'S CLOSURE, which is the shape the
-- arr-keyed descent needs and the one `nestValOK?` deliberately does
-- not have: that predicate is a fact about a VALUE alone, while the
-- key a subscription is charged at sees through the telescope the
-- value may reference.  The two coincide on a slot-free arrival.
-- AND THE FLAT SLOT MEASURE CANNOT STAND IN FOR IT, which is worth
-- saying because that measure is the one the caps face already carries
-- as a standing premise and the obvious candidate for generalising this
-- key away.  `closSizeᵉ` reads `input i` as `slotClos i`, so a
-- definition naming a slot TWICE pays for it twice, and a telescope in
-- which each definition doubles its predecessor is closed under
-- `inputsBelowᵉ`: the closure measure is multiplicative in the
-- telescope's depth where `slotsSize` is a flat sum of written sizes.
-- Four such slots already read 27 against 98.  So `slotsSize sl ≤
-- Caps.cSize c` does not imply this predicate, and the two premises are
-- independent rather than one subsuming the other.

-- AND WHETHER THE CAP THE TOP INSTANTIATES CAN SATISFY IT IS OPEN, AND
-- SYMBOLIC-OR-NOTHING.  Every consumer of this key takes it as a
-- premise, so nothing owes a proof today; what is owed at the top is
-- that `capsAt`'s own size admits the telescope, and by the paragraph
-- above that number has to beat a measure exponential in the
-- telescope's depth.  THE MEASURING ROUTE IS CLOSED: `capsAt`'s size is
-- `iterSize` at a count the caps counting family produces, and that
-- family is the one the harness quarantines as unreachable by
-- measurement -- native code at the smallest arguments, no value -- so
-- no probe, row or `refl` pin can decide it.  What is left is
-- arithmetic already in the tree: `exp-iterSize` puts `2 ^ k` under
-- that size, so the question reduces to whether the count dominates the
-- slot depth, and that is a statement about the counting family rather
-- than about this predicate.  No assembly is stated for it here because
-- the walk has no top-level consumer to hang one on yet.

nestClosOK? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → Val Γ (obs u) → Bool
nestClosOK? c sl o = closSizeᵉ (slotClos sl) o ≤ᵇ Caps.cSize c

-- AND THE SAME READING FOLDED OVER A WHOLE SUBSCRIPTION, event by
-- event, which is the shape the caps face already states its own
-- arrival predicate in.  Only a `value` carries an arrival, so every
-- other event reads as true outright -- the fold is a filter with the
-- closure reading attached, not a second traversal.
nestClosOK?ᵛ : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → (u : Ty) → Val Γ u → Bool
nestClosOK?ᵛ c sl unitᵗ    _        = true
nestClosOK?ᵛ c sl boolᵗ    _        = true
nestClosOK?ᵛ c sl natᵗ     _        = true
nestClosOK?ᵛ c sl (s ×ᵗ t) (a , b)  = nestClosOK?ᵛ c sl s a ∧ nestClosOK?ᵛ c sl t b
nestClosOK?ᵛ c sl (s +ᵗ t) (inj₁ a) = nestClosOK?ᵛ c sl s a
nestClosOK?ᵛ c sl (s +ᵗ t) (inj₂ b) = nestClosOK?ᵛ c sl t b
nestClosOK?ᵛ c sl (obs t)  o        = nestClosOK? c sl o

eventNest? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → InstEvent (Val Γ u) → Bool
eventNest? {u = u} c sl (value v) = nestClosOK?ᵛ c sl u v
eventNest? c sl (init _)    = true
eventNest? c sl (close _ _) = true
eventNest? c sl (handoff _) = true
eventNest? c sl complete    = true

burstNest? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → Stream Γ u → Bool
burstNest? c sl = all (λ em → all (eventNest? c sl) (InstEmit.events em))

-- AND BOTH ARRIVAL BOOLEANS WIDEN WITH THE CAP, which is what lets a
-- caller read a bound at the level the walk reports and spend it at
-- the join its own arm needs.  The size field is the only one the
-- arrival cap moves, and every reading here is against it.
nestClosOK?ᵛ-widen : ∀ {n} {Γ : Ctx n} {c c′ : Caps} (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  c ⊑ᶜ c′ → nestClosOK?ᵛ c sl u v ≡ true → nestClosOK?ᵛ c′ sl u v ≡ true
nestClosOK?ᵛ-widen sl unitᵗ    v        le h = refl
nestClosOK?ᵛ-widen sl boolᵗ    v        le h = refl
nestClosOK?ᵛ-widen sl natᵗ     v        le h = refl
nestClosOK?ᵛ-widen sl (s ×ᵗ t) (a , b)  le h =
  ∧-intro (nestClosOK?ᵛ-widen sl s a le (proj₁ (∧-true _ _ h)))
          (nestClosOK?ᵛ-widen sl t b le (proj₂ (∧-true _ _ h)))
nestClosOK?ᵛ-widen sl (s +ᵗ t) (inj₁ a) le h = nestClosOK?ᵛ-widen sl s a le h
nestClosOK?ᵛ-widen sl (s +ᵗ t) (inj₂ b) le h = nestClosOK?ᵛ-widen sl t b le h
nestClosOK?ᵛ-widen {c = c} sl (obs t) o le h =
  ≤ᵇ-true _ _ (≤-trans (≤ᵇ⇒≤ (closSizeᵉ (slotClos sl) o) (Caps.cSize c) (T-to h)) (proj₁ le))

burstNest?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ) (str : Stream Γ u) →
  c ⊑ᶜ c′ → burstNest? c sl str ≡ true → burstNest? c′ sl str ≡ true
burstNest?-widen sl [] le h = refl
burstNest?-widen {u = u} sl (em ∷ ems) le h =
  ∧-intro (all-impl _ _ EV (InstEmit.events em) (proj₁ (∧-true _ _ h)))
          (burstNest?-widen sl ems le (proj₂ (∧-true _ _ h)))
  where
  EV : ∀ (ev : InstEvent (Val _ u)) → _ ≡ true → _ ≡ true
  EV (value v)   hv = nestClosOK?ᵛ-widen sl u v le hv
  EV (init _)    hv = refl
  EV (close _ _) hv = refl
  EV (handoff _) hv = refl
  EV complete    hv = refl

abstract
  nestClosOK?-size : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
    (o : Val Γ (obs u)) →
    nestClosOK? c sl o ≡ true → closSizeᵉ (slotClos sl) o ≤ Caps.cSize c
  nestClosOK?-size c sl o h = ≤ᵇ⇒≤ _ _ (T-to h)

-- AND IT NARROWS THE WAY THE SIZE PREDICATE DOES, which is what lets a
-- head hand the bound to what it wraps: every wrapper is one node
-- bigger than its source under the closure measure exactly as it is
-- under the written one, so the inequality that carries the premise
-- inward is the constructor's own equation and nothing more.
abstract
  nestClosOK?-mono : ∀ {n} {Γ : Ctx n} {u v} (c : Caps) (sl : Slots Γ)
    (x : Val Γ (obs u)) (y : Val Γ (obs v)) →
    closSizeᵉ (slotClos sl) x ≤ closSizeᵉ (slotClos sl) y →
    nestClosOK? c sl y ≡ true → nestClosOK? c sl x ≡ true
  nestClosOK?-mono c sl x y le h =
    ≤ᵇ-true (closSizeᵉ (slotClos sl) x) (Caps.cSize c)
      (≤-trans le (nestClosOK?-size c sl y h))

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
  × (nestClosOK? c sl o ≡ true)
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

  nestValOK?-merge : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
    (lim : Maybe ℕ) (b : Closed Γ (obs u)) →
    nestValOK? c (obs u) (mergeAllᵉ lim b) ≡ true →
    nestValOK? c (obs (obs u)) b ≡ true
  nestValOK?-merge {u = u} c lim b h =
    ≤ᵇ-true (syncSizeᵛ (obs (obs u)) b) (Caps.cSize c)
      (≤-trans (n≤1+n (syncSizeᵉ b)) (≤ᵇ⇒≤ _ _ (T-to h)))

  nestValOK?-switch : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
    (b : Closed Γ (obs u)) →
    nestValOK? c (obs u) (switchAllᵉ b) ≡ true →
    nestValOK? c (obs (obs u)) b ≡ true
  nestValOK?-switch {u = u} c b h =
    ≤ᵇ-true (syncSizeᵛ (obs (obs u)) b) (Caps.cSize c)
      (≤-trans (n≤1+n (syncSizeᵉ b)) (≤ᵇ⇒≤ _ _ (T-to h)))

  nestValOK?-exhaust : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
    (b : Closed Γ (obs u)) →
    nestValOK? c (obs u) (exhaustAllᵉ b) ≡ true →
    nestValOK? c (obs (obs u)) b ≡ true
  nestValOK?-exhaust {u = u} c b h =
    ≤ᵇ-true (syncSizeᵛ (obs (obs u)) b) (Caps.cSize c)
      (≤-trans (n≤1+n (syncSizeᵉ b)) (≤ᵇ⇒≤ _ _ (T-to h)))



-- THE THRU FRAME'S PUSH, TAKEN APART.  A `thru-outer` frame is the one
-- whose step SUBSCRIBES what passes it, so its push cannot be a single
-- postulated leaf the way the filter's and the map's are: the checked
-- part is everything AROUND the subscription -- how the walk chains its
-- consume steps, how the wrap writes its flag, how `pushBurst` splits
-- and reassembles each emit -- and the lemmas below carry exactly that,
-- leaving one fit relation to assert what a consume step costs.

-- The reassembled emit's value reading is the stepped values and only
-- them: bookkeeping splits to no value on either side of the retag, a
-- `value` maps to itself, and the terminal `complete` is value-free.
abstract
  splitEvents-book-id : ∀ {n} {Γ : Ctx n} {s u} {A : Set}
    (es : List (InstEvent (Val Γ s)))
    (tl : List (InstEvent (Val Γ u))) →
    proj₁ (splitEvents {A = A}
            (proj₁ (proj₂ (splitEvents {A = Val Γ u} es)) ++ tl))
      ≡ proj₁ (splitEvents {A = A} tl)
  splitEvents-book-id []               tl = refl
  splitEvents-book-id (value v   ∷ es) tl = splitEvents-book-id es tl
  splitEvents-book-id (init s    ∷ es) tl = splitEvents-book-id es tl
  splitEvents-book-id (close s r ∷ es) tl = splitEvents-book-id es tl
  splitEvents-book-id (handoff s ∷ es) tl = splitEvents-book-id es tl
  splitEvents-book-id (complete  ∷ es) tl = splitEvents-book-id es tl

  splitEvents-retag-id : ∀ {n} {Γ : Ctx n} {u} {A B : Set}
    (evs : List (InstEvent B))
    (tl : List (InstEvent (Val Γ u))) →
    proj₁ (splitEvents {A = A} (retagEvents evs ++ tl))
      ≡ proj₁ (splitEvents {A = A} tl)
  splitEvents-retag-id []               tl = refl
  splitEvents-retag-id (value v   ∷ es) tl = splitEvents-retag-id es tl
  splitEvents-retag-id (init s    ∷ es) tl = splitEvents-retag-id es tl
  splitEvents-retag-id (close s r ∷ es) tl = splitEvents-retag-id es tl
  splitEvents-retag-id (handoff s ∷ es) tl = splitEvents-retag-id es tl
  splitEvents-retag-id (complete  ∷ es) tl = splitEvents-retag-id es tl

  pushEmit-vals : ∀ {n} {Γ : Ctx n} {s u} {A B : Set}
    (es : List (InstEvent (Val Γ s)))
    (evs : List (InstEvent B))
    (vals : List (Val Γ u)) (fin : Bool) →
    proj₁ (splitEvents {A = A}
            (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))
             ++ retagEvents evs
             ++ map value vals
             ++ (if fin then complete ∷ [] else [])))
      ≡ vals
  pushEmit-vals es evs vals true  =
    trans (splitEvents-book-id es _)
      (trans (splitEvents-retag-id evs _)
        (trans (splitEvents-vals vals (complete ∷ []))
               (++-identityʳ vals)))
  pushEmit-vals es evs vals false =
    trans (splitEvents-book-id es _)
      (trans (splitEvents-retag-id evs _)
        (trans (splitEvents-vals vals [])
               (++-identityʳ vals)))

  -- the retag type is a phantom on the VALUE component, so the two
  -- readings a statement and its reduction pick are the same list
  splitEvents-vals-A : ∀ {n} {Γ : Ctx n} {u} {A B : Set}
    (es : List (InstEvent (Val Γ u))) →
    proj₁ (splitEvents {A = A} es) ≡ proj₁ (splitEvents {A = B} es)
  splitEvents-vals-A []               = refl
  splitEvents-vals-A (value v   ∷ es) = cong (v ∷_) (splitEvents-vals-A es)
  splitEvents-vals-A (init s    ∷ es) = splitEvents-vals-A es
  splitEvents-vals-A (close s r ∷ es) = splitEvents-vals-A es
  splitEvents-vals-A (handoff s ∷ es) = splitEvents-vals-A es
  splitEvents-vals-A (complete  ∷ es) = splitEvents-vals-A es

-- A write that does not deepen its node moves NO reading of the table:
-- `lookupNode-set-at` at the point where the written state is bounded
-- by the one it replaces, which is what a flag flip is.
abstract
  lookupNode-set-same : ∀ {n} {Γ : Ctx n} (j nid : NodeId)
    (ns os : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
    lookupNode nid nodes ≡ just os →
    nodeNest ns ≤ nodeNest os →
    maybe nodeNest 0 (lookupNode j (setNode nid ns nodes))
      ≤ maybe nodeNest 0 (lookupNode j nodes)
  lookupNode-set-same j nid ns os ((k , s′) ∷ r) hl hle with k ≡ᵇ nid in eqk
  lookupNode-set-same j nid ns os ((k , s′) ∷ r) refl hle | true
    rewrite ≡ᵇ→≡ k nid eqk with nid ≡ᵇ j
  ...   | true  = hle
  ...   | false = ≤-refl
  lookupNode-set-same j nid ns os ((k , s′) ∷ r) hl hle | false
    with k ≡ᵇ j
  ...   | true  = ≤-refl
  ...   | false = lookupNode-set-same j nid ns os r hl hle

  ⊔-chain : ∀ {x y z G : ℕ} → x ≤ y ⊔ G → y ≤ z ⊔ G → x ≤ z ⊔ G
  ⊔-chain {z = z} {G = G} hxy hyz = ≤-trans hxy (⊔-lub hyz (m≤n⊔m z G))

-- THE WRAP IS FREE.  On the closing emit it re-reads its own node and
-- writes it back with the drained flag set, and a flag deepens nothing:
-- a merge node's nesting is its queue's fold with or without the flag,
-- and the other two states read zero either way.  Values pass verbatim.
abstract
  thruWrap-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (op : AllOp) (nid : NodeId) (fin : Bool)
    (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
    (sched : Sched Γ) (st : EvalSt e) →
    let r = thruWrap op nid fin (vs , bs , sched , st) in
    (proj₁ r ≡ vs)
    × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≤ nodesMax st)
    × ((j : NodeId) → nodeNestAt j (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≤ nodeNestAt j st)
  thruWrap-nest op nid false vs bs sched st = refl , ≤-refl , (λ j → ≤-refl)
  thruWrap-nest mergeAllᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st) in eq
  ... | just (mergeAll-st lim act q od) =
        refl
        , ≤-trans (setNode-nodes nid (mergeAll-st lim act q true) (EvalSt.nodes st))
                  (⊔-lub (lookupNode-nodes nid (mergeAll-st lim act q od)
                            (EvalSt.nodes st) eq)
                         ≤-refl)
        , (λ j → lookupNode-set-same j nid (mergeAll-st lim act q true)
                   (mergeAll-st lim act q od) (EvalSt.nodes st) eq ≤-refl)
  ... | just (scan-st v)        = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (take-st k)        = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (switch-st cu od)  = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (exhaust-st ac od) = refl , ≤-refl , (λ j → ≤-refl)
  ... | nothing                 = refl , ≤-refl , (λ j → ≤-refl)
  thruWrap-nest switchᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st) in eq
  ... | just (switch-st cur od) =
        refl
        , ≤-trans (setNode-nodes nid (switch-st cur true) (EvalSt.nodes st))
                  (⊔-lub z≤n ≤-refl)
        , (λ j → lookupNode-set-same j nid (switch-st cur true)
                   (switch-st cur od) (EvalSt.nodes st) eq ≤-refl)
  ... | just (scan-st v)         = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (take-st k)         = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (mergeAll-st l a q od) = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (exhaust-st ac od)  = refl , ≤-refl , (λ j → ≤-refl)
  ... | nothing                  = refl , ≤-refl , (λ j → ≤-refl)
  thruWrap-nest exhaustᵒ nid true vs bs sched st
    with lookupNode nid (EvalSt.nodes st) in eq
  ... | just (exhaust-st act od) =
        refl
        , ≤-trans (setNode-nodes nid (exhaust-st act true) (EvalSt.nodes st))
                  (⊔-lub z≤n ≤-refl)
        , (λ j → lookupNode-set-same j nid (exhaust-st act true)
                   (exhaust-st act od) (EvalSt.nodes st) eq ≤-refl)
  ... | just (scan-st v)         = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (take-st k)         = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (mergeAll-st l a q od) = refl , ≤-refl , (λ j → ≤-refl)
  ... | just (switch-st cu od)   = refl , ≤-refl , (λ j → ≤-refl)
  ... | nothing                  = refl , ≤-refl , (λ j → ≤-refl)

-- WHAT A CONSUME STEP MUST COST, threaded over the run's own states the
-- way `capsDrainOK` threads its premise: one conjunct per value of the
-- outer's burst, each read at the state the previous step actually left.
-- This is the relation the three fit leaves below assert and the walk
-- lemma spends, and it is per-step by design -- the head's whole-descent
-- claim is recovered from it by checked chaining, so the assertion left
-- is the smallest one the frame's subscription forces.
thruFitOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (G : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruFitOK G fuel op nid κ id now [] sched st = ⊤
thruFitOK G fuel op nid κ id now (o ∷ os) sched st =
  (nestDᵛˢ (proj₁ rc) ≤ G)
  × (nodesMax (proj₂ (proj₂ (proj₂ rc))) ≤ nodesMax st ⊔ G)
  × ((j : NodeId) → nodeNestAt j (proj₂ (proj₂ (proj₂ rc))) ≤ nodeNestAt j st ⊔ G)
  × thruFitOK G fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
  where rc = thruConsume fuel op nid κ id now o sched st

-- A WIDER GRANT IS STILL A GRANT.  Every conjunct is upward-closed in
-- `G` -- two of them under a `⊔` -- so a fit taken in one currency
-- transports to any bound above it, which is what lets the frame spend
-- a walk proven at the machinery's own grant.
thruFitOK-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (G G′ : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  G ≤ G′ →
  thruFitOK G fuel op nid κ id now os sched st →
  thruFitOK G′ fuel op nid κ id now os sched st
thruFitOK-mono G G′ fuel op nid κ id now [] sched st le fit = tt
thruFitOK-mono G G′ fuel op nid κ id now (o ∷ os) sched st le (h1 , h2 , h3 , rest) =
  ≤-trans h1 le
  , ≤-trans h2 (⊔-mono-≤ ≤-refl le)
  , (λ j → ≤-trans (h3 j) (⊔-mono-≤ ≤-refl le))
  , thruFitOK-mono G G′ fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc))) le rest
  where rc = thruConsume fuel op nid κ id now o sched st

-- The walk is the fit chained: values join step by step, the store
-- bounds compose because the grant is the SAME `G` at every step.
thruWalk-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (G : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  thruFitOK G fuel op nid κ id now os sched st →
  let r = thruWalk fuel op nid κ id now os sched st in
  (nestDᵛˢ (proj₁ r) ≤ G)
  × (nodesMax (proj₂ (proj₂ (proj₂ r))) ≤ nodesMax st ⊔ G)
  × ((j : NodeId) → nodeNestAt j (proj₂ (proj₂ (proj₂ r))) ≤ nodeNestAt j st ⊔ G)
thruWalk-nest G fuel op nid κ id now [] sched st fit =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
thruWalk-nest G fuel op nid κ id now (o ∷ os) sched st (h1 , h2 , h3 , rest) =
  ≤-trans (nestDᵛˢ-++ (proj₁ rc) (proj₁ rw)) (⊔-lub h1 (proj₁ IH))
  , ⊔-chain (proj₁ (proj₂ IH)) h2
  , (λ j → ⊔-chain (proj₂ (proj₂ IH) j) (h3 j))
  where
  rc = thruConsume fuel op nid κ id now o sched st
  rw = thruWalk fuel op nid κ id now os
         (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
  IH = thruWalk-nest G fuel op nid κ id now os
         (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc))) rest

-- The same relation lifted over the burst the descent hands back, one
-- fit per emit, each at the state the previous frame left.
pushFitOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (G : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushFitOK G fuel op nid κ id now [] sched st = ⊤
pushFitOK {Γ = Γ} {u = u} G fuel op nid κ id now (em ∷ ems) sched st =
  thruFitOK G fuel op nid κ id now (proj₁ sp) sched st
  × pushFitOK G fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

-- And the push itself, CHECKED: split each emit, walk it, wrap it,
-- reassemble -- the value reading survives the reassembly verbatim, so
-- the head's burst conjunct is the walks' joined, and the store
-- conjuncts chain because every frame runs at the same grant.
pushBurst-nest-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (G : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  pushFitOK G fuel op nid κ id now str sched st →
  let r = pushBurst fuel id now (thru-outer op nid) κ str sched st in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ G)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ G)
  × ((j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st ⊔ G)
pushBurst-nest-thru G fuel op nid κ id now [] sched st fit =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
pushBurst-nest-thru {Γ = Γ} {t = t} {u = u} G fuel op nid κ id now (em ∷ ems)
                    sched st (fitH , fitR) =
  ≤-trans (nestDᵛˢ-++
             (proj₁ (splitEvents {A = Val Γ t}
               (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ sf))
                ++ map value (proj₁ sf)
                ++ (if proj₁ (proj₂ (proj₂ sf)) then complete ∷ [] else []))))
             (proj₁ (splitBurst {A = Val Γ t}
               (proj₁ (pushBurst fuel id now (thru-outer op nid) κ ems sched₁ st₁)))))
    (⊔-lub (≤-trans (≤-reflexive (cong (nestDᵛˢ {u = u}) PEV)) (proj₁ WK))
           (proj₁ IH))
  , ⊔-chain (proj₁ (proj₂ IH)) N₁
  , (λ j → ⊔-chain (proj₂ (proj₂ IH) j) (N₂ j))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  wk = thruWalk fuel op nid κ id now (proj₁ sp) sched st
  WK = thruWalk-nest G fuel op nid κ id now (proj₁ sp) sched st fitH
  WR = thruWrap-nest op nid (proj₂ (proj₂ sp)) (proj₁ wk) (proj₁ (proj₂ wk))
         (proj₁ (proj₂ (proj₂ wk))) (proj₂ (proj₂ (proj₂ wk)))
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ sf)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ sf)))
  IH = pushBurst-nest-thru G fuel op nid κ id now ems sched₁ st₁ fitR
  PEV : proj₁ (splitEvents {A = Val Γ t}
          (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ sf))
           ++ map value (proj₁ sf)
           ++ (if proj₁ (proj₂ (proj₂ sf)) then complete ∷ [] else [])))
          ≡ proj₁ wk
  PEV = trans (pushEmit-vals (InstEmit.events em) (proj₁ (proj₂ sf)) (proj₁ sf)
                (proj₁ (proj₂ (proj₂ sf))))
              (proj₁ WR)
  N₁ : nodesMax st₁ ≤ nodesMax st ⊔ G
  N₁ = ≤-trans (proj₁ (proj₂ WR)) (proj₁ (proj₂ WK))
  N₂ : (j : NodeId) → nodeNestAt j st₁ ≤ nodeNestAt j st ⊔ G
  N₂ j = ≤-trans (proj₂ (proj₂ WR) j) (proj₂ (proj₂ WK) j)

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
abstract
  stepFrame-take-split : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (g : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame g id now (take-f nid) κ vals fin sched st in
    (nestDᵛˢ (proj₁ r) ≤ nestDᵛˢ vals)
    × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≤ nodesMax st)
    × (∀ (j : NodeId) →
         nodeNestAt j (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≤ nodeNestAt j st)
  stepFrame-take-split g id now nid κ vals fin sched st
    with lookupNode nid (EvalSt.nodes st) in eq
  ... | nothing                    = z≤n , ≤-refl , (λ j → ≤-refl)
  ... | just (scan-st _)           = z≤n , ≤-refl , (λ j → ≤-refl)
  ... | just (mergeAll-st _ _ _ _) = z≤n , ≤-refl , (λ j → ≤-refl)
  ... | just (switch-st _ _)       = z≤n , ≤-refl , (λ j → ≤-refl)
  ... | just (exhaust-st _ _)      = z≤n , ≤-refl , (λ j → ≤-refl)
  ... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
  ...   | true  =
        takeVals-nest k vals
        , ≤-trans (setNode-nodes nid (take-st zero) (EvalSt.nodes st))
                  (⊔-lub z≤n ≤-refl)
        , (λ j → lookupNode-set-same j nid (take-st zero) (take-st k)
                   (EvalSt.nodes st) eq ≤-refl)
  ...   | false =
        takeVals-nest k vals
        , ≤-trans (setNode-nodes nid
                     (take-st (proj₁ (proj₂ (takeVals k vals))))
                     (EvalSt.nodes st))
                  (⊔-lub z≤n ≤-refl)
        , (λ j → lookupNode-set-same j nid
                   (take-st (proj₁ (proj₂ (takeVals k vals)))) (take-st k)
                   (EvalSt.nodes st) eq ≤-refl)

pushBurst-nest-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ s t)
  (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  let r = pushBurst g id now (take-f nid) κ str sched st in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r)))
     ≤ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} str)))
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st)
pushBurst-nest-take g id now nid κ [] sched st =
  z≤n , ≤-refl , (λ j → ≤-refl)
pushBurst-nest-take {Γ = Γ} {t = t} {s = s} g id now nid κ (em ∷ ems) sched st =
  ≤-trans (nestDᵛˢ-++
             (proj₁ (splitEvents {A = Val Γ t}
               (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ sf))
                ++ map value (proj₁ sf)
                ++ (if proj₁ (proj₂ (proj₂ sf)) then complete ∷ [] else []))))
             (proj₁ (splitBurst {A = Val Γ t}
               (proj₁ (pushBurst g id now (take-f nid) κ ems sched₁ st₁)))))
    (⊔-lub (≤-trans (≤-reflexive (cong (nestDᵛˢ {u = s}) PEV))
                    (≤-trans (proj₁ STEP)
                      (≤-trans (≤-reflexive (cong (nestDᵛˢ {u = s})
                                 (splitEvents-vals-A {A = Val Γ s} {B = Val Γ t}
                                   (InstEmit.events em))))
                        (nestDᵛˢ-++ˡ
                          (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
                          (proj₁ (splitBurst {A = Val Γ t} ems))))))
           (≤-trans (proj₁ IH)
                    (nestDᵛˢ-++ʳ
                      (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
                      (proj₁ (splitBurst {A = Val Γ t} ems)))))
  , ≤-trans (proj₁ (proj₂ IH)) (proj₁ (proj₂ STEP))
  , (λ j → ≤-trans (proj₂ (proj₂ IH) j) (proj₂ (proj₂ STEP) j))
  where
  sp = splitEvents {A = Val Γ s} (InstEmit.events em)
  sf = stepFrame g id now (take-f nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ sf)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ sf)))
  STEP = stepFrame-take-split g id now nid κ (proj₁ sp)
           (proj₂ (proj₂ sp)) sched st
  IH = pushBurst-nest-take g id now nid κ ems sched₁ st₁
  PEV : proj₁ (splitEvents {A = Val Γ t}
          (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ sf))
           ++ map value (proj₁ sf)
           ++ (if proj₁ (proj₂ (proj₂ sf)) then complete ∷ [] else [])))
          ≡ proj₁ sf
  PEV = pushEmit-vals (InstEmit.events em) (proj₁ (proj₂ sf)) (proj₁ sf)
          (proj₁ (proj₂ (proj₂ sf)))

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
pushBurst-nest-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (κ : Path Γ u t) (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  let r = pushBurst g id now (map-f fn) κ str sched st in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r)))
     ≤ 2 ^ syncSizeᵗ fn
       * (nestDᵗ fn + nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} str))))
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st)
pushBurst-nest-map g id now fn κ [] sched st =
  z≤n , ≤-refl , (λ j → ≤-refl)
pushBurst-nest-map {Γ = Γ} {t = t} {s = s} {u = u} g id now fn κ (em ∷ ems) sched st =
  ≤-trans (nestDᵛˢ-++
             (proj₁ (splitEvents {A = Val Γ t}
               (proj₁ (proj₂ sp) ++ retagEvents {A = Val Γ t} []
                ++ map value (map (applyFn fn) (proj₁ sp))
                ++ (if proj₂ (proj₂ sp) then complete ∷ [] else []))))
             (proj₁ (splitBurst {A = Val Γ t}
               (proj₁ (pushBurst g id now (map-f fn) κ ems sched st)))))
    (⊔-lub (≤-trans (≤-reflexive (cong (nestDᵛˢ {u = u}) PEV))
                    (≤-trans (mapVals-nest-sync fn (proj₁ sp))
                             (*-monoʳ-≤ (2 ^ syncSizeᵗ fn)
                               (+-monoʳ-≤ (nestDᵗ fn)
                                 (≤-trans (≤-reflexive (cong (nestDᵛˢ {u = s})
                                            (splitEvents-vals-A
                                              {A = Val Γ u} {B = Val Γ t}
                                              (InstEmit.events em))))
                                   (nestDᵛˢ-++ˡ
                                     (proj₁ (splitEvents {A = Val Γ t}
                                              (InstEmit.events em)))
                                     (proj₁ (splitBurst {A = Val Γ t} ems))))))))
           (≤-trans (proj₁ IH)
                    (*-monoʳ-≤ (2 ^ syncSizeᵗ fn)
                      (+-monoʳ-≤ (nestDᵗ fn)
                        (nestDᵛˢ-++ʳ
                          (proj₁ (splitEvents {A = Val Γ t} (InstEmit.events em)))
                          (proj₁ (splitBurst {A = Val Γ t} ems)))))))
  , proj₁ (proj₂ IH)
  , proj₂ (proj₂ IH)
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  IH = pushBurst-nest-map g id now fn κ ems sched st
  PEV : proj₁ (splitEvents {A = Val Γ t}
          (proj₁ (proj₂ sp) ++ retagEvents {A = Val Γ t} []
           ++ map value (map (applyFn fn) (proj₁ sp))
           ++ (if proj₂ (proj₂ sp) then complete ∷ [] else [])))
          ≡ map (applyFn fn) (proj₁ sp)
  PEV = pushEmit-vals {B = Val Γ t} (InstEmit.events em) []
          (map (applyFn fn) (proj₁ sp)) (proj₂ (proj₂ sp))


-- THE QUEUE CONJUNCT IS THE CROSSING, AND IT IS ONE UNIT WIDE.  What
-- the room asks for is `suc (length q) ≤ cWid c` -- ROOM for the
-- arrival about to park -- while the caps invariant carries
-- `length q ≤ cWid c`.  That single unit is the whole gap, and it is
-- why this record is false at a FIXED cap and true at a stepping one:
-- the invariant at a cap gives the room at any STRICTLY wider one, and
-- one level of the frame step is exactly what buys a unit of width --
-- `iterFold-lift` says so, at `K` and `q` both zero, and the step's
-- width field IS that iterate.
--
-- SO THE CONJUNCT SHOULD NOT BE A PREMISE AT ALL.  Read at the level
-- above the one the caps boolean is held at, it is DERIVED -- from the
-- node reading `capsOK?` already carries, through the lookup -- and
-- the parked pair that kills this shape stops being expressible, since
-- what it crosses is a width the statement no longer names.  Threading the
-- strong reading down to here is what makes that derivation available,
-- and it is the same threading the arms beside this need to spend the
-- proven face.
-- THE ROOM THE WIDTH FIELD MUST STILL HAVE AT THE NODE THIS STEP
-- WRITES.  The invariant's node conjunct bounds a merge queue two ways
-- against ONE field -- every queued value's frame width, and the
-- queue's LENGTH -- while the premise on the arriving value bounds its
-- SIZE and nothing else.  The no-room arm appends, so a step handed a
-- value that premise admits can still push the length past the field,
-- and no fact about the value reaches a count of how many the node
-- already holds.  Hence a premise about the NODE, quantified over what
-- the table actually has there the way the drain's bundle already is.
--
-- AND THE WIDTH UNDER THE ARRIVAL'S OWN SUBSCRIBE, in the two states
-- an arm can reach it at.  The step's descent is granted at a key read
-- over the burst, so the width is an obligation on the ARRIVAL and
-- travels with it -- and the switch's arm subscribes at the state its
-- KILL leaves rather than the one handed in, which is a different
-- reading of the same measure and cannot be recovered from the first.
-- Quantifying over what the table holds is what the queue conjunct
-- above already does, and for the same reason: the arm that reaches
-- the second state is chosen by the node, not by the value.
--
-- REFUTED: Refuted.Thru-Step-Caps
thruRoom : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruRoom {n = n} {Γ = Γ} {u = u} c W fuel op nid κ id now o sched st =
  (pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c)
  × ((lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs u))) (od : Bool) →
       lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
       suc (length q) ≤ Caps.cWid c)
  × (innerW fuel op nid κ id now o sched st ≤ W)
  × ((cur : Maybe Id) (od : Bool) →
       lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od) →
       innerW fuel op nid κ id now o
         (proj₁ (proj₂ (switchKill cur sched st)))
         (proj₂ (proj₂ (switchKill cur sched st))) ≤ W)

-- and the same over a walk's arrivals, each at the state the previous
-- one left -- the shape `thruFitOK` already has, for the same reason
thruRoomOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruRoomOK c W fuel op nid κ id now [] sched st = ⊤
thruRoomOK c W fuel op nid κ id now (o ∷ os) sched st =
  thruRoom c W fuel op nid κ id now o sched st
  × thruRoomOK c W fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
  where rc = thruConsume fuel op nid κ id now o sched st

-- THE WIDTH HALF OF THE ROOM RECORD ON ITS OWN, because it is the half
-- no caps premise can supply.  A frame carries an op and node ids and
-- no syntax, so nothing read off the frame can see what a subscription
-- will descend into; both width conjuncts read the ARRIVAL through
-- `innerW`, once at the state handed in and once at the state a kill
-- leaves.  Splitting them out is what lets the burst record state them
-- where the arriving values are in scope, and leaves the queue and the
-- frame width to the caps side, which does read the state.
thruRoomW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruRoomW W fuel op nid κ id now o sched st =
  (innerW fuel op nid κ id now o sched st ≤ W)
  × ((cur : Maybe Id) (od : Bool) →
       lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od) →
       innerW fuel op nid κ id now o
         (proj₁ (proj₂ (switchKill cur sched st)))
         (proj₂ (proj₂ (switchKill cur sched st))) ≤ W)

-- and over a walk's arrivals, each at the state the previous one left
thruRoomWOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruRoomWOK W fuel op nid κ id now [] sched st = ⊤
thruRoomWOK W fuel op nid κ id now (o ∷ os) sched st =
  thruRoomW W fuel op nid κ id now o sched st
  × thruRoomWOK W fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
  where rc = thruConsume fuel op nid κ id now o sched st

-- AND THE QUEUE BOUND FOLDED THE SAME WAY, which the caps at the
-- frame's own state cannot supply and a refutation says so: the caps
-- admit a queue as long as the width field, and the record asks that
-- field for one more.  It is a claim about the node table and not
-- about a value, so it travels with the WALK rather than with an
-- arrival -- one reading per state the walk passes through, which is
-- the shape the drain's own bundle already has at the sibling frame.
thruRoomQOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (fuel : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) → Set
thruRoomQOK c fuel op nid κ id now [] sched st = ⊤
thruRoomQOK {Γ = Γ} {u = u} c fuel op nid κ id now (o ∷ os) sched st =
  ((lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs u))) (od : Bool) →
     lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     suc (length q) ≤ Caps.cWid c)
  × thruRoomQOK c fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
  where rc = thruConsume fuel op nid κ id now o sched st

-- the parking write on its own, caps half: the queue grows by one
-- arrival whose frame width the room record bounds, so the table's
-- width fold still passes.  Extracted so the measure-free walk below
-- and the measured step both spend it.
merge-park-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (nid : NodeId) (lim : Maybe ℕ) (act : ℕ)
  (q : List (Val Γ (obs u))) (od : Bool) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} lim act q od) →
  nestCapsOK? c sched st ≡ true →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  suc (length q) ≤ Caps.cWid c →
  nestCapsOK? c sched
    (record st { nodes = setNode nid (mergeAll-st {t = u} lim act (q ++ o ∷ []) od)
                   (EvalSt.nodes st) }) ≡ true
merge-park-caps {n = n} {u = u} c nid lim act q od o sched st eq hc hw hq =
  nestCapsOK?-setNode c nid ns sched st wn hc
  where
  ns = mergeAll-st {t = u} lim act (q ++ o ∷ []) od

  wn₀ : nodeWidᴺ? (Caps.cWid c) (Sched.slots sched)
          (mergeAll-st {t = u} lim act q od) ≡ true
  wn₀ = nestCapsOK?-lookupWid c nid _ sched st eq hc

  hlen : length (q ++ o ∷ []) ≤ Caps.cWid c
  hlen = ≤-trans (≤-reflexive (trans (length-++ q {o ∷ []})
                                     (+-comm (length q) 1))) hq

  wn : nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) ns ≡ true
  wn = ∧-intro
         (all-++-intro (λ x → pWᵉ n (Sched.slots sched) x ≤ᵇ Caps.cWid c)
            q (o ∷ [])
            (∧-trueˡ wn₀)
            (∧-intro (≤ᵇ-true _ _ hw) refl))
         (≤ᵇ-true _ _ hlen)

-- THE TWO ARMS A MERGE'S STEP HAS, and they are the whole of it: the
-- limit has room and the arrival is SUBSCRIBED, or it is spent and the
-- arrival is PARKED.  Every other way into `thruConsume` -- no node at
-- the id, a node of another shape, a node carrying another element
-- type -- returns its inputs untouched, so all five conjuncts are the
-- hypotheses back and the body below discharges them rather than
-- asserting them.
--
-- THE PARK ARM CARRIES THREE, not five: the burst is empty there and
-- the schedule is the one that came in, so the two conjuncts about
-- them are `z≤n` and a hypothesis.  Stating a leaf over what it
-- actually owes is what keeps the fit CHECKED when it lands.
--
-- AND THE ROOM PREMISE IS WHY THE QUEUE LENGTH IS IN THE TELESCOPE.
-- The caller's room record quantifies over the node it finds at the
-- id, so once the step has matched that node the record is spent and
-- what is left is the one number it yielded.  Passing the number
-- rather than the record is not a weakening: it is the same fact with
-- the match already made, and it is what lets this leaf be stated
-- without naming `thruConsume` at all.
-- REFUTED: `Refuted.Thru-Step-Caps` is why that premise is there at
--   all -- the node conjunct COUNTS the queue as well as measuring it,
--   so the parking arm overflows a field the arrival fits in exactly.
thruStep-merge-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (nid : NodeId)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs u))) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} lim act q od) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  suc (length q) ≤ Caps.cWid c →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  let st′ = record st
              { nodes = setNode nid (mergeAll-st {t = u} lim act (q ++ o ∷ []) od)
                          (EvalSt.nodes st) }
      G′  = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nodesMax st′ ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) → nodeNestAt j st′ ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c sched st′ ≡ true)
thruStep-merge-park {n = n} {Γ = Γ} {e = e} {u = u}
  c sl B W m m′ nid lim act q od o sched st eq hsl hm hc hv hw hq hn =
  c1 , c2 , merge-park-caps c nid lim act q od o sched st eq hc hw hq
  where
  ns₀ = mergeAll-st {t = u} lim act q od
  ns  = mergeAll-st {t = u} lim act (q ++ o ∷ []) od
  G′  = nestB (Caps.cSize c) W (nestUnit e sl) B m′

  -- the arrival is inside the grant the STEP promises, which is the
  -- one the caller reads at `m′`; the queue it joins was inside the
  -- table's own maximum already
  oG : nestDᵛ (obs u) o ≤ G′
  oG = ≤-trans hn (nestB-mono (Caps.cSize c) W (nestUnit e sl) B
                     (≤-trans (n≤1+n m) hm))

  qapp : nodeNest ns ≤ nodeNest ns₀ ⊔ G′
  qapp = ≤-trans (nestDᵛˢ-++ q (o ∷ []))
                 (⊔-mono-≤ ≤-refl (⊔-lub oG z≤n))

  c1 : nodesMax (record st { nodes = setNode nid ns (EvalSt.nodes st) })
         ≤ nodesMax st ⊔ G′
  c1 = ≤-trans (setNode-nodes nid ns (EvalSt.nodes st))
         (⊔-lub (≤-trans qapp
                   (⊔-mono-≤ (lookupNode-nodes nid ns₀ (EvalSt.nodes st) eq) ≤-refl))
                (m≤m⊔n _ _))

  atSelf : (j : NodeId) → nid ≡ j →
    maybe nodeNest 0 (lookupNode j (setNode nid ns (EvalSt.nodes st)))
      ≤ maybe nodeNest 0 (lookupNode j (EvalSt.nodes st)) ⊔ G′
  atSelf j refl =
    ≤-trans (≤-reflexive (cong (maybe nodeNest 0)
               (lookupNode-setNode nid ns (EvalSt.nodes st))))
            (≤-trans qapp
               (⊔-mono-≤ (≤-reflexive (sym (cong (maybe nodeNest 0) eq))) ≤-refl))

  -- A WRITE IS INVISIBLE AT EVERY OTHER KEY, and the pointwise
  -- conjunct needs that rather than `lookupNode-set-at`: that bound
  -- charges every reading the written node's own nesting, which at a
  -- key the write did not touch would demand the arrival's cap fit
  -- inside the grant, and nothing supplies that.
  c2 : (j : NodeId) →
    nodeNestAt j (record st { nodes = setNode nid ns (EvalSt.nodes st) })
      ≤ nodeNestAt j st ⊔ G′
  c2 j with nid ≡ᵇ j in ej
  ... | true  = atSelf j (≡ᵇ→≡ nid j ej)
  ... | false = ≤-trans (≤-reflexive (cong (maybe nodeNest 0)
                           (lookupNode-setNode-other j nid ns (EvalSt.nodes st) ej)))
                        (m≤m⊔n _ _)


-- A BUMP IS NOT A WRITE, as far as this face can see.  `mergeAllBump`
-- re-reads the node and puts back the same queue under a different
-- live count, and `nodeNest` reads the QUEUE -- so every reading of the
-- table is unchanged, at the bumped key and everywhere else.
abstract
  bump-at : ∀ {n} {Γ : Ctx n} (j nid : NodeId) (d : Bool)
    (ns : List (NodeId × NodeState Γ)) →
    maybe nodeNest 0 (lookupNode j (mergeAllBump nid d ns))
      ≤ maybe nodeNest 0 (lookupNode j ns)
  bump-at j nid d ns with lookupNode nid ns in eq
  ... | nothing                       = ≤-refl
  ... | just (scan-st _)              = ≤-refl
  ... | just (take-st _)              = ≤-refl
  ... | just (switch-st _ _)          = ≤-refl
  ... | just (exhaust-st _ _)         = ≤-refl
  ... | just (mergeAll-st lim act q od) with nid ≡ᵇ j in ej
  ...   | false = ≤-reflexive
                    (cong (maybe nodeNest 0)
                       (lookupNode-setNode-other j nid _ ns ej))
  ...   | true  rewrite sym (≡ᵇ→≡ nid j ej)
                      | lookupNode-setNode nid
                          (mergeAll-st lim (if d then act else suc act) q od) ns
                      | eq = ≤-refl

  bump-fold : ∀ {n} {Γ : Ctx n} (nid : NodeId) (d : Bool)
    (ns : List (NodeId × NodeState Γ)) →
    nodesFold (mergeAllBump nid d ns) ≤ nodesFold ns
  bump-fold nid d ns with lookupNode nid ns in eq
  ... | nothing               = ≤-refl
  ... | just (scan-st _)      = ≤-refl
  ... | just (take-st _)      = ≤-refl
  ... | just (switch-st _ _)  = ≤-refl
  ... | just (exhaust-st _ _) = ≤-refl
  ... | just (mergeAll-st lim act q od) =
        ≤-trans (setNode-nodes nid _ ns)
                (⊔-lub (lookupNode-nodes nid (mergeAll-st lim act q od) ns eq)
                       ≤-refl)

-- THE SYNC SPINE IS NEVER EMPTY, so its predecessor is a real index:
-- every clause of `syncSizeᵉ` is either the literal one or a `suc`, and
-- a term with no boundary at all still counts its own head.  What the
-- step spends this for is the frame charge, whose exponent must sit
-- STRICTLY under the cap while the premise available bounds the spine
-- by it -- one boundary of the arrival is the subscription itself,
-- which crosses without duplicating anything.
abstract
  syncSizeᵉ-suc-pred : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (x : Exp Γ Δᵍ Δ Θ t) →
    suc (pred (syncSizeᵉ x)) ≡ syncSizeᵉ x
  syncSizeᵉ-suc-pred (input i)         = refl
  syncSizeᵉ-suc-pred (ofᵉ ts)          = refl
  syncSizeᵉ-suc-pred emptyᵉ            = refl
  syncSizeᵉ-suc-pred (mapᵉ f x)        = refl
  syncSizeᵉ-suc-pred (takeᵉ c x)       = refl
  syncSizeᵉ-suc-pred (scanᵉ f z x)     = refl
  syncSizeᵉ-suc-pred (mergeAllᵉ lim x) = refl
  syncSizeᵉ-suc-pred (switchAllᵉ x)    = refl
  syncSizeᵉ-suc-pred (exhaustAllᵉ x)   = refl
  syncSizeᵉ-suc-pred (μᵉ x)            = refl
  syncSizeᵉ-suc-pred (varᵉ x)          = refl
  syncSizeᵉ-suc-pred (deferᵉ x)        = refl

-- THE DESCENT READ AGAINST ITS ARRIVAL, which is the one thing neither
-- proven subscribe bound supplies.  Both of those are stated as a whole
-- GRANT keyed on
-- the descent -- flattened at the cap for the drain, tight at the
-- arrival's own spine for the recursive head -- and a step that must
-- land ONE level above its body can absorb neither, since both spend a
-- factor per level where the step has exactly one level to spend.
--
-- WHAT A STEP CAN ABSORB IS A BASE-TWO CHARGE PER BOUNDARY, which is
-- both what `nestB-frame-dbl` takes and what the substitution actually
-- costs: a frame naming its payload twice delivers twice what it
-- received, once per boundary crossed, and the arrival's own sync size
-- counts those boundaries.  The additive half is the program's nesting
-- unit, which is what one installed node contributes and is under the
-- grant at every index.
--
-- AND THE WIDTH PREMISE IS ABSENT DELIBERATELY: both measures in the
-- conclusion are `⊔`-folds over depths, so how MANY values a burst
-- carries does not enter, and a premise the conclusion cannot mention
-- would be satisfiable at any width and assert nothing.
-- THE DESCENT AT THE ARRIVAL'S OWN SIZE, which is the shape the
-- consume steps need and the one the cap-keyed descent deliberately
-- does not have.  `arrD` charges two per UNIT of term size rather
-- than a whole per-level factor per boundary, and `syncSizeᵉ` is a
-- full term size -- a map's own function counts -- so every clause
-- has exactly the factor its frame charges and no more.  That is why
-- the frame law here needs no premise relating the frame to the cap:
-- the exponent and the frame's size are the same quantity.
-- REFUTED: Refuted.Thru-Step-Nest
-- DEAD ROUTE: spending the proven subscribe bound is STRUCTURALLY
--   DEAD, and it is the route the indexed shape most invites, so it is
--   worth killing here rather than at the third attempt.  That bound
--   FLATTENS the descent at the cap -- deliberately, because the drain
--   it serves walks a queue and wants ONE exponent rather than one per
--   element -- so what it delivers over an arrival bounded by the
--   grant at `m` is the grant at the CAP over that base.  One step of
--   the key affords one factor; the flattened bound spends a factor
--   per level up to the cap, and the two differ by every level between
--   `suc m` and the cap.  No choice of base closes it, the base being
--   what both sides are read over.  What the step needs is a subscribe
--   bound keyed on the ARRIVAL's own sync size, which is the shape the
--   recursive head already has and the drain's deliberately does not.
-- DEAD ROUTE: and the TIGHT bound does not close it either, which is
--   the more useful half because it says what the residue is.  Spending
--   it puts the arrival's own bound in as the base, so the delivery is
--   the grant at the arrival's sync size OVER the grant at `m` -- two
--   grants stacked.  Composing them adds the keys and costs a `suc`, so
--   what comes out sits at `suc (m + syncSizeᵉ o)` and the statement is
--   read at `m′`.  At the caller `m′` is `suc m`, so the route closes
--   only when the emitted arrival carries NO boundary of its own, which
--   is not the general case.  What this does NOT show is that the
--   caller's grant is too small: the composition is the worst case of a
--   bound that flattens, and the measured delivery doubles per level
--   where the composition charges a full factor.  The gap is the
--   subscribe bound's slack, so the residue is a delivery bound tight
--   in the arrival rather than a bigger grant.
NestArrAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Set
NestArrAt {Γ = Γ} {t = t} {e = e} c sl B W g o κ id now sched st =
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs _) o ≡ true →
  -- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, which is the premise this
  -- face was always owed and the cap-keyed one already carries: the
  -- key here is READ THROUGH THE TELESCOPE, so a premise stated on the
  -- written size says nothing at `input i`, where the size is one and
  -- the walk re-enters on a definition of any size at all.
  nestClosOK? c sl o ≡ true →
  nestDᵉ o ≤ B →
  -- AND THE WIDTH PREMISE IS NOT ABSENT, WHICH IT USED TO BE.  The
  -- reading it was absent under is that both conclusions are `⊔`-folds
  -- over depths, so how MANY values a burst carries cannot enter --
  -- true of the conclusion and false of the DEMAND, since a fold
  -- multiplies the delivered depth once per value while the key gains
  -- only what that value costs to write down.  Measured, the two rates
  -- are independent and the margin closes; the scan head's own header
  -- carries the rows.  So the key is read at the width as well, which
  -- is the same premise the cap-keyed family has always taken.
  descW g o κ id now sched st ≤ W →
  let r = subscribeE g o κ id now sched st
      D = arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) o) in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ D)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ D)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st ⊔ D)

-- a size is positive at every head, which is the one thing the frame
-- law asks and the one thing no clause has to establish
syncSizeᵉ-pos : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (x : Exp Γ Δᵍ Δ Θ t) →
  1 ≤ syncSizeᵉ x
syncSizeᵉ-pos x = ≤-trans (s≤s z≤n) (≤-reflexive (syncSizeᵉ-suc-pred x))

-- and the same step read as an inequality, which is what a key whose
-- positivity comes from a DOMINATION rather than from its own clauses
-- can supply
suc-pred-≤ : ∀ {x : ℕ} → 1 ≤ x → suc (pred x) ≤ x
suc-pred-≤ {suc _} _ = ≤-refl

postulate
  -- THE HEADS THIS DESCENT STILL OWES.  Each is the arr-keyed twin of
  -- a clause the cap-keyed descent already discharges, so what is open
  -- is the transport and not the shape.
  -- THE SCAN HEAD, WHICH IS WHERE THE BURST LENGTH IS REALLY BET.  A
  -- scan's step is written once and applied once per value of the burst
  -- it is fed, so the delivered depth is MULTIPLIED once per value
  -- while the key gains only what that value costs to write down.  Both
  -- rates are properties of the program and neither bounds the other,
  -- which is why the grant is read over `suc W` copies of the key
  -- rather than over the key alone: the product puts the WIDTH in the
  -- exponent, so the grant grows quadratically in the value count where
  -- the demand gains a fixed two bits each, and the head does not have
  -- to win the race on the step function's written size alone.
  --
  -- REFUTED: `Refuted.Scan-Arr-Nest` kills the reading that charges a
  --   script nothing -- 16383 delivered against 6144, at a fourteen-value
  --   cold script, the row one value shorter holding against the SAME
  --   charge, so it is a crossing and not a scale error.  What the same
  --   file pins beside it is the quantity that replaces it: twelve at no
  --   values and forty at fourteen, a term in the delivered length
  --   exactly where the demand has one.
  -- PROBED: `Probed.Scan-Arr-Clos-Key` reads THIS form at that witness,
  --   the fit holding at zero, seven, thirteen and fourteen values with
  --   the key rising two per value against a delivery that doubles -- so
  --   the grant doubles twice per value and the margin widens along the
  --   axis that produced the refutation.  Not covered: a script of
  --   OBSERVABLE values, which charges both sides and is not read here,
  --   and the interaction with a substituting slot, the telescope there
  --   being scripted throughout.
  -- PROBED: `Probed.Scan-Arr-Margin` takes the axis that receipt holds
  --   still -- how fast the STEP duplicates rather than how long the
  --   script is -- at four accumulator copies over an `ofᵉ` source of
  --   bare naturals, the worst pairing the family offers: delivered 0,
  --   2, 10, 42, 170 and on to 43690, against keys of 19, 115 and 243
  --   bits at zero, four and eight values.  Covered LOAD-BEARING: the
  --   value conjunct at that family, and the SIGN of the margin --
  --   read at the arrival alone the exponent is flat in the width and
  --   every row past the head start fails, which is what forced the
  --   width in.  The width is pinned as the burst's own length, a
  --   lower bound on the sealed measure, and the grant is monotone in
  --   it.  NOT covered: a source whose key gains nothing per value,
  --   and the interaction with a substituting slot, whose key is read
  --   through the telescope rather than off the term.
  subscribeE-nest-arr-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u) (b : Closed Γ s)
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestArrAt c sl B W g (scanᵉ f z b) κ id now sched st

  -- THE WALL THE THREE BOUNDARY HEADS CROSS, and it is now the whole
  -- of what they owe: the clause below each of these is a checked body
  -- that recurses on the definition and pushes the burst, so what is
  -- asserted here is the emit-by-emit FIT at the arr key and nothing
  -- else.  The cap-keyed face reads its own fit off `pushVals-*`
  -- through `pushFit-ems`; the arr key is not a `nestB`, so that route
  -- does not transport and the fit is stated directly.
  --
  -- PROBED: `Probed.Thru-Step-Indexed` takes the one axis on which the
  --   two sides move at comparable rates -- the arrival's own term, where
  --   the delivery is whatever the substitution emits.  Nesting a
  --   duplicating step delivers two, four and eight against arrivals of
  --   two, three and four, every fit inside the grant and both premises
  --   pinned by `refl`, which is the DOUBLING PER BOUNDARY these leaves
  --   charge for.  Covered LOAD-BEARING: the value conjunct at that
  --   family, read at a grant BELOW this one -- the rows take the key
  --   at one copy where the width premise buys `suc W` of them, so a
  --   fit there is a fit here.
  -- PROBED: `Probed.Thru-Arr-Slot` takes the region that receipt names
  --   as open -- a SUBSTITUTING SLOT, where the key is read through the
  --   telescope rather than off the term -- at the very witness that
  --   killed the cap-keyed sibling.  Covered LOAD-BEARING: the value
  --   conjunct at four layers and all three operators, the key rising
  --   about fifteen per layer against a delivery that doubles, so the
  --   margin widens along the axis that produced that refutation: four
  --   against eight there, one hundred and eighty quadrillion against
  --   eight here.  NOT covered: a telescope deepening without
  --   lengthening, which no head in this language writes, and the two
  --   STORE conjuncts, weaker than the value one at the same grant.
  thruFit-arr-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (lim : Maybe ℕ)
    (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (mergeAllᵉ lim b) ≡ true →
    nestClosOK? c sl (mergeAllᵉ lim b) ≡ true →
    nestDᵉ (mergeAllᵉ lim b) ≤ B →
    descW g (mergeAllᵉ lim b) κ id now sched st ≤ W →
    let res = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
                id now (proj₂ (mintNode sched))
                (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st)
    in pushFitOK (arrD (nestUnit e sl) B
                    (suc W * closSizeᵉ (slotClos sl) (mergeAllᵉ lim b)))
         g mergeAllᵒ (proj₁ (mintNode sched)) κ id now
         (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  -- PROBED: `Probed.Thru-Step-Indexed`, whose coverage is stated at
  --   `thruFit-arr-merge` above.
  -- PROBED: `Probed.Thru-Arr-Slot`, likewise stated there.
  thruFit-arr-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (switchAllᵉ b) ≡ true →
    nestClosOK? c sl (switchAllᵉ b) ≡ true →
    nestDᵉ (switchAllᵉ b) ≤ B →
    descW g (switchAllᵉ b) κ id now sched st ≤ W →
    let res = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
                id now (proj₂ (mintNode sched))
                (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
    in pushFitOK (arrD (nestUnit e sl) B
                    (suc W * closSizeᵉ (slotClos sl) (switchAllᵉ b)))
         g switchᵒ (proj₁ (mintNode sched)) κ id now
         (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  -- PROBED: `Probed.Thru-Step-Indexed`, whose coverage is stated at
  --   `thruFit-arr-merge` above.
  -- PROBED: `Probed.Thru-Arr-Slot`, likewise stated there.
  thruFit-arr-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (exhaustAllᵉ b) ≡ true →
    nestClosOK? c sl (exhaustAllᵉ b) ≡ true →
    nestDᵉ (exhaustAllᵉ b) ≤ B →
    descW g (exhaustAllᵉ b) κ id now sched st ≤ W →
    let res = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
                id now (proj₂ (mintNode sched))
                (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
    in pushFitOK (arrD (nestUnit e sl) B
                    (suc W * closSizeᵉ (slotClos sl) (exhaustAllᵉ b)))
         g exhaustᵒ (proj₁ (mintNode sched)) κ id now
         (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))


-- A PLUMBING RETAG REWRITES `kind`, WHICH THE SPLIT NEVER READS, so a
-- connect's adopted burst delivers exactly the values the definition's
-- own subscribe did.
splitBurst-plumb : ∀ {n} {Γ : Ctx n} {u} {A : Set} (str : Stream Γ u) →
  proj₁ (splitBurst {A = A} (sharedPlumb str))
  ≡ proj₁ (splitBurst {A = A} str)
splitBurst-plumb []         = refl
splitBurst-plumb (em ∷ ems) =
  cong (proj₁ (splitEvents (InstEmit.events em)) ++_) (splitBurst-plumb ems)

-- AND A WHOLE BURST INHERITS THAT, one emit's value column at a time
-- -- which is what lets a bound taken by one face be read by another
-- that picked a different bookkeeping type for the same subscription.
splitBurst-vals-A : ∀ {n} {Γ : Ctx n} {u} {A B : Set} (str : Stream Γ u) →
  proj₁ (splitBurst {A = A} str) ≡ proj₁ (splitBurst {A = B} str)
splitBurst-vals-A []         = refl
splitBurst-vals-A (em ∷ ems) =
  cong₂ _++_ (splitEvents-vals-A (InstEmit.events em)) (splitBurst-vals-A ems)

-- WHAT A SUBSCRIBE OWES, AS ONE NAME OVER ITS WHOLE RESULT.  The walk's
-- three conjuncts are read off one triple, and an arm that EXITS two
-- ways has to state them twice; naming them once is what lets the two
-- exits be discharged as the same obligation at two triples.
NestOut : ∀ {n} {Γ : Ctx n} {t} {u} {e : Closed Γ t} →
  ℕ → EvalSt e → Stream Γ u × Sched Γ × EvalSt e → Set
NestOut {Γ = Γ} {t = t} D st R =
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ R))) ≤ D)
  × (nodesMax (proj₂ (proj₂ R)) ≤ nodesMax st ⊔ D)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ R)) ≤ nodeNestAt j st ⊔ D)

-- and a branch owes it at whichever triple it took
nestOut-if : ∀ {n} {Γ : Ctx n} {t} {u} {e : Closed Γ t}
  (D : ℕ) (st : EvalSt e) (bc : Bool)
  (X Y : Stream Γ u × Sched Γ × EvalSt e) →
  NestOut {t = t} D st X → NestOut {t = t} D st Y →
  NestOut {t = t} D st (if bc then X else Y)
nestOut-if D st true  X Y hx hy = hx
nestOut-if D st false X Y hx hy = hy

-- THE SHARED ARM, and it is the whole of what the slot head owes --
-- the scripted arms need nothing, since `isData` excludes `obs` and
-- a script therefore has no depth to deliver at all.
--
-- THE KEY EXPANDS THE SLOT, and that is the whole content of the
-- restatement.  A share re-enters the walk on its definition, so
-- whatever key the head spends at `input i` must DOMINATE the key
-- the walk spends at `d` -- and the arrival's own written size
-- there is ONE, however large the definition behind it.  The
-- additive reading of that gap does not survive: a definition that
-- SUBSTITUTES builds what it emits, one occurrence in the step
-- function and one in the source it maps over, so a subscribe
-- doubles per layer while `nestDᵉ`, a subterm measure, rises by one.
-- Nor was there room in `B`, the head's own premise being
-- `nestDᵉ o ≤ B` at `o = input i`, which is zero.
--
-- WHAT PAYS FOR IT is that the doubling is BOUGHT rather than free:
-- a layer that duplicates also enlarges the definition it duplicates
-- in, measured at fifteen units of synchronous size per doubling, so
-- a key keyed on the DEFINITION's size outruns the delivery from the
-- first row.  `Rx.Slot-Clos.slotClos` is that key, and its fixpoint
-- hands this arm exactly one step of it over the descent it calls --
-- `slotClos sl i` is one MORE than the definition's closure size.
--
-- AND THE CALLER'S `B` IS GONE FROM THE GRANT, which is the content
-- of the restatement rather than a tidy-up.  A slot handoff does not
-- descend into the arrival, it LEAVES it: the caller's additive term
-- bounds the depth of a term the walk is about to stop looking at,
-- and what the descent on the definition needs is a term bounding
-- the DEFINITION's depth.  The unit is that term -- the telescope's
-- nesting is one of its summands -- and the one step of key the
-- slot's closure holds over the definition's pays for the swap
-- exactly, which is what `arrD-slot` is.
--
-- AND THE SLOT PREMISE IS NOT CALL-SITE CONVENIENCE.  The grant is
-- read over the UNIT, whose telescope summand pays for exactly the
-- definitions the telescope holds, so a connect on a definition the
-- slots do NOT hold is granted nothing by that term at all.  Without
-- the premise the statement is false rather than merely unprovable,
-- which is the one justification a hypothesis has.
--
-- A CONSTANT SHIFT OF THE KEY COULD NOT HAVE BEEN IT, which is worth
-- keeping because it is the first thing to try and it is decidably
-- wrong: shift every key by the same term and the two sides shift
-- together, `1 + c` against `syncSizeᵉ d + c`.
-- REFUTED: `Refuted.Shared-Slot-Nest-Arr`, which is what killed the
--   additive form -- at a four-layer substituting definition it
--   delivers `1 2 4 8` against a grant of `2 3 4 5`, crossing at the
--   third layer, and it reaches the head's own conclusion as well as
--   this arm's.  The same module takes the CONTAINED family at the
--   same four programs, `0 1 2 3` against the same grant, so the
--   additive form was right about containment and wrong about
--   substitution.  Neither reading survives a key of one, which is
--   the quantity that moved.
-- RECOVERY: git show 98665c7 restores the three probe families this
--   arm was carried on -- `Probed.Shared-Slot-Clos-Key` (the
--   substituting and contained layer families), `.Telescope` (a
--   two-slot environment, the only shape where the staged key does
--   work) and `.Script-Below` (a fold over a scripted slot beneath a
--   shared one).  Their coverage is superseded by the body below;
--   the harness is what a later arr-keyed statement would want back.
sharedConnect-nest-arr : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas) (i : Fin n)
  (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)}
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sl i ≡ shared d {ok = ok} →
  nestCapsOK? c sched st ≡ true →
  suc (closSizeᵉ (slotClos sl) d) ≤ Caps.cSize c →
  connW g i d κ id now sched st ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = sharedConnect g i d κ id now sched st
      D = arrD (nestUnit e sl) (nestUnit e sl)
            (suc W * closSizeᵉ (slotClos sl) d) in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ D)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ D)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st ⊔ D)

-- THE SLOT HEAD SPLITS THREE WAYS, AND TWO OF THEM OWE NOTHING.  A
-- share that has already completed replays a close in one instant, and
-- a share that is already connected joins mid-flight: neither carries a
-- value, so the delivered depth is zero, and neither touches the node
-- table -- `register` writes the registry and the counter beside it, so
-- `nodesMax` and `nodeNestAt` read the same list they read before.  The
-- whole of what this head owes is the CONNECT arm, which re-enters the
-- walk on the definition, and that is what the leaf is.
subscribeSharedSlot-nest-arr : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (i : Fin n)
  (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)}
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → sl i ≡ shared d {ok = ok} →
  nestCapsOK? c sched st ≡ true →
  suc (closSizeᵉ (slotClos sl) d) ≤ Caps.cSize c →
  connW g i d κ id now sched st ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = subscribeSharedSlot g i d κ id now sched st
      D = arrD (nestUnit e sl) B (suc W * suc (closSizeᵉ (slotClos sl) d)) in
  (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ D)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ D)
  × (∀ (j : NodeId) → nodeNestAt j (proj₂ (proj₂ r)) ≤ nodeNestAt j st ⊔ D)
subscribeSharedSlot-nest-arr {e = e} c sl B W g i d κ id now sched st
                             hsl hsi hc hk hw
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
... | false
  with memberSource (toℕ i) (EvalSt.connectedShares st)
... | true  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
... | false =
  ≤-trans (proj₁ L) step
  , ≤-trans (proj₁ (proj₂ L)) (⊔-mono-≤ ≤-refl step)
  , (λ j → ≤-trans (proj₂ (proj₂ L) j) (⊔-mono-≤ ≤-refl step))
  where
  L = sharedConnect-nest-arr c sl W g i d κ id now sched st hsl hsi hc hk hw

  step : arrD (nestUnit e sl) (nestUnit e sl) (suc W * closSizeᵉ (slotClos sl) d)
       ≤ arrD (nestUnit e sl) B (suc W * suc (closSizeᵉ (slotClos sl) d))
  step = arrDW-slot (nestUnit e sl) B W (closSizeᵉ (slotClos sl) d)
           (≤-trans (syncSizeᵉ-pos d)
                    (syncSize≤closᵉ (slotClos sl) (slotClos-pos sl) d))


subscribeE-nest-arr : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  NestArrAt c sl B W g o κ id now sched st
-- A SLOT SUBSCRIPTION READS THE TELESCOPE RATHER THAN DESCENDING, so
-- there is no key to spend and the additive half of the grant is what
-- has to cover it.  That is exactly the difference from the cap-keyed
-- form, which multiplies by an arrival whose `nestDᵉ` is zero here and
-- so charges nothing at all.
subscribeE-nest-arr c sl B W g (input i) κ id now sched st hsl hc hv hcl hn hw
  with Sched.slots sched i in eqs
... | shared d
  rewrite slotClos-fix sl i (trans (sym (cong (λ f → f i) hsl)) eqs) =
  subscribeSharedSlot-nest-arr c sl B W g i d κ id now sched st hsl
    (trans (sym (cong (λ f → f i) hsl)) eqs) hc (≤ᵇ⇒≤ _ _ (T-to hcl))
    (≤-trans (descW-conn g i d κ id now sched st eqs) hw)
... | scripted {ok = ok} (hot _)
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
... | false = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest-arr {Γ = Γ} c sl B W g (input i) κ id now sched st
                    hsl hc hv hcl hn hw
    | scripted {ok = ok} (cold sync []) =
  ≤-trans (≤-reflexive
            (trans (cong (nestDᵛˢ {u = lookup Γ i}) (oneShot-vals sync id sched))
                   (nestDᵛˢ-data ok sync))) z≤n
  , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest-arr {Γ = Γ} {t = t} c sl B W g (input i) κ id now sched st
                    hsl hc hv hcl hn hw
    | scripted {ok = ok} (cold sync (dl ∷ ds)) =
  ≤-trans (≤-reflexive
            (trans (cong (nestDᵛˢ {u = lookup Γ i})
                     (initHead-vals {A = Val Γ t} sync id
                        (proj₁ (mintSource sched))))
                   (nestDᵛˢ-data ok sync))) z≤n
  , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)

subscribeE-nest-arr {Γ = Γ} {t = t} {e = e} {u = u} c sl B W g (ofᵉ ts) κ id now sched st
  hsl hc hv hcl hn hw =
  ≤-trans (≤-reflexive (cong (nestDᵛˢ {u = u})
             (oneShot-vals {A = Val Γ t} (map (λ tm → evalTm tm) ts) id sched)))
    (≤-trans (≤-trans (ofVals-nest-sync ts) (*-monoʳ-≤ (2 ^ syncSizeᵗˢ ts) hn))
             (arrDW-flat (nestUnit e sl) B W (syncSizeᵗˢ ts)
               (closSizeᵗˢ (slotClos sl) ts)
               (≤-trans (syncSize≤closᵗˢ (slotClos sl) (slotClos-pos sl) ts)
                        (arrDW-key W (closSizeᵗˢ (slotClos sl) ts)))))
  , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest-arr c sl B W g emptyᵉ κ id now sched st hsl hc hv hcl hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest-arr {e = e} c sl B W g (mapᵉ f b) κ id now sched st
                    hsl hc hv hcl hn hw =
  ≤-trans (proj₁ push)
    (≤-trans (*-monoʳ-≤ (2 ^ syncSizeᵗ f) (+-mono-≤ hfB (proj₁ IH)))
             (arrDW-frame (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
               (syncSizeᵗ f) (closSizeᵗ (slotClos sl) f)
               (≤-trans (syncSizeᵉ-pos b) (clos-b))
               (m≤n+m B (nestUnit e sl))
               (≤-trans (syncSize≤closᵗ (slotClos sl) (slotClos-pos sl) f)
                        (arrDW-key W (closSizeᵗ (slotClos sl) f)))))
  , ≤-trans (proj₁ (proj₂ push))
      (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow))
  , (λ j → ≤-trans (proj₂ (proj₂ push) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow)))
  where
  res = subscribeE g b (map-f f ↠ κ) id now sched st

  push = pushBurst-nest-map g id now f κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH = subscribeE-nest-arr c sl B W g b (map-f f ↠ κ) id now sched st
         hsl hc (nestValOK?-map c f b hv)
         (nestClosOK?-mono c sl b (mapᵉ f b)
            (≤-trans (m≤n+m _ _) (n≤1+n _)) hcl)
         (≤-trans (m≤n+m (nestDᵉ b) (nestDᵗ f)) hn)
         (≤-trans (descW-map g f b κ id now sched st) hw)

  hfB : nestDᵗ f ≤ B
  hfB = ≤-trans (m≤m+n (nestDᵗ f) (nestDᵉ b)) hn

  clos-b : syncSizeᵉ b ≤ closSizeᵉ (slotClos sl) b
  clos-b = syncSize≤closᵉ (slotClos sl) (slotClos-pos sl) b

  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) b)
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (mapᵉ f b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
           (closSizeᵉ (slotClos sl) (mapᵉ f b))
           (≤-trans (n≤1+n _)
                    (s≤s (m≤n+m (closSizeᵉ (slotClos sl) b)
                                (closSizeᵗ (slotClos sl) f))))
subscribeE-nest-arr {e = e} c sl B W g (takeᵉ cnt b) κ id now sched st
                    hsl hc hv hcl hn hw
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
  inv₀ = nestCapsOK?-setNode c nid (take-st (suc k)) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  push = pushBurst-nest-take g id now nid κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH = subscribeE-nest-arr c sl B W g b (take-f nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-take c cnt b hv)
         (nestClosOK?-mono c sl b (takeᵉ cnt b)
            (≤-trans (m≤n+m _ _) (n≤1+n _)) hcl)
         hn
         (≤-trans (descW-take g cnt b κ id now sched st k eqc) hw)

  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (take-st (suc k)) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (take-st (suc k)) st)
                    (⊔-lub z≤n ≤-refl)

  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) b)
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (takeᵉ cnt b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
           (closSizeᵉ (slotClos sl) (takeᵉ cnt b))
           (≤-trans (m≤n+m (closSizeᵉ (slotClos sl) b)
                           (closSizeᵗ (slotClos sl) cnt))
                    (n≤1+n _))
subscribeE-nest-arr c sl B W g (scanᵉ f z b) κ id now sched st =
  subscribeE-nest-arr-scan c sl B W g f z b κ id now sched st
subscribeE-nest-arr {e = e} {u = u} c sl B W g (mergeAllᵉ lim b) κ id now sched st
                    hsl hc hv hcl hn hw =
  proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (mergeAll-st {t = u} lim 0 [] false) st
  res    = subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (mergeAll-st {t = u} lim 0 [] false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH = subscribeE-nest-arr c sl B W g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-merge c lim b hv)
         (nestClosOK?-mono c sl b (mergeAllᵉ lim b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-merge g lim b κ id now sched st) hw)

  FIT = thruFit-arr-merge c sl B W g lim b κ id now sched st hsl hc hv hcl hn hw

  PUSH = pushBurst-nest-thru
           (arrD (nestUnit e sl) B
              (suc W * closSizeᵉ (slotClos sl) (mergeAllᵉ lim b)))
           g mergeAllᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT

  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (mergeAll-st {t = u} lim 0 [] false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (mergeAll-st {t = u} lim 0 [] false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) b)
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (mergeAllᵉ lim b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
           (closSizeᵉ (slotClos sl) (mergeAllᵉ lim b)) (n≤1+n _)
subscribeE-nest-arr {e = e} {u = u} c sl B W g (switchAllᵉ b) κ id now sched st
                    hsl hc hv hcl hn hw =
  proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (switch-st nothing false) st
  res    = subscribeE g b (thru-outer switchᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (switch-st nothing false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH = subscribeE-nest-arr c sl B W g b (thru-outer switchᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-switch c b hv)
         (nestClosOK?-mono c sl b (switchAllᵉ b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-switch g b κ id now sched st) hw)

  FIT = thruFit-arr-switch c sl B W g b κ id now sched st hsl hc hv hcl hn hw

  PUSH = pushBurst-nest-thru
           (arrD (nestUnit e sl) B
              (suc W * closSizeᵉ (slotClos sl) (switchAllᵉ b)))
           g switchᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT

  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (switch-st nothing false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (switch-st nothing false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) b)
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (switchAllᵉ b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
           (closSizeᵉ (slotClos sl) (switchAllᵉ b)) (n≤1+n _)
subscribeE-nest-arr {e = e} {u = u} c sl B W g (exhaustAllᵉ b) κ id now sched st
                    hsl hc hv hcl hn hw =
  proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (exhaust-st false false) st
  res    = subscribeE g b (thru-outer exhaustᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (exhaust-st false false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH = subscribeE-nest-arr c sl B W g b (thru-outer exhaustᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-exhaust c b hv)
         (nestClosOK?-mono c sl b (exhaustAllᵉ b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-exhaust g b κ id now sched st) hw)

  FIT = thruFit-arr-exhaust c sl B W g b κ id now sched st hsl hc hv hcl hn hw

  PUSH = pushBurst-nest-thru
           (arrD (nestUnit e sl) B
              (suc W * closSizeᵉ (slotClos sl) (exhaustAllᵉ b)))
           g exhaustᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT

  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (exhaust-st false false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (exhaust-st false false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) b)
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (exhaustAllᵉ b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) b)
           (closSizeᵉ (slotClos sl) (exhaustAllᵉ b)) (n≤1+n _)
subscribeE-nest-arr c sl B W g0 (μᵉ b) κ id now sched st hsl hc hv hcl hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest-arr {e = e} c sl B W (gs fuel) (μᵉ b) κ id now sched st
                    hsl hc hv hcl hn hw =
  ≤-trans (proj₁ IH) grow
  , ≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow)
  , (λ j → ≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow))
  where
  IH = subscribeE-nest-arr c sl B W fuel (unfoldμ b) κ id now sched st hsl hc
         (≤ᵇ-true (syncSizeᵉ (unfoldμ b)) (Caps.cSize c)
           (≤-trans (≤-reflexive (syncSize-unfoldμ b))
             (≤-trans (n≤1+n (syncSizeᵉ b))
                      (nestValOK?-size c (μᵉ b) hv))))
         (nestClosOK?-mono c sl (unfoldμ b) (μᵉ b)
            (≤-trans (≤-reflexive (closSize-unfoldμ (slotClos sl) b))
                     (n≤1+n _))
            hcl)
         (≤-trans (≤-reflexive (nestD-unfoldμ b)) hn)
         (≤-trans (descW-mu fuel b κ id now sched st) hw)

  -- the unfolding leaves the sync spine where it was, the recursive
  -- occurrences being defer-gated, so the μ node is the only thing
  -- this head spends and one step of the key covers it
  grow : arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (unfoldμ b))
           ≤ arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) (μᵉ b))
  grow = arrDW-mono (nestUnit e sl) B W (closSizeᵉ (slotClos sl) (unfoldμ b))
           (closSizeᵉ (slotClos sl) (μᵉ b))
           (≤-trans (≤-reflexive (closSize-unfoldμ (slotClos sl) b))
                    (n≤1+n _))
-- a defer PARKS its body rather than subscribing it, so the burst is
-- bookkeeping and the node installed reads zero: nothing about the
-- body reaches either measure, which is why the head needs no key
subscribeE-nest-arr c sl B W g (deferᵉ b) κ id now sched st hsl hc hv hcl hn hw =
  z≤n
  , ≤-trans (setNode-nodes _ _ (EvalSt.nodes st)) (⊔-lub z≤n (m≤m⊔n _ _))
  , (λ j → ≤-trans (nodeNestAt-set j _ _ st) (⊔-lub z≤n (m≤m⊔n _ _)))


-- NO FUEL IS NO CONNECT: the arm returns a dry close and leaves the
-- state alone, so every conjunct is at its floor.
sharedConnect-nest-arr c sl W g0 i d κ id now sched st hsl hsi hc hk hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
sharedConnect-nest-arr {Γ = Γ} {t = t} {e = e} c sl W (gs fuel) i d κ id now sched st
                       hsl hsi hc hk hw =
  nestOut-if {t = t} D st (burstCompleted (proj₁ res)) _ _ died lived
  where
  D = arrD (nestUnit e sl) (nestUnit e sl) (suc W * closSizeᵉ (slotClos sl) d)

  st₁ : EvalSt e
  st₁ = register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })

  res = subscribeE fuel d (share-sink i) id now sched st₁

  -- the registration writes the registry and the counter beside it, so
  -- every conjunct of the invariant reads the list it read before
  IH = subscribeE-nest-arr c sl (nestUnit e sl) W fuel d (share-sink i) id now
         sched st₁ hsl hc
         (≤ᵇ-true (syncSizeᵛ (obs (lookup Γ i)) d) (Caps.cSize c)
            (≤-trans (≤-trans (syncSize≤closᵉ (slotClos sl) (slotClos-pos sl) d)
                              (n≤1+n _))
                     hk))
         (≤ᵇ-true (closSizeᵉ (slotClos sl) d) (Caps.cSize c)
            (≤-trans (n≤1+n _) hk))
         -- the definition is a SUMMAND of the telescope's nesting, which
         -- is what the premise buys and what the unit is made of
         (≤-trans (≤-trans (≤-reflexive (sym (cong slotNest hsi)))
                           (fᵢ≤sum-tab (λ j → slotNest (sl j)) i))
                  (≤-trans (m≤n+m (slotsNestSum sl) (nestDᵉ e)) (n≤1+n _)))
         (≤-trans (connW-gs fuel i d κ id now sched st) hw)

  -- the definition died inside its own connect burst: a close is
  -- latched and the registration drops, neither of which is a value
  -- and neither of which touches the node table
  died : NestOut {t = t} D st
           ((((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                at id from toℕ i as subscribe) ∷ sharedPlumb (proj₁ res))
            , proj₁ (proj₂ res)
            , record (proj₂ (proj₂ res))
                { registry = dropSource (toℕ i) (EvalSt.registry (proj₂ (proj₂ res)))
                ; completedSources =
                    toℕ i ∷ EvalSt.completedSources (proj₂ (proj₂ res)) })
  died = ≤-trans (≤-reflexive
                   (cong (nestDᵛˢ {u = lookup Γ i}) (splitBurst-plumb (proj₁ res))))
                 (proj₁ IH)
       , proj₁ (proj₂ IH) , proj₂ (proj₂ IH)

  lived : NestOut {t = t} D st
            ((((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                ∷ sharedPlumb (proj₁ res))
             , proj₁ (proj₂ res) , proj₂ (proj₂ res))
  lived = ≤-trans (≤-reflexive
                    (cong (nestDᵛˢ {u = lookup Γ i}) (splitBurst-plumb (proj₁ res))))
                  (proj₁ IH)
        , proj₁ (proj₂ IH) , proj₂ (proj₂ IH)

subscribeInner-nest-arr : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (o : Closed Γ s)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs s) o ≡ true →
  nestClosOK? c sl o ≡ true →
  nestDᵉ o ≤ B →
  innerW sf op allNid κ id now o sched st ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = subscribeInner sf op allNid κ id now o sched st
      D = arrD (nestUnit e sl) B (suc W * closSizeᵉ (slotClos sl) o) in
  (nestDᵛˢ (proj₁ (proj₂ r)) ≤ D)
  × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ D)
  × ((j : NodeId) →
       nodeNestAt j (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
         ≤ nodeNestAt j st ⊔ D)
subscribeInner-nest-arr c sl B W g0 op allNid κ id now o sched st
                        hsl hc hv hcl hn hw =
  z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeInner-nest-arr c sl B W (gs fuel) op allNid κ id now o sched st
                        hsl hc hv hcl hn hw =
  subscribeE-nest-arr c sl B W fuel o
    (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st hsl
    (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)
    hv hcl hn (≤-trans (innerW-gs fuel op allNid κ id now o sched st) hw)

-- ONE CONSUME STEP, AT TWO GRANT INDICES AND NOT ONE.  Each head reads
-- its own node, and every arm either leaves the state alone or runs
-- the ONE `subscribeInner` all three share and writes one node -- so
-- the three stand or fall together, and they do so on the delivered
-- values rather than on either store reading.
--
-- ONE BOUND FOR BOTH SIDES DOES NOT HOLD, which is why the arrival is
-- read at `m` and the delivery at `m′`.  A map's step function may name
-- its payload TWICE while the measure charges the map's two halves by
-- SUM, so the substitution puts the payload's whole nesting in both
-- copies and the delivery reads DOUBLE an arrival the flat grant
-- admitted -- with no constant alongside it to absorb the gap.  The
-- ratio is two at every depth, so this is not a corner.
--
-- AND THE LEVEL IS WHAT PAYS FOR IT, which is the whole reason the
-- grant is keyed on the descent's size rather than being one number:
-- `nestB-frame` absorbs a doubling and the frame's own additive charge
-- into ONE step of the key, and an `All` head's `syncSizeᵉ` is exactly
-- one above its body's, so the step the callers must supply is
-- `≤-refl`.  A flat grant has no index to spend, which is why it could
-- not have been repaired by choosing a bigger number.
--
-- AND THE SLOTS CONJUNCT IS NOT DECORATION: the walk re-enters at the
-- state the previous arrival left, so without it the grant the next
-- step is read at is a different one, and the chain does not compose.
--
-- AND THE ARM THAT SUBSCRIBES IS WHERE THE INDUCTION LIVES: every
-- other way into `thruConsume` either returns its inputs untouched or
-- parks the arrival, so the step's whole caps obligation is the
-- descent's own and the arms contribute only their write-backs.

-- THE ONE SUBSCRIPTION ALL THREE ARMS SHARE, which is where the caps
-- bundle is really bet: every node the descent installs must pass the
-- width fold and the slot telescope must come back unmoved.  The
-- writes AROUND it are checked beside it -- a bump rewrites one node
-- to a state the width predicate reads identically, a kill touches no
-- node and no slot, and each arm's own write-back is a state the
-- predicate reads as true outright.
--
-- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, not merely its written
-- size, and the caps half needs that premise for the same reason the
-- nesting half does: the walk's slot clause reads the telescope a
-- shared arrival points into, and `nestValOK?` is a fact about the
-- VALUE alone.  Without it the connect leg installs a definition no
-- premise has ever sized.  The suppliers already carry it -- the burst
-- admissibility fold states it emit by emit -- so what this threads is
-- a fact the chain had and dropped.
-- AND THE BODY IT USED TO HAVE RESTED ON A WALK THAT IS NOW KNOWN
-- FALSE AT ONE CAP, so the statement stands and the proof does not.
-- What the descent installs is the arrival's syntax SUBSTITUTED, whose
-- proven width bound is the iterate rather than the entry reading, so
-- a conclusion at the cap the premises were read at cannot come from
-- the face -- the face reports at a cap that steps, and the step is
-- what this statement has nowhere to put.  The entry-width key here is
-- what stops the neighbouring witness from reaching this form: it
-- pins the arrival's DELIVERED width, which that witness exceeds, so
-- what sits below is adjacent rather than decisive and nothing has yet
-- instantiated this shape.
--
-- AND THE DESCENT IT NEEDS IS PROVEN, ONE FACE OVER AND STRICTLY
-- STRONGER: `subscribeInner-caps` reports the caps boolean over the
-- descended state, the value key over the payload, the event key over
-- the burst and a STRICT level bound, at a cap that STEPS -- which is
-- what a walk through a substituting head can honestly claim, and why
-- it is not refutable where this shape is.  So this row is not owed a
-- proof; it is owed a CONVERSION, and the premises that face asks for
-- are the walk premise's own, dropped at this cone's door in favour of
-- the weaker reading.
--
-- AND THE WHOLE CHAIN ABOVE IT IS PROVEN THERE TOO -- the per-arrival
-- step and the fold over a burst both -- so what stands here is a
-- weaker DUPLICATE of proven code.  The duplicate checker cannot see
-- it: the two are stated at different predicates and different caps,
-- so they read as different facts while being the same operation.
-- What holds the copy in place is the NESTING chain beside it, which
-- takes its state facts from these arms; moving it onto the proven
-- ones is the conversion, and the level those report is what the fold
-- has to join rather than accumulate.
-- REFUTED: `Refuted.Subscribe-Burst-Width` kills the unkeyed walk this
--   body descended through, at a parked pair whose queue crosses the
--   width the premises were read at.
-- RECOVERY: git show 5899a5e restores the body, whose re-entry
--   argument -- that the minted id and the appended frame are writes
--   the predicate does not read -- the ceiling form still needs.
postulate
  subscribeInner-nestCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (fuel : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick)
    (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) o ≡ true →
    nestClosOK? c sl o ≡ true →
    pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
    ⦃ _ : FaceOK c sl ⦄ →
    let R      = subscribeInner fuel op nid κ id now o sched st
        sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
        st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))) in
    (nestCapsOK? c sched₁ st₁ ≡ true) × (Sched.slots sched₁ ≡ sl)


-- A bump rewrites one node to a state the width predicate cannot tell
-- from the old one: the merge clause of `widNode` reads only the
-- queue, and the bump moves only the activity counter.
mergeAllBump-nestCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (done : Bool) (sched : Sched Γ) (st : EvalSt e) →
  nestCapsOK? c sched st ≡ true →
  nestCapsOK? c sched
    (record st { nodes = mergeAllBump nid done (EvalSt.nodes st) }) ≡ true
mergeAllBump-nestCaps c nid done sched st h
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (mergeAll-st lim act q od) =
      nestCapsOK?-setNode c nid
        (mergeAll-st lim (if done then act else suc act) q od) sched st
        (nestCapsOK?-lookupWid c nid (mergeAll-st lim act q od) sched st eq h) h
... | just (scan-st v)        = h
... | just (take-st k)        = h
... | just (switch-st cu od)  = h
... | just (exhaust-st ac od) = h
... | nothing                 = h

thruStep-merge-inner-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs u))) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} lim act q od) →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  suc (length q) ≤ Caps.cWid c →
  ⦃ _ : FaceOK c sl ⦄ →
  let R      = subscribeInner fuel mergeAllᵒ nid κ id now o sched st
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₁ { nodes = mergeAllBump nid done (EvalSt.nodes st₁) } in
  (nestCapsOK? c sched₁ st′ ≡ true) × (Sched.slots sched₁ ≡ sl)
thruStep-merge-inner-caps c sl fuel nid κ id now lim act q od o sched st
  hl hsl hc hv hcl hw hq =
  mergeAllBump-nestCaps c nid done sched₁ st₁ (proj₁ SUB) , proj₂ SUB
  where
  R      = subscribeInner fuel mergeAllᵒ nid κ id now o sched st
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  SUB = subscribeInner-nestCaps c sl fuel mergeAllᵒ nid κ id now o sched st
          hsl hc hv hcl hw

thruStep-merge-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Val Γ (obs u))) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} lim act q od) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  -- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, not merely its written
  -- size.  The unconditional reading was REFUTED at a substituting
  -- slot definition, where the two differ by a whole telescope, so
  -- this is the true statement replacing a false one rather than a
  -- weakening -- and the descent below spends it as the frame charge's
  -- exponent, which is the same quantity the key is read at.
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  suc (length q) ≤ Caps.cWid c →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  -- AND THE INNER'S OWN WIDTH, which the arr-keyed descent this step
  -- runs now reads: the key it is granted at is read over the burst,
  -- so the width has to arrive with the arrival rather than being
  -- recovered from the grant.
  innerW fuel mergeAllᵒ nid κ id now o sched st ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let R      = subscribeInner fuel mergeAllᵒ nid κ id now o sched st
      vs     = proj₁ (proj₂ R)
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₁ { nodes = mergeAllBump nid done (EvalSt.nodes st₁) }
      G′     = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ vs ≤ G′)
  × (nodesMax st′ ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) → nodeNestAt j st′ ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c sched₁ st′ ≡ true)
  × (Sched.slots sched₁ ≡ sl)
thruStep-merge-inner {e = e} c sl B W m m′ fuel nid κ id now lim act q od o sched st
                     eq hsl hm hc hv hcl hw hlen hn hwi =
    ≤-trans (proj₁ ARR) frame
  , ≤-trans (bump-fold nid done (EvalSt.nodes st₁))
            (≤-trans (proj₁ (proj₂ ARR)) (⊔-mono-≤ ≤-refl frame))
  , (λ j → ≤-trans (bump-at j nid done (EvalSt.nodes st₁))
                   (≤-trans (proj₂ (proj₂ ARR) j) (⊔-mono-≤ ≤-refl frame)))
  , proj₁ CAPS , proj₂ CAPS
  where
  R = subscribeInner fuel mergeAllᵒ nid κ id now o sched st

  done : Bool
  done = proj₁ (proj₂ (proj₂ (proj₂ R)))

  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))

  N : ℕ
  N = nestB (Caps.cSize c) W (nestUnit e sl) B m

  ARR = subscribeInner-nest-arr c sl N W fuel mergeAllᵒ nid κ id now o sched st
          hsl hc hv (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hn hwi

  CAPS = thruStep-merge-inner-caps c sl fuel nid κ id now lim act q od o sched st
           eq hsl hc hv (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hw hlen

  hk : suc (pred (suc W * closSizeᵉ (slotClos sl) o)) ≤ suc W * Caps.cSize c
  hk = ≤-trans (suc-pred-≤
                 (arrDW-pos W (closSizeᵉ (slotClos sl) o)
                   (≤-trans (syncSizeᵉ-pos o)
                            (syncSize≤closᵉ (slotClos sl)
                               (slotClos-pos sl) o))))
               (*-monoʳ-≤ (suc W) hcl)

  frame : 2 ^ pred (suc W * closSizeᵉ (slotClos sl) o) * (nestUnit e sl + N)
            ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m′
  frame = ≤-trans (*-monoʳ-≤ (2 ^ pred (suc W * closSizeᵉ (slotClos sl) o))
                     (+-monoˡ-≤ N (nestB-unit (Caps.cSize c) W (nestUnit e sl) B m)))
                  (nestB-frame-dblW (Caps.cSize c) W (nestUnit e sl) B m
                     (pred (suc W * closSizeᵉ (slotClos sl) o)) m′ hk hm)

-- THE SWITCH HAS ONE ARM THAT DOES ANYTHING: there is no limit to
-- spend, so an arrival always kills the current inner and subscribes.
-- What the leaf owes over the merge's is the KILL -- `switchKill`
-- emits closes and edits the table before the descent runs, so the
-- state the subscribe starts from is not the one the caller handed in.

-- THE KILL MOVES NO NODE, which is the whole of what this face needs
-- from it: `switchKill` rewrites the registry, the cancelled list and
-- the live set, and the node table is carried through untouched.
abstract
  switchKill-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (cur : Maybe Id) (sched : Sched Γ) (st : EvalSt e) →
    EvalSt.nodes (proj₂ (proj₂ (switchKill cur sched st))) ≡ EvalSt.nodes st
  switchKill-nodes nothing  sched st = refl
  switchKill-nodes (just v) sched st = refl

thruStep-switch-inner-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (cur : Maybe Id) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od) →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  ⦃ _ : FaceOK c sl ⦄ →
  let K      = switchKill cur sched st
      sched₁ = proj₁ (proj₂ K)
      st₁    = proj₂ (proj₂ K)
      R      = subscribeInner fuel switchᵒ nid κ id now o sched₁ st₁
      inst   = proj₁ R
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₂
                 { nodes = setNode nid
                     (switch-st (if done then nothing else just inst) od)
                     (EvalSt.nodes st₂) } in
  (nestCapsOK? c sched₁ st₁ ≡ true)
  × (Sched.slots sched₁ ≡ sl)
  × (nestCapsOK? c sched₂ st′ ≡ true)
  × (Sched.slots sched₂ ≡ sl)
thruStep-switch-inner-caps c sl fuel nid κ id now nothing od o sched st
  hl hsl hc hv hcl hw =
  hc , hsl
  , nestCapsOK?-setNode c nid
      (switch-st (if done then nothing else just inst) od) sched₂ st₂
      refl (proj₁ SUB)
  , proj₂ SUB
  where
  R      = subscribeInner fuel switchᵒ nid κ id now o sched st
  inst   = proj₁ R
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  sched₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  SUB = subscribeInner-nestCaps c sl fuel switchᵒ nid κ id now o sched st
          hsl hc hv hcl hw
thruStep-switch-inner-caps c sl fuel nid κ id now (just v) od o sched st
  hl hsl hc hv hcl hw =
  hc , hsl
  , nestCapsOK?-setNode c nid
      (switch-st (if done then nothing else just inst) od) sched₂ st₂
      refl (proj₁ SUB)
  , proj₂ SUB
  where
  K      = switchKill (just v) sched st
  sched₁ = proj₁ (proj₂ K)
  st₁    = proj₂ (proj₂ K)
  R      = subscribeInner fuel switchᵒ nid κ id now o sched₁ st₁
  inst   = proj₁ R
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  sched₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  SUB = subscribeInner-nestCaps c sl fuel switchᵒ nid κ id now o sched₁ st₁
          hsl hc hv hcl hw

thruStep-switch-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (cur : Maybe Id) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  -- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, not merely its written
  -- size.  The unconditional reading was REFUTED at a substituting
  -- slot definition, where the two differ by a whole telescope, so
  -- this is the true statement replacing a false one rather than a
  -- weakening -- and the descent below spends it as the frame charge's
  -- exponent, which is the same quantity the key is read at.
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  innerW fuel switchᵒ nid κ id now o
    (proj₁ (proj₂ (switchKill cur sched st)))
    (proj₂ (proj₂ (switchKill cur sched st))) ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let K      = switchKill cur sched st
      sched₁ = proj₁ (proj₂ K)
      st₁    = proj₂ (proj₂ K)
      R      = subscribeInner fuel switchᵒ nid κ id now o sched₁ st₁
      vs     = proj₁ (proj₂ R)
      inst   = proj₁ R
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₂
                 { nodes = setNode nid
                     (switch-st (if done then nothing else just inst) od)
                     (EvalSt.nodes st₂) }
      G′     = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ vs ≤ G′)
  × (nodesMax st′ ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) → nodeNestAt j st′ ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c sched₂ st′ ≡ true)
  × (Sched.slots sched₂ ≡ sl)
thruStep-switch-inner {e = e} c sl B W m m′ fuel nid κ id now cur od o sched st
                      eq hsl hm hc hv hcl hw hn hwi =
    ≤-trans (proj₁ ARR) frame
  , ≤-trans (setNode-nodes nid _ (EvalSt.nodes st₂))
            (⊔-lub z≤n (≤-trans (proj₁ (proj₂ ARR))
                                (⊔-mono-≤ killFold frame)))
  , (λ j → ≤-trans (nodeNestAt-set j nid _ st₂)
                   (⊔-lub z≤n (≤-trans (proj₂ (proj₂ ARR) j)
                                       (⊔-mono-≤ (killAt j) frame))))
  , proj₁ (proj₂ (proj₂ CAPS)) , proj₂ (proj₂ (proj₂ CAPS))
  where
  K = switchKill cur sched st
  sched₁ = proj₁ (proj₂ K)
  st₁ = proj₂ (proj₂ K)

  R = subscribeInner fuel switchᵒ nid κ id now o sched₁ st₁
  st₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))

  N : ℕ
  N = nestB (Caps.cSize c) W (nestUnit e sl) B m

  CAPS = thruStep-switch-inner-caps c sl fuel nid κ id now cur od o sched st
           eq hsl hc hv (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hw

  ARR = subscribeInner-nest-arr c sl N W fuel switchᵒ nid κ id now o sched₁ st₁
          (proj₁ (proj₂ CAPS)) (proj₁ CAPS) hv
          (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hn hwi

  killFold : nodesMax st₁ ≤ nodesMax st
  killFold = ≤-reflexive (cong nodesFold (switchKill-nodes cur sched st))

  killAt : (j : NodeId) → nodeNestAt j st₁ ≤ nodeNestAt j st
  killAt j = ≤-reflexive
               (cong (λ z → maybe nodeNest 0 (lookupNode j z))
                     (switchKill-nodes cur sched st))

  hk : suc (pred (suc W * closSizeᵉ (slotClos sl) o)) ≤ suc W * Caps.cSize c
  hk = ≤-trans (suc-pred-≤
                 (arrDW-pos W (closSizeᵉ (slotClos sl) o)
                   (≤-trans (syncSizeᵉ-pos o)
                            (syncSize≤closᵉ (slotClos sl)
                               (slotClos-pos sl) o))))
               (*-monoʳ-≤ (suc W) hcl)

  frame : 2 ^ pred (suc W * closSizeᵉ (slotClos sl) o) * (nestUnit e sl + N)
            ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m′
  frame = ≤-trans (*-monoʳ-≤ (2 ^ pred (suc W * closSizeᵉ (slotClos sl) o))
                     (+-monoˡ-≤ N (nestB-unit (Caps.cSize c) W (nestUnit e sl) B m)))
                  (nestB-frame-dblW (Caps.cSize c) W (nestUnit e sl) B m
                     (pred (suc W * closSizeᵉ (slotClos sl) o)) m′ hk hm)

-- AND THE EXHAUST HAS ONE TOO, the busy arm dropping the arrival
-- outright -- so the only work is the idle one, and it is the merge's
-- admit arm without a queue to write back.
thruStep-exhaust-inner-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (exhaust-st false od) →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  ⦃ _ : FaceOK c sl ⦄ →
  let R      = subscribeInner fuel exhaustᵒ nid κ id now o sched st
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₁
                 { nodes = setNode nid (exhaust-st (not done) od)
                             (EvalSt.nodes st₁) } in
  (nestCapsOK? c sched₁ st′ ≡ true) × (Sched.slots sched₁ ≡ sl)
thruStep-exhaust-inner-caps c sl fuel nid κ id now od o sched st
  hl hsl hc hv hcl hw =
  nestCapsOK?-setNode c nid (exhaust-st (not done) od) sched₁ st₁
    refl (proj₁ SUB)
  , proj₂ SUB
  where
  R      = subscribeInner fuel exhaustᵒ nid κ id now o sched st
  done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  SUB = subscribeInner-nestCaps c sl fuel exhaustᵒ nid κ id now o sched st
          hsl hc hv hcl hw

thruStep-exhaust-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (od : Bool)
  (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode nid (EvalSt.nodes st) ≡ just (exhaust-st false od) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  -- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, not merely its written
  -- size.  The unconditional reading was REFUTED at a substituting
  -- slot definition, where the two differ by a whole telescope, so
  -- this is the true statement replacing a false one rather than a
  -- weakening -- and the descent below spends it as the frame charge's
  -- exponent, which is the same quantity the key is read at.
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  innerW fuel exhaustᵒ nid κ id now o sched st ≤ W →
  ⦃ _ : FaceOK c sl ⦄ →
  let R      = subscribeInner fuel exhaustᵒ nid κ id now o sched st
      vs     = proj₁ (proj₂ R)
      done   = proj₁ (proj₂ (proj₂ (proj₂ R)))
      sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
      st′    = record st₁
                 { nodes = setNode nid (exhaust-st (not done) od)
                             (EvalSt.nodes st₁) }
      G′     = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ vs ≤ G′)
  × (nodesMax st′ ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) → nodeNestAt j st′ ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c sched₁ st′ ≡ true)
  × (Sched.slots sched₁ ≡ sl)
thruStep-exhaust-inner {e = e} c sl B W m m′ fuel nid κ id now od o sched st
                       eq hsl hm hc hv hcl hw hn hwi =
    ≤-trans (proj₁ ARR) frame
  , ≤-trans (setNode-nodes nid (exhaust-st (not done) od) (EvalSt.nodes st₁))
            (⊔-lub z≤n (≤-trans (proj₁ (proj₂ ARR)) (⊔-mono-≤ ≤-refl frame)))
  , (λ j → ≤-trans (nodeNestAt-set j nid (exhaust-st (not done) od) st₁)
                   (⊔-lub z≤n (≤-trans (proj₂ (proj₂ ARR) j)
                                       (⊔-mono-≤ ≤-refl frame))))
  , proj₁ CAPS , proj₂ CAPS
  where
  R = subscribeInner fuel exhaustᵒ nid κ id now o sched st

  done : Bool
  done = proj₁ (proj₂ (proj₂ (proj₂ R)))

  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))

  N : ℕ
  N = nestB (Caps.cSize c) W (nestUnit e sl) B m

  ARR = subscribeInner-nest-arr c sl N W fuel exhaustᵒ nid κ id now o sched st
          hsl hc hv (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hn hwi

  CAPS = thruStep-exhaust-inner-caps c sl fuel nid κ id now od o sched st
           eq hsl hc hv (≤ᵇ-true (closSizeᵉ (slotClos sl) o) (Caps.cSize c) hcl) hw

  hk : suc (pred (suc W * closSizeᵉ (slotClos sl) o)) ≤ suc W * Caps.cSize c
  hk = ≤-trans (suc-pred-≤
                 (arrDW-pos W (closSizeᵉ (slotClos sl) o)
                   (≤-trans (syncSizeᵉ-pos o)
                            (syncSize≤closᵉ (slotClos sl)
                               (slotClos-pos sl) o))))
               (*-monoʳ-≤ (suc W) hcl)

  frame : 2 ^ pred (suc W * closSizeᵉ (slotClos sl) o) * (nestUnit e sl + N)
            ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m′
  frame = ≤-trans (*-monoʳ-≤ (2 ^ pred (suc W * closSizeᵉ (slotClos sl) o))
                     (+-monoˡ-≤ N (nestB-unit (Caps.cSize c) W (nestUnit e sl) B m)))
                  (nestB-frame-dblW (Caps.cSize c) W (nestUnit e sl) B m
                     (pred (suc W * closSizeᵉ (slotClos sl) o)) m′ hk hm)

-- THE STATE PAIR SURVIVES ONE ARRIVAL, measure-free: the slots
-- equation and the invariant come back from `thruConsume` on the
-- caller's own premises, with no grant read anywhere.  The subscribing
-- arms are the postulated inner-caps leaves; the parking arm and every
-- untouched-node arm are discharged here, so what this body asserts is
-- exactly the leaves and nothing beside them.

-- AND THIS IS WHERE THE WEAKENED INVARIANT IS PRODUCED, which is what
-- fixes the shape of retiring it.  Every entry into that currency holds
-- the FULL face already, so two of the three downgrades are a choice
-- made at the door and one was not read at all -- but the two that
-- remain cannot have the door pushed any further down, because the
-- premise their own recursion consumes is this head's CONCLUSION.  The
-- currency is not threaded through the walk; it is minted by it.
--
-- So the cone comes out in ONE piece or not at all -- and it comes out
-- against something that already exists.  This head, the three step
-- heads beside it, the arrival walk, the frame step, the burst push and
-- both subscribe heads are all duplicated one module up, HEAD FOR HEAD
-- against the same evaluator heads, at the FULL face and proven -- two
-- of them under the very same name.  The duplicate check cannot see it:
-- the statements differ in their currency, and the modules are never in
-- scope together.
--
-- So nothing here needs restating.  What is owed is the premises that
-- clique reads and this one does not -- the slot caps, the two
-- positivity keys, the path key, and the budget, operator and depth
-- currencies -- carried from the two doors out to the consumers, which
-- hold them already.  Stated at the full face WITHOUT them it would be
-- the statement the width refutation kills, one layer up and no truer
-- for the move; that is why the threading is the work and the deletion
-- is not.

-- AND THE SCALAR HALF OF THAT LIST IS FREE AT THE DOOR, which is what
-- sizes the threading and is the reason it is worth starting.  Four of
-- the face's premises are constant along the whole cone -- a size cap
-- of two or more, a positive registry, the slot caps and the slot
-- telescope under the size cap -- and the cone's only door out reaches
-- its consumers at the INSTANT's cap, where all four are proven facts
-- about that family rather than hypotheses anyone must acquire:
-- `capsAt-base-size⁺` delivers two of them at once, `1≤capsAt-reg` the
-- registry and `slotsCaps?-capsAt` the slot caps.  So carrying them is
-- plumbing to the head that needs them and costs the top-line theorem
-- NOTHING; what is actually owed is the path key, the budget and depth
-- currencies, and the index below.

-- AND THE PREMISES ARE NECESSARY AND NOT SUFFICIENT, which is the part
-- the sentence above understates and the part that sizes the job.  The
-- proven head does not report at the cap it was entered at: it reports
-- at a level STEPPED by an existential of its own, bounded by the
-- face's level function.  So an importer inherits that shape -- this
-- head's conclusion, the arrival walk's above it and the burst push's
-- above that all become level-carrying, and the level ACCUMULATES
-- along the arrival list rather than being a constant the caller
-- picks.  That is the same level the walk's own exit pair was found
-- unable to carry in place; the difference is that out there it is
-- already carried, and bounded.  So the threading is not a premise
-- edit: it is the cone taking the face's INDEX along with the face's
-- hypotheses, and no smaller change reaches the imported heads.
thruConsume-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  nestClosOK? c sl o ≡ true →
  thruRoom c W fuel op nid κ id now o sched st →
  let rc = thruConsume fuel op nid κ id now o sched st in
  nestCapsOK? c (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc))) ≡ true
thruConsume-caps {u = u} c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = hc
...   | yes refl with hasRoom lim act
...     | true =
          let C = thruStep-merge-inner-caps c sl fuel nid κ id now
                    lim act q od o sched st eq hsl hc hv hcl
                    (proj₁ hr) (proj₁ (proj₂ hr) lim act q od refl)
          in proj₁ C
...     | false =
          merge-park-caps c nid lim act q od o sched st eq hc
                  (proj₁ hr) (proj₁ (proj₂ hr) lim act q od refl)
thruConsume-caps c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr | nothing = hc
thruConsume-caps c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr | just (scan-st _) = hc
thruConsume-caps c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr | just (take-st _) = hc
thruConsume-caps c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr | just (switch-st _ _) = hc
thruConsume-caps c sl W fuel mergeAllᵒ nid κ id now o sched st hsl hc hv hcl hr | just (exhaust-st _ _) = hc
thruConsume-caps c sl W fuel switchᵒ nid κ id now o sched st hsl hc hv hcl hr
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (switch-st cur od) =
      let C = thruStep-switch-inner-caps c sl fuel nid κ id now cur od o sched st
                eq hsl hc hv hcl (proj₁ hr)
      in proj₁ (proj₂ (proj₂ C))
... | nothing = hc
... | just (scan-st _) = hc
... | just (take-st _) = hc
... | just (mergeAll-st _ _ _ _) = hc
... | just (exhaust-st _ _) = hc
thruConsume-caps c sl W fuel exhaustᵒ nid κ id now o sched st hsl hc hv hcl hr
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (exhaust-st true od)  = hc
... | just (exhaust-st false od) =
      let C = thruStep-exhaust-inner-caps c sl fuel nid κ id now od o sched st
                eq hsl hc hv hcl (proj₁ hr)
      in proj₁ C
... | nothing = hc
... | just (scan-st _) = hc
... | just (take-st _) = hc
... | just (mergeAll-st _ _ _ _) = hc
... | just (switch-st _ _) = hc

-- and over a whole arrival list, each at the state the previous one
-- left -- the fold `thruRoomOK` already has the shape of
thruWalk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  all (nestValOK? c (obs u)) os ≡ true →
  all (nestClosOK? c sl) os ≡ true →
  thruRoomOK c W fuel op nid κ id now os sched st →
  let rw = thruWalk fuel op nid κ id now os sched st in
  nestCapsOK? c (proj₁ (proj₂ (proj₂ rw))) (proj₂ (proj₂ (proj₂ rw))) ≡ true
thruWalk-caps c sl W fuel op nid κ id now [] sched st hsl hc hv hcl hr = hc
thruWalk-caps {u = u} c sl W fuel op nid κ id now (o ∷ os) sched st hsl hc hv hcl (hro , hros) =
  thruWalk-caps c sl W fuel op nid κ id now os
    (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
    (trans (KeepsC.slotsEq (thruConsume-keeps fuel op nid κ id now o sched st)) hsl)
    C (proj₂ (∧-true _ _ hv)) (proj₂ (∧-true _ _ hcl)) hros
  where
  rc = thruConsume fuel op nid κ id now o sched st
  C  = thruConsume-caps c sl W fuel op nid κ id now o sched st hsl hc
         (proj₁ (∧-true _ _ hv)) (proj₁ (∧-true _ _ hcl)) hro

-- the wrap on its own: it writes one node whose width reading is
-- unchanged -- the done flag is the one field `widNode` never reads --
-- and it never touches the schedule
thruWrap-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  nestCapsOK? c (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true →
  let w = thruWrap op nid fin r in
  nestCapsOK? c (proj₁ (proj₂ (proj₂ (proj₂ w))))
                (proj₂ (proj₂ (proj₂ (proj₂ w)))) ≡ true
thruWrap-caps c sl op nid false (vs , bs , sched′ , st′) hc = hc
thruWrap-caps c sl mergeAllᵒ nid true (vs , bs , sched′ , st′) hc
  with lookupNode nid (EvalSt.nodes st′) in eq
... | just (mergeAll-st lim act q od) =
      nestCapsOK?-setNode c nid (mergeAll-st lim act q true) sched′ st′
              (nestCapsOK?-lookupWid c nid (mergeAll-st lim act q od) sched′ st′ eq hc) hc
... | nothing = hc
... | just (scan-st _) = hc
... | just (take-st _) = hc
... | just (switch-st _ _) = hc
... | just (exhaust-st _ _) = hc
thruWrap-caps c sl switchᵒ nid true (vs , bs , sched′ , st′) hc
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur od) =
      nestCapsOK?-setNode c nid (switch-st cur true) sched′ st′ refl hc
... | nothing = hc
... | just (scan-st _) = hc
... | just (take-st _) = hc
... | just (mergeAll-st _ _ _ _) = hc
... | just (exhaust-st _ _) = hc
thruWrap-caps c sl exhaustᵒ nid true (vs , bs , sched′ , st′) hc
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act od) =
      nestCapsOK?-setNode c nid (exhaust-st act true) sched′ st′ refl hc
... | nothing = hc
... | just (scan-st _) = hc
... | just (take-st _) = hc
... | just (mergeAll-st _ _ _ _) = hc
... | just (switch-st _ _) = hc

-- ONE INSTANT AT THE WRAP'S FRAME PRESERVES THE STATE PAIR.  This is
-- the step every clause of the caps walk will spend at its instant
-- boundary: `stepFrame` at a `thru-outer` frame is the consume fold
-- under the wrap, so the pair rides the two proofs above.
stepThru-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  all (nestValOK? c (obs u)) vals ≡ true →
  all (nestClosOK? c sl) vals ≡ true →
  thruRoomOK c W fuel op nid κ id now vals sched st →
  let sf = stepFrame fuel id now (thru-outer op nid) κ vals fin sched st in
  nestCapsOK? c (proj₁ (proj₂ (proj₂ (proj₂ sf))))
                (proj₂ (proj₂ (proj₂ (proj₂ sf)))) ≡ true
stepThru-caps c sl W fuel op nid κ id now vals fin sched st hsl hc hv hcl hr =
  thruWrap-caps c sl op nid fin (thruWalk fuel op nid κ id now vals sched st)
    (thruWalk-caps c sl W fuel op nid κ id now vals sched st hsl hc hv hcl hr)

-- THE STEP, ASSEMBLED: the case split is `thruConsume`'s own, so the
-- arms that return their inputs untouched are discharged here and only
-- the two that do work are owed.
thruStep-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  thruRoom c W fuel mergeAllᵒ nid κ id now o sched st →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  ⦃ _ : FaceOK c sl ⦄ →
  let rc = thruConsume fuel mergeAllᵒ nid κ id now o sched st
      G′ = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ (proj₁ rc) ≤ G′)
  × (nodesMax (proj₂ (proj₂ (proj₂ rc))) ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) →
       nodeNestAt j (proj₂ (proj₂ (proj₂ rc))) ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c (proj₁ (proj₂ (proj₂ rc)))
                   (proj₂ (proj₂ (proj₂ rc))) ≡ true)
thruStep-merge {u = u} c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
...   | yes refl with hasRoom lim act
...     | true =
          let I = thruStep-merge-inner c sl B W m m′ fuel nid κ id now
                    lim act q od o sched st eq hsl hm hc hv hcl
                    (proj₁ hr) (proj₁ (proj₂ hr) lim act q od refl) hn
                    (proj₁ (proj₂ (proj₂ hr)))
          in proj₁ I , proj₁ (proj₂ I) , proj₁ (proj₂ (proj₂ I))
           , proj₁ (proj₂ (proj₂ (proj₂ I)))
...     | false =
          let P = thruStep-merge-park c sl B W m m′ nid
                    lim act q od o sched st eq hsl hm hc hv
                    (proj₁ hr) (proj₁ (proj₂ hr) lim act q od refl) hn
          in z≤n , proj₁ P , proj₁ (proj₂ P) , proj₂ (proj₂ P)
thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
    | nothing               = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
    | just (scan-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
    | just (take-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
    | just (switch-st _ _)  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
    | just (exhaust-st _ _) = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc

thruStep-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  thruRoom c W fuel switchᵒ nid κ id now o sched st →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  ⦃ _ : FaceOK c sl ⦄ →
  let rc = thruConsume fuel switchᵒ nid κ id now o sched st
      G′ = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ (proj₁ rc) ≤ G′)
  × (nodesMax (proj₂ (proj₂ (proj₂ rc))) ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) →
       nodeNestAt j (proj₂ (proj₂ (proj₂ rc))) ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c (proj₁ (proj₂ (proj₂ rc)))
                   (proj₂ (proj₂ (proj₂ rc))) ≡ true)
thruStep-switch {u = u} c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (switch-st cur od) =
      let I = thruStep-switch-inner c sl B W m m′ fuel nid κ id now cur od
                o sched st eq hsl hm hc hv hcl (proj₁ hr) hn
                (proj₂ (proj₂ (proj₂ hr)) cur od refl)
      in proj₁ I , proj₁ (proj₂ I) , proj₁ (proj₂ (proj₂ I))
           , proj₁ (proj₂ (proj₂ (proj₂ I)))
... | nothing               = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (mergeAll-st _ _ _ _) = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (scan-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (take-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (exhaust-st _ _) = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc

thruStep-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) o ≡ true →
  closSizeᵉ (slotClos sl) o ≤ Caps.cSize c →
  thruRoom c W fuel exhaustᵒ nid κ id now o sched st →
  nestDᵛ (obs u) o ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  ⦃ _ : FaceOK c sl ⦄ →
  let rc = thruConsume fuel exhaustᵒ nid κ id now o sched st
      G′ = nestB (Caps.cSize c) W (nestUnit e sl) B m′ in
  (nestDᵛˢ (proj₁ rc) ≤ G′)
  × (nodesMax (proj₂ (proj₂ (proj₂ rc))) ≤ nodesMax st ⊔ G′)
  × ((j : NodeId) →
       nodeNestAt j (proj₂ (proj₂ (proj₂ rc))) ≤ nodeNestAt j st ⊔ G′)
  × (nestCapsOK? c (proj₁ (proj₂ (proj₂ rc)))
                   (proj₂ (proj₂ (proj₂ rc))) ≡ true)
thruStep-exhaust {u = u} c sl B W m m′ fuel nid κ id now o sched st hsl hm hc hv hcl hr hn
  with lookupNode nid (EvalSt.nodes st) in eq
... | just (exhaust-st false od) =
      let I = thruStep-exhaust-inner c sl B W m m′ fuel nid κ id now od
                o sched st eq hsl hm hc hv hcl (proj₁ hr) hn
                (proj₁ (proj₂ (proj₂ hr)))
      in proj₁ I , proj₁ (proj₂ I) , proj₁ (proj₂ (proj₂ I))
           , proj₁ (proj₂ (proj₂ (proj₂ I)))
... | just (exhaust-st true od)  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | nothing               = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (mergeAll-st _ _ _ _) = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (scan-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (take-st _)      = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc
... | just (switch-st _ _)  = z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _) , hc

-- The fit over one emit's values is now CHECKED: each arrival spends
-- its step, the invariant the step returns is what the next arrival
-- runs under, and the per-value bound falls out of the joined one
-- because `nestDᵛˢ` is a join.
thruFit-vals : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  suc m ≤ m′ →
  nestCapsOK? c sched st ≡ true →
  all (nestValOK? c (obs u)) os ≡ true →
  all (nestClosOK? c sl) os ≡ true →
  thruRoomOK c W fuel op nid κ id now os sched st →
  nestDᵛˢ os ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  ⦃ _ : FaceOK c sl ⦄ →
  thruFitOK (nestB (Caps.cSize c) W (nestUnit e sl) B m′)
    fuel op nid κ id now os sched st
thruFit-vals c sl B W m m′ fuel op nid κ id now [] sched st hsl hm hc hv hcl hr hn = tt
thruFit-vals {u = u} c sl B W m m′ fuel mergeAllᵒ nid κ id now (o ∷ os) sched st hsl hm hc hv hcl hr hn =
  proj₁ S , proj₁ (proj₂ S) , proj₁ (proj₂ (proj₂ S))
  , thruFit-vals c sl B W m m′ fuel mergeAllᵒ nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
      (trans (KeepsC.slotsEq
                (thruConsume-keeps fuel mergeAllᵒ nid κ id now o sched st)) hsl) hm
      (proj₂ (proj₂ (proj₂ S))) (proj₂ (∧-true _ _ hv))
      (proj₂ (∧-true _ _ hcl)) (proj₂ hr)
      (≤-trans (m≤n⊔m (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)
  where
  rc = thruConsume fuel mergeAllᵒ nid κ id now o sched st
  S = thruStep-merge c sl B W m m′ fuel nid κ id now o sched st hsl hm hc
        (proj₁ (∧-true _ _ hv))
        (nestClosOK?-size c sl o (proj₁ (∧-true _ _ hcl))) (proj₁ hr)
        (≤-trans (m≤m⊔n (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)
thruFit-vals {u = u} c sl B W m m′ fuel switchᵒ nid κ id now (o ∷ os) sched st hsl hm hc hv hcl hr hn =
  proj₁ S , proj₁ (proj₂ S) , proj₁ (proj₂ (proj₂ S))
  , thruFit-vals c sl B W m m′ fuel switchᵒ nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
      (trans (KeepsC.slotsEq
                (thruConsume-keeps fuel switchᵒ nid κ id now o sched st)) hsl) hm
      (proj₂ (proj₂ (proj₂ S))) (proj₂ (∧-true _ _ hv))
      (proj₂ (∧-true _ _ hcl)) (proj₂ hr)
      (≤-trans (m≤n⊔m (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)
  where
  rc = thruConsume fuel switchᵒ nid κ id now o sched st
  S = thruStep-switch c sl B W m m′ fuel nid κ id now o sched st hsl hm hc
        (proj₁ (∧-true _ _ hv))
        (nestClosOK?-size c sl o (proj₁ (∧-true _ _ hcl))) (proj₁ hr)
        (≤-trans (m≤m⊔n (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)
thruFit-vals {u = u} c sl B W m m′ fuel exhaustᵒ nid κ id now (o ∷ os) sched st hsl hm hc hv hcl hr hn =
  proj₁ S , proj₁ (proj₂ S) , proj₁ (proj₂ (proj₂ S))
  , thruFit-vals c sl B W m m′ fuel exhaustᵒ nid κ id now os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
      (trans (KeepsC.slotsEq
                (thruConsume-keeps fuel exhaustᵒ nid κ id now o sched st)) hsl) hm
      (proj₂ (proj₂ (proj₂ S))) (proj₂ (∧-true _ _ hv))
      (proj₂ (∧-true _ _ hcl)) (proj₂ hr)
      (≤-trans (m≤n⊔m (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)
  where
  rc = thruConsume fuel exhaustᵒ nid κ id now o sched st
  S = thruStep-exhaust c sl B W m m′ fuel nid κ id now o sched st hsl hm hc
        (proj₁ (∧-true _ _ hv))
        (nestClosOK?-size c sl o (proj₁ (∧-true _ _ hcl))) (proj₁ hr)
        (≤-trans (m≤m⊔n (nestDᵛ (obs u) o) (nestDᵛˢ os)) hn)

-- WHAT SURVIVES THE FIT IS ROOM, AND THE FRAME CAN NOW HAND THE WALK
-- ALL OF IT.  Two of the record's four conjuncts are the burst's, one
-- is the queue the node holds, and the last is the arriving value's own
-- frame width -- which the caps premise already carries, `pWᵛ` at an
-- observable type BEING `pWᵉ`.  So the frame's job is not to derive the
-- record but to carry it along the walk: each consume runs at the state
-- the previous one left, and the slot telescope the width is read
-- against is what the state chain preserves.
--
-- REFUTED: `Refuted.Thru-Room-Frame` kills the form that asked the CAPS
--   for the queue bound, at the parking state its sibling already uses.
--   The caps admit a queue as long as the width field and the record
--   asks that field for one more, so the contradiction lands at the
--   FIRST arrival and no length premise reaches it.  That is why the
--   queue conjunct is owed by the walk's own record instead.
thruRoom-frame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (p : Path Γ u t)
  (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  all (nestValOK? c (obs u)) vals ≡ true →
  all (valCaps? c sl (obs u)) vals ≡ true →
  all (nestClosOK? c sl) vals ≡ true →
  thruRoomWOK W sf op nid p id now vals sched st →
  thruRoomQOK c sf op nid p id now vals sched st →
  thruRoomOK c W sf op nid p id now vals sched st
thruRoom-frame c W sl sf id now op nid p [] sched st
  hsl hc hnv hval hcl hw hq = tt
thruRoom-frame {n = n} {u = u} c W sl sf id now op nid p (o ∷ os) sched st
  hsl hc hnv hval hcl (hw , hws) (hq , hqs) =
  ROOM
  , thruRoom-frame c W sl sf id now op nid p os
      (proj₁ (proj₂ (proj₂ rc))) (proj₂ (proj₂ (proj₂ rc)))
      (trans (KeepsC.slotsEq
                (thruConsume-keeps sf op nid p id now o sched st)) hsl) K
      (proj₂ (∧-true _ _ hnv)) (proj₂ (∧-true _ _ hval))
      (proj₂ (∧-true _ _ hcl)) hws hqs
  where
  rc = thruConsume sf op nid p id now o sched st

  wid : pWᵉ n (Sched.slots sched) o ≤ Caps.cWid c
  wid = subst (λ z → pWᵉ n z o ≤ Caps.cWid c) (sym hsl)
          (≤ᵇ⇒≤ (pWᵛ n sl (obs u) o) (Caps.cWid c)
             (T-to (valCaps?-wid c sl (obs u) o (proj₁ (∧-true _ _ hval)))))

  ROOM : thruRoom c W sf op nid p id now o sched st
  ROOM = wid , hq , proj₁ hw , proj₂ hw

  K = thruConsume-caps c sl W sf op nid p id now o sched st hsl hc
        (proj₁ (∧-true _ _ hnv)) (proj₁ (∧-true _ _ hcl)) ROOM

-- THE ARRIVAL'S SYNC READING IS UNDER ITS RESOLVED CLOSURE, so the
-- key premise pays for the size premise the walk asks about each
-- value and no second hypothesis is owed.  The telescope is positive
-- at every slot, which is the side condition that makes the closure a
-- widening rather than a re-reading.
nestClosOK?⇒val : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (o : Val Γ (obs u)) →
  nestClosOK? c sl o ≡ true → nestValOK? c (obs u) o ≡ true
nestClosOK?⇒val c sl o h =
  ≤ᵇ-true _ _ (≤-trans (syncSize≤closᵉ (slotClos sl) (slotClos-pos sl) o)
                       (nestClosOK?-size c sl o h))

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
-- AND IT TAKES TWO PREMISES, WHICH ARE INDEPENDENT AND EACH
-- LOAD-BEARING FOR A DIFFERENT READER.  Tying the cap to the
-- TELESCOPE is what makes the arithmetic work: a telescope of depth
-- `d` costs `d` units of written size, so the cap dominates `d` and
-- the grant's tower dominates the `2 ^ d` a doubling definition can
-- deliver; and at the top it is a proven consequence of `capsAt`'s own
-- size, which is what lets a consumer discharge it.  Keying on the
-- ARRIVAL's resolved closure is what the route to a proof needs: this
-- module's proven statement about consuming one subscribed value takes
-- that key, as do the arr-keyed twin and the drain, and the size
-- premise cannot supply it -- the resolved closure is multiplicative
-- in the telescope's depth where the written sum is flat, so neither
-- premise implies the other.
--
-- AND THE DOUBLING SLOT FAMILY CANNOT BE SWEPT AGAINST THE CONDITIONED
-- FORM AT ALL, which is a coverage boundary and not evidence for the
-- statement.  Tying the cap to the telescope makes both sides move with
-- the layer count, at different orders: the slot's written size climbs
-- about fifteen per layer -- twenty-five at one layer, fifty-five at
-- three -- so the grant is a tower in a number growing linearly, while
-- the delivery only doubles, reading eight at three layers against a
-- grant past two to the six-thousandth.  Every deeper witness widens
-- the margin, so no member of the family can fail and a sweep over it
-- is unfalsifiable by construction.  What could still break the
-- statement has to break the link the premise creates: a delivery that
-- grows without the telescope's written size growing with it.
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
-- REFUTED: `Refuted.Thru-Fit-Frame-Slot` kills the form WITHOUT the
--   resolved-size premise, at a shared slot, eight against four.  A
--   slot reference has size one and depth zero, both by definition
--   and both correct, so the arrival pinned EVERY term of the grant
--   at its floor -- the cap `valCaps?` admits is one and the store
--   term is zero -- while the definition behind the slot doubles per
--   layer when it is subscribed.  No cap absorbed it: `capsOK?` has
--   no clause for slot defs, deliberately, they being fixed syntax,
--   and the width cap that does read the telescope is not a term of
--   the grant.  The same file carries the crossing at the PARENT,
--   whose own telescope term is linear where the delivery doubles --
--   which is why the premise is added HERE and spent there rather
--   than the unit being widened.
-- DEAD ROUTE: sweeping the ARRIVAL's depth cannot refute this, and the
--   reason is arithmetic rather than a failed attempt.  The grant's
--   factor is `nestFac`, a tower in the cap -- the cap is read off the
--   arrival's own size through the `valCaps?` premise, and a step that
--   duplicates needs a term big enough to write the duplication down.
--   So depth buys the bound side a tower per unit of size and the
--   measure side a doubling per level, and every deeper witness widens
--   the margin.  The refutations above all killed FLAT factors, which
--   is the axis that was open before the exponent moved into the burst.
--   What this does NOT cover is an arrival that NAMES its content
--   instead of carrying it, where the cap is read off the reference
--   and the delivery comes from somewhere the reference does not
--   measure -- the refutation below.

-- THE FRAME'S FIT IS THE MACHINERY'S WALK, WIDENED.  `thruFit-vals`
-- already proves the fit at the grant the rest of the tower spends,
-- and the descent is opened at the cap itself, where that grant IS
-- the frame layer's shape.  What the frame adds is only that the
-- arrival's own joined nesting sits under the base term, which is
-- where the walk starts, and that the whole thing survives a wider
-- bound -- both arithmetic.
thruFit-frame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (p : Path Γ u t)
  (vals : List (Val Γ (obs u))) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  1 ≤ W → length vals ≤ W → 1 ≤ Caps.cSize c → capsOK? c sched st ≡ true →
  all (valCaps? c sl (obs u)) vals ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  all (nestClosOK? c sl) vals ≡ true →
  thruRoomWOK W sf op nid p id now vals sched st →
  thruRoomQOK c sf op nid p id now vals sched st →
  thruFitOK (nestFac (Caps.cSize c) W
              * ((nodesMax st ⊔ nestDᵛˢ vals)
                 + nestU (Caps.cSize c) (nestUnit e sl)))
    sf op nid p id now vals sched st
thruFit-frame {e = e} c W sl sf id now op nid p vals sched st
  hsl h1w hlv h1S hcap hval hss hclos hrw hrq =
  thruFitOK-mono
    (nestB (Caps.cSize c) W (nestUnit e sl) (nestDᵛˢ vals) (Caps.cSize c))
    (nestFac (Caps.cSize c) W
      * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl)))
    sf op nid p id now vals sched st
    (≤-trans (nestB-at (Caps.cSize c) W (nestUnit e sl) (nestDᵛˢ vals))
             (*-monoʳ-≤ (nestFac (Caps.cSize c) W)
                (+-monoˡ-≤ (nestU (Caps.cSize c) (nestUnit e sl))
                   (m≤n⊔m (nodesMax st) (nestDᵛˢ vals)))))
    (thruFit-vals c sl (nestDᵛˢ vals) W 0 (Caps.cSize c) sf op nid p id now
       vals sched st hsl h1S (capsOK?⇒nest c sched st hcap)
       (all-impl (nestClosOK? c sl) (nestValOK? c (obs _))
          (λ o → nestClosOK?⇒val c sl o) vals hclos)
       hclos
       (thruRoom-frame c W sl sf id now op nid p vals sched st
          hsl (capsOK?⇒nest c sched st hcap)
          (all-impl (nestClosOK? c sl) (nestValOK? c (obs _))
             (λ o → nestClosOK?⇒val c sl o) vals hclos)
          hval hclos hrw hrq)
       (nestB-base (Caps.cSize c) W (nestUnit e sl) (nestDᵛˢ vals) 0))

-- The head itself is now the walk and the wrap composed at that
-- grant, with the base term absorbed by positivity of the factor.
stepFrame-nodes-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (p : Path Γ u t)
  (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  1 ≤ W → length vals ≤ W → capsOK? c sched st ≡ true →
  all (valCaps? c sl (obs u)) vals ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  all (nestClosOK? c sl) vals ≡ true →
  1 ≤ Caps.cSize c →
  thruRoomWOK W sf op nid p id now vals sched st →
  thruRoomQOK c sf op nid p id now vals sched st →
  let r = stepFrame sf id now (thru-outer op nid) p vals fin sched st in
  length (proj₁ r) ≤ W →
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ nestFac (Caps.cSize c) W
      * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))
stepFrame-nodes-thru {e = e} c W sl sf id now op nid p vals fin sched st
  hsl h1w hlv hcap hval hss hclos h1S hrw hrq hlr =
  ⊔-lub
    (≤-trans (proj₁ (proj₂ WRAP))
      (≤-trans (proj₁ (proj₂ WALK))
        (⊔-lub (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))
                        (raiseN (Caps.cSize c) W
                          (nodesMax st ⊔ nestDᵛˢ vals)
                          (nestU (Caps.cSize c) (nestUnit e sl))))
               ≤-refl)))
    (≤-trans (≤-reflexive (cong nestDᵛˢ (proj₁ WRAP))) (proj₁ WALK))
  where
  G = nestFac (Caps.cSize c) W
        * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU (Caps.cSize c) (nestUnit e sl))
  w = thruWalk sf op nid p id now vals sched st
  WALK = thruWalk-nest G sf op nid p id now vals sched st
           (thruFit-frame c W sl sf id now op nid p vals sched st
              hsl h1w hlv h1S hcap hval hss hclos hrw hrq)
  WRAP = thruWrap-nest op nid fin (proj₁ w) (proj₁ (proj₂ w))
           (proj₁ (proj₂ (proj₂ w))) (proj₂ (proj₂ (proj₂ w)))

-- What the outer's burst has to satisfy, emit by emit and at the state
-- each frame leaves: the invariant holds there, the values it carries
-- are admissible, and their joined nesting is already inside the grant.
-- It mirrors `pushFitOK` exactly, which is what lets the fit be read
-- off it rather than asserted alongside it.
pushValsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsOK c sl B W m fuel op nid κ id now [] sched st = ⊤
pushValsOK {Γ = Γ} {e = e} {u = u} c sl B W m fuel op nid κ id now (em ∷ ems) sched st =
  (Sched.slots sched ≡ sl)
  × (nestCapsOK? c sched st ≡ true)
  × (all (nestValOK? c (obs u)) (proj₁ sp) ≡ true)
  × (all (nestClosOK? c sl) (proj₁ sp) ≡ true)
  × thruRoomOK c W fuel op nid κ id now (proj₁ sp) sched st
  × (nestDᵛˢ (proj₁ sp) ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m)
  × pushValsOK c sl B W m fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

-- AND IT SPLITS IN TWO, along the line the risk actually runs on.  Five
-- of the six conjuncts are the caps bundle a burst carries -- the
-- slots, the invariant, admissibility written and admissibility under
-- the telescope, room at the node -- and the sixth is the MEASURE.  A head owes both, but it owes them for
-- different reasons: the bundle mirrors what the caps face already
-- carries along a burst, while the measure is where a substituting
-- frame can outrun its grant.  Stating them apart is what lets the
-- second be probed and ranked without the first riding along.
--
-- Both halves recurse over the SAME stream at the SAME states, since
-- the frame each emit leaves is a function of the emit and the state
-- and of neither half's own content -- which is why the join below is
-- a plain induction and not a re-derivation.
pushValsCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsCapsOK c sl W fuel op nid κ id now [] sched st = ⊤
pushValsCapsOK {Γ = Γ} {u = u} c sl W fuel op nid κ id now (em ∷ ems) sched st =
  (Sched.slots sched ≡ sl)
  × (nestCapsOK? c sched st ≡ true)
  × (all (nestValOK? c (obs u)) (proj₁ sp) ≡ true)
  × (all (nestClosOK? c sl) (proj₁ sp) ≡ true)
  × thruRoomOK c W fuel op nid κ id now (proj₁ sp) sched st
  × pushValsCapsOK c sl W fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

pushValsNestOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsNestOK c sl B W m fuel op nid κ id now [] sched st = ⊤
pushValsNestOK {Γ = Γ} {e = e} {u = u} c sl B W m fuel op nid κ id now (em ∷ ems) sched st =
  (nestDᵛˢ (proj₁ sp) ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m)
  × pushValsNestOK c sl B W m fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

pushVals-both : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  pushValsCapsOK c sl W fuel op nid κ id now str sched st →
  pushValsNestOK c sl B W m fuel op nid κ id now str sched st →
  pushValsOK c sl B W m fuel op nid κ id now str sched st
pushVals-both c sl B W m fuel op nid κ id now [] sched st hcap hnest = tt
pushVals-both {Γ = Γ} {u = u} c sl B W m fuel op nid κ id now (em ∷ ems) sched st
              (hsl , hc , hv , hcl , hr , restC) (hn , restN) =
  hsl , hc , hv , hcl , hr , hn
  , pushVals-both c sl B W m fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
      restC restN
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

-- AND THE CAPS HALF SPLITS AGAIN, three ways and along its own
-- conjuncts, because its five obligations are not one kind of fact.
-- Two ride the STATE CHAIN -- the slots equation and the invariant,
-- re-read at the frame each instant leaves; two are properties of the
-- STREAM ALONE -- admissibility written and admissibility under the
-- telescope, read off the split values with no state anywhere in
-- their type; and one is the ROOM WALK, the per-value march through
-- `thruConsume` at the wrap's own node.  Splitting by conjunct is
-- what isolates the risk: the admissibility half can be walked with
-- no caps state threaded through it at all, the state half reduces
-- per value to the `thruStep` facts and per instant to the wrap's
-- `setNode`, and what remains hard is exactly the room walk and
-- nothing else.  All three recurse at the SAME states, so the join
-- below is a plain zip.
pushValsStOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsStOK c sl fuel op nid κ id now [] sched st = ⊤
pushValsStOK {Γ = Γ} {u = u} c sl fuel op nid κ id now (em ∷ ems) sched st =
  (Sched.slots sched ≡ sl)
  × (nestCapsOK? c sched st ≡ true)
  × pushValsStOK c sl fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

pushValsAdmOK : ∀ {n} {Γ : Ctx n} {u}
  (c : Caps) (sl : Slots Γ) (str : Stream Γ (obs u)) → Set
pushValsAdmOK c sl [] = ⊤
pushValsAdmOK {Γ = Γ} {u = u} c sl (em ∷ ems) =
  (all (nestValOK? c (obs u)) (proj₁ sp) ≡ true)
  × (all (nestClosOK? c sl) (proj₁ sp) ≡ true)
  × pushValsAdmOK c sl ems
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)

pushValsRoomOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsRoomOK c sl W fuel op nid κ id now [] sched st = ⊤
pushValsRoomOK {Γ = Γ} {u = u} c sl W fuel op nid κ id now (em ∷ ems) sched st =
  thruRoomOK c W fuel op nid κ id now (proj₁ sp) sched st
  × pushValsRoomOK c sl W fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

-- AND THE ROOM RECORD'S THREE HALVES, EACH FOLDED OVER THE BURST THE
-- SAME WAY THE ROOM ITSELF IS.  The room walk is a checked fold of the
-- frame's own record, so what the burst leaves owe is no longer the
-- record but its inputs: the arrivals' written admissibility against
-- the telescope, the arrival widths the frame reads, and the queue
-- reading at each state the walk passes through.
pushValsWidOK : ∀ {n} {Γ : Ctx n} {u}
  (c : Caps) (sl : Slots Γ) (str : Stream Γ (obs u)) → Set
pushValsWidOK c sl [] = ⊤
pushValsWidOK {Γ = Γ} {u = u} c sl (em ∷ ems) =
  (all (valCaps? c sl (obs u)) (proj₁ sp) ≡ true)
  × pushValsWidOK c sl ems
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)

pushValsWOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsWOK W fuel op nid κ id now [] sched st = ⊤
pushValsWOK {Γ = Γ} {u = u} W fuel op nid κ id now (em ∷ ems) sched st =
  thruRoomWOK W fuel op nid κ id now (proj₁ sp) sched st
  × pushValsWOK W fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

pushValsQOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → Set
pushValsQOK c fuel op nid κ id now [] sched st = ⊤
pushValsQOK {Γ = Γ} {u = u} c fuel op nid κ id now (em ∷ ems) sched st =
  thruRoomQOK c fuel op nid κ id now (proj₁ sp) sched st
  × pushValsQOK c fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

pushVals-caps-join : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  pushValsStOK c sl fuel op nid κ id now str sched st →
  pushValsAdmOK c sl str →
  pushValsRoomOK c sl W fuel op nid κ id now str sched st →
  pushValsCapsOK c sl W fuel op nid κ id now str sched st
pushVals-caps-join c sl W fuel op nid κ id now [] sched st hst hadm hroom = tt
pushVals-caps-join c sl W fuel op nid κ id now (em ∷ ems) sched st
    (hsl , hc , restSt) (hv , hcl , restAdm) (hr , restRoom) =
  hsl , hc , hv , hcl , hr
  , pushVals-caps-join c sl W fuel op nid κ id now ems _ _ restSt restAdm restRoom

-- AND THE STATE HALF RIDES THE OTHER TWO: given the pair at entry,
-- admissibility and room supply exactly what the per-instant step
-- consumes, so the whole state chain is a checked induction and the
-- leaf it leaves behind is one fact about one state -- the exit pair.
pushValsSt-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  pushValsAdmOK c sl str →
  pushValsRoomOK c sl W fuel op nid κ id now str sched st →
  pushValsStOK c sl fuel op nid κ id now str sched st
pushValsSt-walk c sl W fuel op nid κ id now [] sched st hsl hc hadm hroom = tt
pushValsSt-walk {Γ = Γ} {u = u} c sl W fuel op nid κ id now (em ∷ ems) sched st
    hsl hc (hv , hcl , restAdm) (hr , restRoom) =
  hsl , hc
  , pushValsSt-walk c sl W fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
      (trans (KeepsC.slotsEq (stepFrame-keeps fuel id now (thru-outer op nid) κ (proj₁ sp)
                             (proj₂ (proj₂ sp)) sched st)) hsl) S restAdm restRoom
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st
  S = stepThru-caps c sl W fuel op nid κ id now (proj₁ sp)
        (proj₂ (proj₂ sp)) sched st hsl hc hv hcl hr

-- AND THE ROOM WALK IS A CHECKED FOLD.  Each instant's arrivals are
-- handed to the frame's own record, and the state pair the next
-- instant is read at comes from the same per-instant step the state
-- walk beside this one advances by -- so the two walks agree on where
-- they are by construction rather than by a shared assumption.
pushVals-room-join : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (W : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  nestCapsOK? c sched st ≡ true →
  pushValsAdmOK c sl str →
  pushValsWidOK c sl str →
  pushValsWOK W fuel op nid κ id now str sched st →
  pushValsQOK c fuel op nid κ id now str sched st →
  pushValsRoomOK c sl W fuel op nid κ id now str sched st
pushVals-room-join c sl W fuel op nid κ id now [] sched st
  hsl hc hadm hwid hw hq = tt
pushVals-room-join {Γ = Γ} {u = u} c sl W fuel op nid κ id now (em ∷ ems) sched st
    hsl hc (hv , hcl , restAdm) (hd , restWid) (hw , restW) (hq , restQ) =
  R
  , pushVals-room-join c sl W fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
      (trans (KeepsC.slotsEq (stepFrame-keeps fuel id now (thru-outer op nid) κ (proj₁ sp)
                             (proj₂ (proj₂ sp)) sched st)) hsl) S restAdm restWid restW restQ
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st
  R = thruRoom-frame c W sl fuel id now op nid κ (proj₁ sp) sched st
        hsl hc hv hd hcl hw hq
  S = stepThru-caps c sl W fuel op nid κ id now (proj₁ sp)
        (proj₂ (proj₂ sp)) sched st hsl hc hv hcl R

-- and the lift, CHECKED: one emit's fit is its values' fit, and the
-- rest runs at the frame the emit left
pushFit-ems : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m m′ : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  suc m ≤ m′ →
  pushValsOK c sl B W m fuel op nid κ id now str sched st →
  ⦃ _ : FaceOK c sl ⦄ →
  pushFitOK (nestB (Caps.cSize c) W (nestUnit e sl) B m′)
    fuel op nid κ id now str sched st
pushFit-ems c sl B W m m′ fuel op nid κ id now [] sched st hm vals = tt
pushFit-ems {Γ = Γ} {u = u} c sl B W m m′ fuel op nid κ id now (em ∷ ems) sched st hm
            (hsl , hc , hv , hcl , hr , hn , rest) =
  thruFit-vals c sl B W m m′ fuel op nid κ id now (proj₁ sp) sched st
    hsl hm hc hv hcl hr hn
  , pushFit-ems c sl B W m m′ fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf)))) hm rest
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

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
--
-- AND THE GRANT NAMES `κ` NOWHERE, WHICH IS ONLY SOUND BECAUSE A PATH
-- FRAME MINTS AT DELIVERY RATHER THAN AT SUBSCRIBE.  The reading that
-- would break it is a `map-f`, whose `pathNestF` factor is `2 ^ sizeᵗ`
-- of the function while every other frame's is one, and whose body is
-- an observable that gets SUBSCRIBED when a value passes it: if that
-- happened inside the frame, an arbitrarily deep body would install
-- arbitrarily deep state under a bound that cannot see the path.
-- Asked directly, at a deferred body two deep and the same body six
-- deep, both readings come back as the table the run started from --
-- the frame mints nothing here.  That is what
-- puts the path factor on the DELIVERY face's bill and off this one,
-- and it is why the omission is a property rather than an oversight.

-- AND THE CAP THE CONCLUSION IS READ AT IS THE CLAUSE'S OWN CHOICE,
-- WHICH IS THE ONE THING THE PREMISES CANNOT SUPPLY.  A substituting
-- head writes an emission the arrival's own cap does not dominate --
-- the tree's bound on a substituted value bases at the cap and
-- multiplies, so a premise asking the emission back under it is
-- unsatisfiable rather than merely unproven.  What the caps face does
-- instead, in every one of its frame lemmas, is report a LEVEL: the
-- conclusion is existential in how far the cap has been stepped, so a
-- parent picks whatever level its child reports rather than owing a
-- level fixed in advance.  Here that is one `Σ ℕ` in front of the
-- triple and nothing else -- the premises stay at the cap handed in,
-- and a clause that needs no step returns zero, at which the grant is
-- the cap-keyed one letter for letter.
NestAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Set
NestAt {Γ = Γ} {t = t} {e = e} c d sl B W g o κ id now sched st =
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs _) o ≡ true →
  -- THE CAP DOMINATES THE ARRIVAL'S CLOSURE, not merely its written
  -- size.  The burst face's own grant is keyed on the written size and
  -- would not ask for this; what asks is the FIT, which crosses into
  -- the arr-keyed inner, and that key sees through the telescope.  The
  -- unconditional reading of that key does not survive a substituting
  -- slot definition, so this is the true statement replacing a false
  -- one rather than a weakening -- and on a slot-free arrival the two
  -- premises coincide.
  nestClosOK? c sl o ≡ true →
  nestDᵉ o ≤ B →
  descW g o κ id now sched st ≤ W →
  -- AND THE LEVEL IS BOUNDED, which is what makes the existential
  -- collapsible at all.  An unbounded level cannot be read at a
  -- successor cap: `iterSize` runs away with the count, so a consumer
  -- reading the grant at `frameStep j c` for an arbitrary `j` has no
  -- ceiling to compare against.  The bound is the caps face's own
  -- count at the descent's depth fuel, JOINED WITH THE ENTRY CAP'S OWN
  -- SIZE FIELD -- and the join is not slack.  A `*All` arm reads its
  -- arrivals one caps level up, because an arrival is the head's syntax
  -- with payloads substituted in and that crosses the size key; the
  -- level it crosses by is the head's own written size, which is what
  -- the second summand names.  The join stays OUT of the count, and
  -- `Refuted.PushVals-Adm-Map` is why: the count is only known to be
  -- positive where the cap grants a registration, so at an empty
  -- registry field a level bounded by the count alone is zero, the step
  -- is the identity, and the flat statement it collapses to is the one
  -- that witness refutes.  Folding the size in would therefore need a
  -- positivity premise on every statement of this family; keeping it
  -- beside the count leaves that premise at the one consumer which
  -- finally collapses the existential, where it is already proven.
  depthE g o κ id now sched st ≤ d →
  let r = subscribeE g o κ id now sched st in
  Σ ℕ λ j →
  let G = nestB (Caps.cSize (frameStep j c)) W (nestUnit e sl) B (syncSizeᵉ o) in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))) ≤ G)
  × (nodesMax (proj₂ (proj₂ r)) ≤ nodesMax st ⊔ G)
  × (∀ (k : NodeId) → nodeNestAt k (proj₂ (proj₂ r)) ≤ nodeNestAt k st ⊔ G)

-- THE `*All` WRAP VOCABULARY.  One op-indexed spelling of what the
-- evaluator writes three ways: the wrap expression a head's premises
-- are read over, and the fresh state installed under it.  Both reduce
-- definitionally at each constructor, so a premise stated over
-- `allWrap op lim b` IS the merge premise at `mergeAllᵒ`, letter for
-- letter -- which is what lets one burst statement stand where three
-- stood.  The limit rides only the merge arm; the other two ops
-- discard it by matching the op first.
allWrap : ∀ {n} {Γ : Ctx n} {u} → AllOp → Maybe ℕ → Closed Γ (obs u) → Closed Γ u
allWrap mergeAllᵒ lim b = mergeAllᵉ lim b
allWrap switchᵒ   _   b = switchAllᵉ b
allWrap exhaustᵒ  _   b = exhaustAllᵉ b

allFresh : ∀ {n} {Γ : Ctx n} (u : Ty) → AllOp → Maybe ℕ → NodeState Γ
allFresh u mergeAllᵒ lim = mergeAll-st {t = u} lim 0 [] false
allFresh _ switchᵒ   _   = switch-st nothing false
allFresh _ exhaustᵒ  _   = exhaust-st false false

-- and the four facts the wrap vocabulary carries across its ops: a
-- fresh node passes the width check, the wrap's admissibility and
-- closure premises narrow to the body's -- each wrap costs one `suc`
-- in both measures -- and the body's descent under the installed frame
-- is inside the wrap's
allFresh-wid : ∀ {n} {Γ : Ctx n} (Wd : ℕ) (sl : Slots Γ)
  (u : Ty) (op : AllOp) (lim : Maybe ℕ) →
  nodeWidᴺ? Wd sl (allFresh u op lim) ≡ true
allFresh-wid Wd sl u mergeAllᵒ lim = refl
allFresh-wid Wd sl u switchᵒ   _   = refl
allFresh-wid Wd sl u exhaustᵒ  _   = refl

allWrap-valOK : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (op : AllOp) (lim : Maybe ℕ)
  (b : Closed Γ (obs u)) →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestValOK? c (obs (obs u)) b ≡ true
allWrap-valOK c mergeAllᵒ lim b hv =
  ≤ᵇ-true (syncSizeᵉ b) (Caps.cSize c)
    (≤-trans (n≤1+n (syncSizeᵉ b))
             (≤ᵇ⇒≤ (suc (syncSizeᵉ b)) (Caps.cSize c) (T-to hv)))
allWrap-valOK c switchᵒ   _   b hv =
  ≤ᵇ-true (syncSizeᵉ b) (Caps.cSize c)
    (≤-trans (n≤1+n (syncSizeᵉ b))
             (≤ᵇ⇒≤ (suc (syncSizeᵉ b)) (Caps.cSize c) (T-to hv)))
allWrap-valOK c exhaustᵒ  _   b hv =
  ≤ᵇ-true (syncSizeᵉ b) (Caps.cSize c)
    (≤-trans (n≤1+n (syncSizeᵉ b))
             (≤ᵇ⇒≤ (suc (syncSizeᵉ b)) (Caps.cSize c) (T-to hv)))

allWrap-closOK : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u)) →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  nestClosOK? c sl b ≡ true
allWrap-closOK c sl mergeAllᵒ lim b hcl =
  ≤ᵇ-true (closSizeᵉ (slotClos sl) b) (Caps.cSize c)
    (≤-trans (n≤1+n (closSizeᵉ (slotClos sl) b))
             (≤ᵇ⇒≤ (suc (closSizeᵉ (slotClos sl) b)) (Caps.cSize c) (T-to hcl)))
allWrap-closOK c sl switchᵒ   _   b hcl =
  ≤ᵇ-true (closSizeᵉ (slotClos sl) b) (Caps.cSize c)
    (≤-trans (n≤1+n (closSizeᵉ (slotClos sl) b))
             (≤ᵇ⇒≤ (suc (closSizeᵉ (slotClos sl) b)) (Caps.cSize c) (T-to hcl)))
allWrap-closOK c sl exhaustᵒ  _   b hcl =
  ≤ᵇ-true (closSizeᵉ (slotClos sl) b) (Caps.cSize c)
    (≤-trans (n≤1+n (closSizeᵉ (slotClos sl) b))
             (≤ᵇ⇒≤ (suc (closSizeᵉ (slotClos sl) b)) (Caps.cSize c) (T-to hcl)))

allWrap-descW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  descW g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ) id now
    (proj₂ (mintNode sched))
    (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  ≤ descW g (allWrap op lim b) κ id now sched st
allWrap-descW g mergeAllᵒ lim b κ id now sched st = descW-merge g lim b κ id now sched st
allWrap-descW g switchᵒ   lim b κ id now sched st = descW-switch g b κ id now sched st
allWrap-descW g exhaustᵒ  lim b κ id now sched st = descW-exhaust g b κ id now sched st

postulate
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
  --   there reports `frameStep (j + j′)` and charges `j′` -- while the
  --   shared statement's conclusion names ONE cap.  The grant is keyed
  --   on `cSize`, so a stepped cap is a larger key and a larger grant,
  --   and a parent whose own obligation is fixed owes the smaller one.
  --   What the route needs is the caps face's OTHER half, which this
  --   statement does not have: there the parent's obligation is
  --   existential in the level too, so it picks the level its child
  --   reports and the mismatch never arises.  Dead against the shared
  --   statement as written; a restatement of that statement, not a
  --   proof, is what reopens it.
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
  --   moves the index by more than one step.  Nor the LEVEL, which
  --   every row reads at zero -- so the bound conjunct is uncovered and
  --   what the rows reach is the three beside it.
  subscribeE-nest-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
    (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u) (b : Closed Γ s)
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    NestAt c d sl B W g (scanᵉ f z b) κ id now sched st
  -- THE `*All` BURST LEAVES, CAPS HALF, SPLIT BY CONJUNCT.  The
  -- masters below the block are REAL BODIES over these, so what each
  -- owes is one kind of fact about the outer's burst and nothing
  -- else.  The EXIT leaf carries the slots equation and the
  -- invariant at the one state the subscribe leaves; the chain from
  -- there is a checked walk over the per-instant step, so the whole
  -- state half stands on this single fact.  The
  -- ADMISSIBILITY leaf is a property of the stream alone -- no state
  -- in its conclusion's type -- so its walk needs no caps threading
  -- at all.  The room is no longer a leaf: it is a checked fold of
  -- the frame's own record, standing on the three that follow it --
  -- the arrivals' width key, the frame widths, and the queue reading.

  -- The stream's own half: every instant's values admissible, written
  -- and under the telescope.  It is stated over ANY subscription at
  -- ANY path rather than over the `*All` arm that consumes it: the
  -- arm's premises reduce to these by the same bundle its own exit
  -- leaf already spends, and generality costs nothing here because
  -- there is no state in the conclusion for a head to have to
  -- re-establish.  The proven twin to grind it against is the exit
  -- walk over the same `subscribeE`, which carries this face's whole
  -- state half at exactly these premises and says nothing about the
  -- burst it returns.
  --
  -- AND IT IS FALSE AT THE FLAT CAP THIS FACE CARRIES.  Every premise
  -- reads the head's SYNTAX, which counts a bound variable as one; an
  -- emitted value is that syntax with the payload SUBSTITUTED IN, so a
  -- step function naming its payload twice hands back about twice the
  -- payload while contributing a constant to the head.  The gap grows
  -- with the payload and no premise can see it.  The repair is not a
  -- premise on this leaf: the arrival is SUBSCRIBED -- the merge arm
  -- hands it to the walk's own re-entry -- so what fails is the walk's
  -- PREMISE surviving this arm, and the only device that preserves it
  -- is a premise that SURVIVES A SUBSTITUTION, which this one does not.
  -- One device does, and it is the caps face's LEVEL: arrivals read at
  -- the entry cap STEPPED.  The state invariant is untouched by it --
  -- it reads the WIDTH field over the node table and no size at all --
  -- so what is owed is the arm's premise and not its state chain.
  --
  -- AND THE LEVEL HAS TO BE THE INSTANT'S, WHICH IS THE MECHANISM
  -- MOVING RATHER THAN THIS LEAF.  This face is grant-free end to end
  -- -- caps, room, width, queue and state folds all conclude the exit
  -- pair -- so the larger-grant objection recorded one block up reaches
  -- the grant-carrying `*All` rows and not these; but the join that
  -- fuses the two halves names the caps premises and the grant's key as
  -- ONE cap, and that cap is not free to be split, because the merge
  -- step spends the ARRIVAL'S closure size as the frame charge's own
  -- exponent.  The grant's exponent IS the bound on the arriving
  -- value's size, so any device that grows that bound grows the grant,
  -- and this arm's arrivals are emissions no entry cap dominates.
  --
  -- SO THE TWO CAPS ARE CONSECUTIVE INSTANT CAPS, AND NOTHING SMALLER
  -- WORKS.  A run's values are assembled from the program's own
  -- templates, and the caps recurrence already separates one instant
  -- from the next by a single blowup that the caps face proves absorbs
  -- one instant's whole growth.  Stating the walk over that PAIR --
  -- premises at the instant's cap, conclusion at its successor's --
  -- puts the emission inside a bound that exists, and the top owes the
  -- successor on both sides, so no parent is left owing the smaller
  -- one.  The cost is that the pair threads every walk predicate, which
  -- is what it was abandoned for once, before the cheaper devices below
  -- were closed.

  -- AND THE PAIR IS OWED ON THE SIZE AXIS ALONE, which is what makes
  -- the restatement affordable rather than a rewrite of the face.  The
  -- arrival's PENDING WIDTH is measured not to move under the very
  -- substitution that breaks its size: a step function naming its
  -- payload twice mentions ONE observable twice, and the frame measure
  -- counts observables rather than mentions.  So the state invariant --
  -- which reads the node table's widths and no size at all -- stays at
  -- the entry cap on both sides of every walk predicate that carries
  -- it, and what takes the stepped cap is the arrival's size key and
  -- the closure key beside it.
  --
  -- AND WHAT IS LEFT IS ONE BOOLEAN OVER THE WHOLE SUBSCRIPTION, not a
  -- per-emit record: the walk down to the emits is proven, and so is
  -- the collapse of the record's two conjuncts into one, since an
  -- arrival's sync reading sits under its resolved closure.  So the
  -- leaf reads closures alone, emit by emit, in the shape the caps
  -- face already states its own arrival predicate in.
  -- REFUTED: `Refuted.PushVals-Adm-Map`
  -- DEAD ROUTE: flattening at a cap CLOSED UNDER a descent's worth of
  --   substitutions is structurally dead, and not for want of
  --   arithmetic.  The walk's flattened grant is handed to the delivery
  --   currency, which prices a level at a SQUARE of the cap and is
  --   closed under the fan recurrence and nothing wider, while one step
  --   of the caps face's size function iterates a multiply once per
  --   unit of cap -- so no closure of the cap under substitution fits
  --   inside it.  Minting a currency here is the part that is dead; the
  --   LEVEL is untouched, and is the one the delivery currency already
  --   prices, since its ladder is per level.  `subscribeE-nest-slot`
  --   carries the worked threading and a pointer to the algebra.
  -- DEAD ROUTE: an INTRINSIC measure on the syntax dominating what that
  --   syntax can emit -- the device that would cost no cap at all -- is
  --   dead by unsatisfiability rather than by difficulty, and the tree
  --   already proves why.  The bound on a value with a payload
  --   substituted in is `applyFn-iterSize`, whose right side is the
  --   caps face's own size iteration based AT THE CAP; so a premise
  --   asking that an emission read inside the cap asks, at one single
  --   iteration and a payload of any size, for `S * suc (2 * V) ≤ S`.
  --   No sharper measure repairs it, because the sharpening would have
  --   to beat a bound the caps face spends everywhere.  A key that
  --   dominates an emission is therefore not a key at this cap, and the
  --   cap has to move -- which is the LEVEL and nothing else.
  -- DEAD ROUTE: reading the caps premises at a stepped cap while the
  --   grant stays at the entry one -- the cheap form of the level,
  --   confined to this family and needing no instant index.  The merge
  --   step spends the arrival's closure size AS the grant's exponent,
  --   so the two occurrences of the cap are one quantity and the split
  --   is not a split.  This is the third closed subdivision of the same
  --   region, which is what puts the finding on the mechanism.
  -- PROBED: `Probed.PushVals-Caps`, whose coverage and its boundary
  --   are stated at `pushVals-caps-queue` below.
  -- RECOVERY: `git show e55d850` restores the level-lifting machinery
  --   these four used to need -- `arrCapAt-size`, `nestValOK?-cap`,
  --   `allWrap-1≤`.  It went out with the nest half, which stopped
  --   re-deriving its bound at the lifted cap and started reading the
  --   child's; a caps leaf whose proof needs an arrival premise carried
  --   UP a level is what would want it back.
  subscribeE-burst-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas) (o : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) o ≡ true →
    nestClosOK? c sl o ≡ true →
    descW g o κ id now sched st ≤ W →
    burstNest? (arrCapAt (Caps.cSize c) c) sl
      (proj₁ (subscribeE g o κ id now sched st)) ≡ true
  -- The arrivals' width key: every value the descent hands back reads
  -- inside the cap at the telescope the frame is standing in.  It is
  -- the one half of the room the frame's own record cannot recover,
  -- since it is a fact about the VALUE and the caps at the frame's
  -- state say nothing about a value that has not arrived.
  --
  -- AND IT DIES TO THE SAME SUBSTITUTION ITS SIBLING DOES, at the same
  -- witness and for the same reason: the key is a size bound, and an
  -- arrival is the head's syntax with the payload substituted in.  The
  -- WIDTH half of the key is not what fails -- the witness sets that
  -- field wide so the reading is unambiguous -- which is why what is
  -- owed here is the arm's level and not a width premise.
  --
  -- AND WHAT IS LEFT IS THE CAPS FACE'S OWN PREDICATE OVER THE WHOLE
  -- SUBSCRIPTION, not a per-emit record: the walk down to the emits is
  -- proven, so the leaf is `burstCaps?` of the descent's burst.  The
  -- face reports exactly that boolean for exactly this `subscribeE`,
  -- and it is importable here -- neither module reaches the other, so
  -- the ban is on a CYCLE and not on a direction.  What it reports at
  -- is a STEPPED cap, and that is the whole of what stands between
  -- them.
  --
  -- AND IT IS FALSE AS STATED, on the WIDTH half and at every level.
  -- The level moves the size axis and leaves the width field exactly
  -- where it was, deliberately: the invariant reads `cWid` and nothing
  -- else, which is what makes it the SAME boolean at the stepped cap
  -- and lets the arm hand its exit pair straight through.  So nothing
  -- here forbids a width of zero -- the two keys are size bounds and
  -- the invariant is satisfied by a table the descent has not written
  -- -- and a source that hands back an observable payload is absurd at
  -- the first instant.
  --
  -- AND A WIDTH KEY ON THE SOURCE DOES NOT REPAIR IT, which is the
  -- part worth knowing before the next attempt: an `ofᵉ`'s own reading
  -- joins its payload COUNT with its parked half, and the emitted
  -- inner's delivered width appears in neither.  The quantity that
  -- covers it is the inner width, and the proven bound delivering all
  -- three at once is `wid-iterFold` -- whose right side is the width
  -- axis ITERATED, at the syntax size and over a slot-width key this
  -- face does not carry.
  --
  -- AND THE ITERATE IS NOT REACHABLE BY STEPPING THIS CAP, which is
  -- what three attempts have now established between them and is the
  -- thing to read before a fourth.  The frame's own room record reads
  -- an arrival's `pWᵉ` against the ENTRY width and nothing else, so
  -- the frozen width is not this walk's convenience -- it is what the
  -- room demands, and a cap that steps it leaves the room unstatable
  -- where it stood.  The step then has to move INTO the room, and the
  -- room is threaded once per arrival across a fold, which is the
  -- per-arrival recurrence the exit family already died to.  So the
  -- iterated width has to arrive from somewhere that already holds
  -- it, and the instant's own cap does: the width field there is the
  -- iterate by construction, which is why the bundle at that cap is a
  -- proven fact rather than a hypothesis anyone acquires.
  -- REFUTED: `Refuted.PushVals-Adm-Map`
  -- REFUTED: `Refuted.Subscribe-Burst-Width` sets the width field to
  --   zero, pins the three keys true there, and crosses at the first
  --   emitted inner -- and its last row pins that the walk stated over
  --   the node table SURVIVES that witness, so the crossing is this
  --   statement's alone and not the exit pair's.
  -- DEAD ROUTE: a delivered-width key on the SOURCE, carried at the
  --   entry field, does not survive the walk it would have to be
  --   threaded through.  It kills the refuting witness -- that source
  --   parks a body wider than the field -- so the leaf itself looks
  --   repairable, and the arm that breaks it is one hop away: a
  --   substituting head hands back its own syntax with the payload
  --   substituted in, and the proven bound for that is `wid-subΘ`,
  --   whose right side is the width axis ITERATED at the syntax size.
  --   A premise stated at the entry field cannot be re-established at
  --   the next arm, so the key would have to be re-acquired at every
  --   substituting head and there is nothing to acquire it from.
  -- DEAD ROUTE: stepping the arrival cap's WIDTH is dead in all three
  --   parameterisations tried -- a level carried on the statement, a
  --   constant one step above entry, and the frozen field simply
  --   deleted so both axes advance together.  The last of those is the
  --   cheapest to re-run and the most informative: the `*All` arm's
  --   exit walk then reports at the stepped cap and its own conclusion
  --   is owed at the entry cap, and no widening runs that way.  What
  --   blocks every version is one conjunct -- the room record's
  --   arrival width, read against the entry field -- so a repair that
  --   does not move that conjunct has not moved anything.
  -- PROBED: `Probed.PushVals-Caps`, whose coverage and its boundary
  --   are stated at `pushVals-caps-queue` below.
  subscribeE-burst-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas) (o : Closed Γ u)
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) o ≡ true →
    nestClosOK? c sl o ≡ true →
    descW g o κ id now sched st ≤ W →
    burstCaps? (arrCapAt (Caps.cSize c) c) sl
      (proj₁ (subscribeE g o κ id now sched st)) ≡ true
  -- The frame widths the burst's arrivals drive, per arrival and at
  -- the state its predecessor left.  This is the measure half of the
  -- room and the only one of the three that reads `W`, so it is where
  -- a grant that is too small shows up.
  -- PROBED: `Probed.PushVals-Caps`, whose coverage and its boundary
  --   are stated at `pushVals-caps-queue` below.
  pushVals-caps-burstW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas)
    (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (allWrap op lim b) ≡ true →
    nestClosOK? c sl (allWrap op lim b) ≡ true →
    descW g (allWrap op lim b) κ id now sched st ≤ W →
    let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
            id now (proj₂ (mintNode sched))
            (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
    in pushValsWOK W g op (proj₁ (mintNode sched)) κ id now
         (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
  -- The queue reading at each state the burst passes through: a merge
  -- node parked at the wrap holds strictly fewer than the width field
  -- grants, so one more arrival still fits.  The caps at that state
  -- cannot supply it -- they admit a queue as long as the field, and
  -- the record asks the field for one more -- which is why it is a
  -- leaf of the burst rather than a consequence of the invariant.
  --
  -- AND IT TAKES THE WIDTH KEY BESIDE IT, because unconditionally it
  -- is FALSE.  At the EMPTY queue the wrap installs, the conclusion
  -- already reads `1 ≤ cWid`, so it asserts the width field is
  -- positive -- and every other premise reads the SIZE field or the
  -- slots, so nothing forbids a width of zero.  The repair is not a
  -- positivity premise cascading through the face: the arrivals' own
  -- key rules the witness out, since at width zero no arrival fits and
  -- the sibling leaf's conclusion is false at the very same program.
  -- REFUTED: `Refuted.Thru-Room-Frame`
  -- REFUTED: `Refuted.PushVals-Queue-Width`
  -- PROBED: `Probed.PushVals-Caps` inhabits all three of these leaves,
  --   and the admissibility beside them, at every constructor of the op
  --   axis -- which the rows therefore cover in FULL -- at the cap each
  --   value's own sync size gives, at two nesting depths and at limits
  --   0 and 1, with each head's written and CLOSURE premises pinned by
  --   `refl` rather than assumed.  The queue arm is resolved through a
  --   real node lookup at the merge and through an absurd one at the
  --   other two.  The RECURSION is covered at all three heads: the one
  --   route to a subscribe-frame burst longer than one instant is a
  --   share CONNECT, whose head instant rides in front of the def's
  --   plumbed burst, and the share-headed rows pin that burst at length
  --   TWO and inhabit the second instant at the state the first
  --   instant's step leaves.  Of the three, only the WIDTH KEY could
  --   have failed on its own -- it is a `refl` on a boolean, where the
  --   frame widths are taken as a quantified premise because the
  --   measure is sealed, and the queue arm's merge lookup is the one
  --   place a numeral is read.  NOT covered, a reading the rows make
  --   rather than a gap they leave: the invariant conjunct's
  --   discrimination, since the state the descent leaves carries one
  --   node and an empty registry and live set, so it reads true even at
  --   a cap granting nothing.
  --   AND THE SUBSTITUTION'S TWO AXES ARE READ APART, at the
  --   refutation's own dup-map program under a cap tight on BOTH
  --   fields: the size crosses and the pending width does not move,
  --   over a flat payload and over a payload that is itself pending.
  --   Two programs at one op, so it is a reading about the mechanism
  --   and not coverage of the axis.
  pushVals-caps-queue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
    (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (allWrap op lim b) ≡ true →
    nestClosOK? c sl (allWrap op lim b) ≡ true →
    descW g (allWrap op lim b) κ id now sched st ≤ W →
    let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
            id now (proj₂ (mintNode sched))
            (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
    in pushValsWidOK (arrCapAt j c) sl (proj₁ res) →
       pushValsQOK (arrCapAt j c) g op (proj₁ (mintNode sched)) κ id now
         (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
-- ONE BOUND ON THE WHOLE COLUMN DISCHARGES EVERY EMIT'S CONJUNCT.  The
-- obligation's threaded state is carried and never read: each conjunct
-- names its own emit's values and the grant, both independent of where
-- the walk has got to, so the induction spends only the two injections
-- of a fold of maxima into a concatenation.
--
-- The bound itself is no longer anyone's leaf: the `*All` arms hand it
-- in, having got it from the child subscription they already recursed
-- on -- the same `subscribeE` this walk is stated over, reported at
-- the child's own level and read at its join with the head's.
-- RECOVERY: `git show e55d850` restores `Probed.PushVals-Body-Key`,
--   whose harness runs a `*All` descent into the BODY at the body's own
--   key over two families -- a nesting tower and a substituting map --
--   and measures the delivered figure level by level.  Its coverage
--   claim is superseded by this walk and the arms above it, but the
--   families and the descent plumbing are what a future rate question
--   would otherwise rebuild.
pushVals-nest-ems : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (sl : Slots Γ) (B W m : ℕ) (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (str : Stream Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γ u} str))
    ≤ nestB (Caps.cSize c) W (nestUnit e sl) B m →
  pushValsNestOK c sl B W m fuel op nid κ id now str sched st
pushVals-nest-ems c sl B W m fuel op nid κ id now []         sched st hb = tt
pushVals-nest-ems {Γ = Γ} {u = u} c sl B W m fuel op nid κ id now (em ∷ ems) sched st hb =
    ≤-trans (nestDᵛˢ-++ˡ (proj₁ sp) (proj₁ (splitBurst {A = Val Γ u} ems))) hb
  , pushVals-nest-ems c sl B W m fuel op nid κ id now ems
      (proj₁ (proj₂ (proj₂ (proj₂ sf)))) (proj₂ (proj₂ (proj₂ (proj₂ sf))))
      (≤-trans (nestDᵛˢ-++ʳ (proj₁ sp) (proj₁ (splitBurst {A = Val Γ u} ems))) hb)
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  sf = stepFrame fuel id now (thru-outer op nid) κ (proj₁ sp)
         (proj₂ (proj₂ sp)) sched st

-- AND THE WIDTH HALF WALKS THE SAME WAY, off the caps face's own burst
-- predicate rather than a bound: each emit owes the arrivals' widths at
-- the telescope, `burstCaps?` is that fact per emit already, and the
-- split's value column is a sublist of the emit's events.  So the leaf
-- underneath is one boolean over the whole subscription, in the caps
-- face's currency rather than this one -- which is the currency the
-- statement that would discharge it is written in.
pushVals-wid-ems : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ (obs u)) →
  burstCaps? c sl str ≡ true → pushValsWidOK c sl str
pushVals-wid-ems c sl []         h = tt
pushVals-wid-ems {u = u} c sl (em ∷ ems) h =
    splitEvents-vals-caps {u = u} c sl (InstEmit.events em) (proj₁ (∧-true _ _ h))
  , pushVals-wid-ems c sl ems (proj₂ (∧-true _ _ h))

-- AND THE ADMISSION HALF WALKS THE SAME WAY, off the burst predicate
-- rather than a per-emit record.  Its two conjuncts are not two facts:
-- the arrival's sync reading is under its resolved closure, so the
-- closure conjunct pays for the size conjunct pointwise and the walk
-- states one boolean, not two.
splitEvents-vals-nest : ∀ {n} {Γ : Ctx n} {u} {A : Set} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ (obs u)))) →
  all (eventNest? c sl) es ≡ true →
  all (nestClosOK? c sl) (proj₁ (splitEvents {A = A} es)) ≡ true
splitEvents-vals-nest c sl []               h = refl
splitEvents-vals-nest c sl (value v   ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-nest c sl es (proj₂ (∧-true _ _ h)))
splitEvents-vals-nest c sl (init _    ∷ es) h =
  splitEvents-vals-nest c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-nest c sl (close _ _ ∷ es) h =
  splitEvents-vals-nest c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-nest c sl (handoff _ ∷ es) h =
  splitEvents-vals-nest c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-nest c sl (complete  ∷ es) h =
  splitEvents-vals-nest c sl es (proj₂ (∧-true _ _ h))

pushVals-adm-ems : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ (obs u)) →
  burstNest? c sl str ≡ true → pushValsAdmOK c sl str
pushVals-adm-ems c sl []         h = tt
pushVals-adm-ems {Γ = Γ} {u = u} c sl (em ∷ ems) h =
    all-impl (nestClosOK? c sl) (nestValOK? c (obs u))
      (λ o → nestClosOK?⇒val c sl o)
      (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) CL
  , CL
  , pushVals-adm-ems c sl ems (proj₂ (∧-true _ _ h))
  where
  CL = splitEvents-vals-nest {A = Val Γ u} c sl (InstEmit.events em)
         (proj₁ (∧-true _ _ h))

pushVals-caps-adm : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  descW g (allWrap op lim b) κ id now sched st ≤ W →
  let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  in pushValsAdmOK (arrCapAt j c) sl (proj₁ res)
pushVals-caps-adm {u = u} c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw =
  pushVals-adm-ems (arrCapAt j c) sl (proj₁ res)
    (burstNest?-widen sl (proj₁ res)
       (arrCapAt-⊑ c (≤-trans (syncSizeᵉ-pos (allWrap op lim b))
                              (nestValOK?-size c (allWrap op lim b) hv)) hj)
       (subscribeE-burst-nest c sl W g b
          (thru-outer op nid ↠ κ) id now (proj₂ (mintNode sched))
          (installNode nid (allFresh u op lim) st)
          hsl
          (nestCapsOK?-setNode c nid (allFresh u op lim)
             (proj₂ (mintNode sched)) st
             (allFresh-wid (Caps.cWid c)
                (Sched.slots (proj₂ (mintNode sched))) u op lim)
             hc)
          (allWrap-valOK c op lim b hv)
          (allWrap-closOK c sl op lim b hcl)
          (≤-trans (allWrap-descW g op lim b κ id now sched st) hw)))
  where
  nid = proj₁ (mintNode sched)
  res = subscribeE g b (thru-outer op nid ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode nid (allFresh u op lim) st)

pushVals-caps-wid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  descW g (allWrap op lim b) κ id now sched st ≤ W →
  let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  in pushValsWidOK (arrCapAt j c) sl (proj₁ res)
pushVals-caps-wid {u = u} c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw =
  pushVals-wid-ems (arrCapAt j c) sl (proj₁ res)
    (burstCaps?-widen sl (proj₁ res)
       (arrCapAt-⊑ c (≤-trans (syncSizeᵉ-pos (allWrap op lim b))
                              (nestValOK?-size c (allWrap op lim b) hv)) hj)
       (subscribeE-burst-caps c sl W g b
          (thru-outer op nid ↠ κ) id now (proj₂ (mintNode sched))
          (installNode nid (allFresh u op lim) st)
          hsl
          (nestCapsOK?-setNode c nid (allFresh u op lim)
             (proj₂ (mintNode sched)) st
             (allFresh-wid (Caps.cWid c)
                (Sched.slots (proj₂ (mintNode sched))) u op lim)
             hc)
          (allWrap-valOK c op lim b hv)
          (allWrap-closOK c sl op lim b hcl)
          (≤-trans (allWrap-descW g op lim b κ id now sched st) hw)))
  where
  nid = proj₁ (mintNode sched)
  res = subscribeE g b (thru-outer op nid ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode nid (allFresh u op lim) st)



-- AND THE FILTER'S DISPATCH DOES TOO: a cut sweeps the live list and
-- drops registrations, neither of which the invariant reads, and both
-- node writes are counters it reads as true.
takeDispatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (nid : NodeId)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (mns : Maybe (NodeState Γ)) →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  let r = takeDispatch {t = t} {e = e} nid vals fin sched st mns in
  nestCapsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true
takeDispatch-caps c sl nid vals fin sched st (just (take-st k)) hsl hc
  with proj₂ (proj₂ (takeVals k vals))
... | true  = setNode-nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) nid
                (take-st zero) (EvalSt.nodes st) refl hc
... | false = setNode-nodeWidᴺ? (Caps.cWid c) (Sched.slots sched) nid
                (take-st (proj₁ (proj₂ (takeVals k vals))))
                (EvalSt.nodes st) refl hc
takeDispatch-caps c sl nid vals fin sched st nothing                    hsl hc = hc
takeDispatch-caps c sl nid vals fin sched st (just (scan-st _))         hsl hc = hc
takeDispatch-caps c sl nid vals fin sched st (just (mergeAll-st _ _ _ _)) hsl hc = hc
takeDispatch-caps c sl nid vals fin sched st (just (switch-st _ _))     hsl hc = hc
takeDispatch-caps c sl nid vals fin sched st (just (exhaust-st _ _))    hsl hc = hc




-- THE INNER SUBSCRIBE'S OWN LEG, and it is a re-entry rather than a
-- step: the wrapper mints a node id and appends an `from-inner` frame,
-- and neither write is one the invariant reads -- the id bump moves a
-- counter the width predicate never looks at, and the frame lives on
-- the path rather than in the table.  So the whole of what this owes
-- is the walk on the definition it descends into, at the arrival's
-- own descent width.

-- THE WRAP'S OWN EXIT, AND IT IS THE UNKEYED WALK ONE HOP DOWN.  This
-- descends into the merge's source under a `thru-outer` frame, with
-- the WRAP's value and closure keys as its premises -- neither of
-- which says anything about the width the source's own inners deliver.
-- So the conclusion is asked at the cap the premises were read at
-- while the descent installs nodes the face can only bound at a cap
-- that steps, which is the crossing the witness below makes at the
-- root path and this shape inherits.
--
-- AND THE PROVEN FACE IS NOT THE REPAIR, WHICH IS A FACT ABOUT THE
-- PREDICATE AND NOT ABOUT THE CAP.  The face reads the strong caps
-- boolean and this family reads the node-table conjunct alone; the
-- conversion between them runs one way, from strong to weak, and there
-- is no route back.  So a door standing here can never assemble what
-- the face asks for, however the cap is parameterised -- the walk was
-- restated at a ceiling, the application typechecked, and it was still
-- unreachable, because nothing in this cone can produce the strong
-- reading to feed it.  The entry that COULD is the thru door, which
-- holds the strong boolean and weakens it immediately; the repair is
-- to stop weakening there, not to re-cap anything here.
--
-- AND ITS DESCENT IS PROVEN ONE FACE OVER, at the stepping cap and the
-- strong reading, exactly as the inner walk's is; the wrap adds a
-- frame and a minted node and neither is a fact that face lacks.  So
-- this row is owed the same conversion, and the two travel together.
-- REFUTED: `Refuted.Subscribe-Burst-Width` kills the walk this was a
--   one-line application of, and pins the two figures it crosses --
--   an arrival cap's width against the reading of the first payload
--   the source hands back.
-- RECOVERY: git show 5899a5e restores the application and the arms
--   under it, together with the node-reading widening and its lift to
--   the table predicate, which any ceiling form needs unchanged.
postulate
  pushVals-caps-exit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (W : ℕ) (g : Gas)
    (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
    nestValOK? c (obs u) (allWrap op lim b) ≡ true →
    nestClosOK? c sl (allWrap op lim b) ≡ true →
    descW g (allWrap op lim b) κ id now sched st ≤ W →
    ⦃ _ : FaceOK c sl ⦄ →
    let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
            id now (proj₂ (mintNode sched))
            (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
    in nestCapsOK? c (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true

-- THE ROOM WALK ASSEMBLED, over the three leaves the block above
-- states apart.  The exit pair is the descent's, so the fold starts at
-- the one state the subscribe leaves and marches from there.
pushVals-caps-room : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  descW g (allWrap op lim b) κ id now sched st ≤ W →
  let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  in pushValsRoomOK (arrCapAt j c) sl W g op (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-caps-room {u = u} c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw =
  pushVals-room-join (arrCapAt j c) sl W g op (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    ⦃ faceArr c sl j faceHere ⦄
    (trans (KeepsC.slotsEq
              (subscribeE-keeps g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
                 id now (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)))
           hsl) EX
    (pushVals-caps-adm c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-caps-wid c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-caps-burstW c sl W g op lim b κ id now sched st hsl hc hv hcl hw)
    (pushVals-caps-queue c j sl W g op lim b κ id now sched st hsl hc hv hcl hw
       (pushVals-caps-wid c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw))
  where
  res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  EX = pushVals-caps-exit c sl W g op lim b κ id now sched st hsl hc hv hcl hw

-- the state half assembled: exit pair in, checked chain out
pushVals-caps-st : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  descW g (allWrap op lim b) κ id now sched st ≤ W →
  let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  in pushValsStOK (arrCapAt j c) sl g op (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-caps-st {u = u} c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw =
  pushValsSt-walk (arrCapAt j c) sl W g op (proj₁ (mintNode sched)) κ id now (proj₁ res)
    (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    ⦃ faceArr c sl j faceHere ⦄
    (trans (KeepsC.slotsEq
              (subscribeE-keeps g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
                 id now (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)))
           hsl) EX
    (pushVals-caps-adm c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-caps-room c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
  where
  res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  EX = pushVals-caps-exit c sl W g op lim b κ id now sched st hsl hc hv hcl hw

-- THE CAPS MASTER IS AN ASSEMBLY.  The walk owes three kinds of fact
-- and the leaves above state them apart; the composition into the
-- full bundle is checked here rather than asserted.
pushVals-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (W : ℕ) (g : Gas)
  (op : AllOp) (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (allWrap op lim b) ≡ true →
  nestClosOK? c sl (allWrap op lim b) ≡ true →
  descW g (allWrap op lim b) κ id now sched st ≤ W →
  let res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)
  in pushValsCapsOK (arrCapAt j c) sl W g op (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-caps {u = u} c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw =
  pushVals-caps-join (arrCapAt j c) sl W g op (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    (pushVals-caps-st c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-caps-adm c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-caps-room c j sl W g op lim b κ id now sched st hj hsl hc hv hcl hw)
  where
  res = subscribeE g b (thru-outer op (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (allFresh u op lim) st)

pushVals-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas)
  (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (mergeAllᵉ lim b) ≡ true →
  nestClosOK? c sl (mergeAllᵉ lim b) ≡ true →
  nestDᵉ (mergeAllᵉ lim b) ≤ B →
  descW g (mergeAllᵉ lim b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st)
  in pushValsOK (arrCapAt j c) sl B W (syncSizeᵉ b)
       g mergeAllᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-merge {Γ = Γ} {t = t} {e = e} {u = u} c j sl B W g lim b κ id now sched st
               hj hsl hc hv hcl hn hw hbu =
  pushVals-both (arrCapAt j c) sl B W (syncSizeᵉ b) g mergeAllᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    (pushVals-caps c j sl W g mergeAllᵒ lim b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-nest-ems (arrCapAt j c) sl B W (syncSizeᵉ b) g mergeAllᵒ
       (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
       (subst (λ z → nestDᵛˢ z ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b))
              (splitBurst-vals-A {A = Val Γ t} {B = Val Γ u} (proj₁ res)) hbu))
  where
  res = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st)

pushVals-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas)
  (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (switchAllᵉ b) ≡ true →
  nestClosOK? c sl (switchAllᵉ b) ≡ true →
  nestDᵉ (switchAllᵉ b) ≤ B →
  descW g (switchAllᵉ b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
  in pushValsOK (arrCapAt j c) sl B W (syncSizeᵉ b)
       g switchᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-switch {Γ = Γ} {t = t} {e = e} {u = u} c j sl B W g b κ id now sched st
               hj hsl hc hv hcl hn hw hbu =
  pushVals-both (arrCapAt j c) sl B W (syncSizeᵉ b) g switchᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    (pushVals-caps c j sl W g switchᵒ nothing b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-nest-ems (arrCapAt j c) sl B W (syncSizeᵉ b) g switchᵒ
       (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
       (subst (λ z → nestDᵛˢ z ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b))
              (splitBurst-vals-A {A = Val Γ t} {B = Val Γ u} (proj₁ res)) hbu))
  where
  res = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)

pushVals-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas)
  (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (exhaustAllᵉ b) ≡ true →
  nestClosOK? c sl (exhaustAllᵉ b) ≡ true →
  nestDᵉ (exhaustAllᵉ b) ≤ B →
  descW g (exhaustAllᵉ b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
  in pushValsOK (arrCapAt j c) sl B W (syncSizeᵉ b)
       g exhaustᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
pushVals-exhaust {Γ = Γ} {t = t} {e = e} {u = u} c j sl B W g b κ id now sched st
               hj hsl hc hv hcl hn hw hbu =
  pushVals-both (arrCapAt j c) sl B W (syncSizeᵉ b) g exhaustᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
    (pushVals-caps c j sl W g exhaustᵒ nothing b κ id now sched st hj hsl hc hv hcl hw)
    (pushVals-nest-ems (arrCapAt j c) sl B W (syncSizeᵉ b) g exhaustᵒ
       (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
       (subst (λ z → nestDᵛˢ z ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b))
              (splitBurst-vals-A {A = Val Γ t} {B = Val Γ u} (proj₁ res)) hbu))
  where
  res = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)


-- THE THREE FITS, now READ OFF the burst statement rather than
-- asserted beside it: `pushFit-ems` turns the emit-by-emit value
-- record into the emit-by-emit fit, and each head supplies that record
-- for its own initial state.
thruFit-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas)
  (lim : Maybe ℕ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (mergeAllᵉ lim b) ≡ true →
  nestClosOK? c sl (mergeAllᵉ lim b) ≡ true →
  nestDᵉ (mergeAllᵉ lim b) ≤ B →
  descW g (mergeAllᵉ lim b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched))
                           (mergeAll-st {t = u} lim 0 [] false) st)
  in pushFitOK (nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B
                  (syncSizeᵉ (mergeAllᵉ lim b)))
       g mergeAllᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
thruFit-merge {e = e} {u = u} c j sl B W g lim b κ id now sched st hj hsl hc hv hcl hn hw hbu =
  pushFit-ems (arrCapAt j c) sl B W (syncSizeᵉ b) (syncSizeᵉ (mergeAllᵉ lim b))
    g mergeAllᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≤-refl
    (pushVals-merge c j sl B W g lim b κ id now sched st hj hsl hc hv hcl hn hw hbu)
    ⦃ faceArr c sl j faceHere ⦄
  where
  res = subscribeE g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched))
                       (mergeAll-st {t = u} lim 0 [] false) st)

thruFit-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (switchAllᵉ b) ≡ true →
  nestClosOK? c sl (switchAllᵉ b) ≡ true →
  nestDᵉ (switchAllᵉ b) ≤ B →
  descW g (switchAllᵉ b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
  in pushFitOK (nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B
                  (syncSizeᵉ (switchAllᵉ b)))
       g switchᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
thruFit-switch {e = e} c j sl B W g b κ id now sched st hj hsl hc hv hcl hn hw hbu =
  pushFit-ems (arrCapAt j c) sl B W (syncSizeᵉ b) (syncSizeᵉ (switchAllᵉ b))
    g switchᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≤-refl
    (pushVals-switch c j sl B W g b κ id now sched st hj hsl hc hv hcl hn hw hbu)
    ⦃ faceArr c sl j faceHere ⦄
  where
  res = subscribeE g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)

thruFit-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Caps.cSize c ≤ j →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs u) (exhaustAllᵉ b) ≡ true →
  nestClosOK? c sl (exhaustAllᵉ b) ≡ true →
  nestDᵉ (exhaustAllᵉ b) ≤ B →
  descW g (exhaustAllᵉ b) κ id now sched st ≤ W →
  (let r₀ = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
   in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r₀)))
        ≤ nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B (syncSizeᵉ b)) →
  let res = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
              id now (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
  in pushFitOK (nestB (Caps.cSize (arrCapAt j c)) W (nestUnit e sl) B
                  (syncSizeᵉ (exhaustAllᵉ b)))
       g exhaustᵒ (proj₁ (mintNode sched)) κ id now
       (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
thruFit-exhaust {e = e} c j sl B W g b κ id now sched st hj hsl hc hv hcl hn hw hbu =
  pushFit-ems (arrCapAt j c) sl B W (syncSizeᵉ b) (syncSizeᵉ (exhaustAllᵉ b))
    g exhaustᵒ (proj₁ (mintNode sched)) κ id now
    (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≤-refl
    (pushVals-exhaust c j sl B W g b κ id now sched st hj hsl hc hv hcl hn hw hbu)
    ⦃ faceArr c sl j faceHere ⦄
  where
  res = subscribeE g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
          id now (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)


-- THE GRANT ONLY EVER GROWS, so a clause proving the shared statement
-- against one bound proves it against any larger one.  The three
-- conjuncts widen together because they are one tuple.
nestTriple-widen : ∀ {D N n0 G G′ : ℕ} {A Bf : NodeId → ℕ} → G ≤ G′ →
  (D ≤ G) × (N ≤ n0 ⊔ G) × (∀ (j : NodeId) → A j ≤ Bf j ⊔ G) →
  (D ≤ G′) × (N ≤ n0 ⊔ G′) × (∀ (j : NodeId) → A j ≤ Bf j ⊔ G′)
nestTriple-widen hG (p , q , r) =
  ≤-trans p hG
  , ≤-trans q (⊔-mono-≤ ≤-refl hG)
  , (λ j → ≤-trans (r j) (⊔-mono-≤ ≤-refl hG))

-- AND TWO LEGS OF ONE WALK JOIN AT THE LARGER LEVEL, which is what a
-- drain over a QUEUE needs: each element reports the level it wanted
-- and the max answers for both.  The flattened grant reads the stepped
-- cap in TWO places -- as the base and as the descent -- so the join
-- spends one monotonicity in each.
nestFlat-level : ∀ (c : Caps) {j j′ : ℕ} → j ≤ j′ → ∀ (W U B : ℕ) → 1 ≤ Caps.cSize c →
  nestB (Caps.cSize (frameStep j c)) W U B (Caps.cSize (frameStep j c))
    ≤ nestB (Caps.cSize (frameStep j′ c)) W U B (Caps.cSize (frameStep j′ c))
nestFlat-level c {j} {j′} le W U B hS =
  ≤-trans (nestB-mono (Caps.cSize (frameStep j c)) W U B step)
          (nestB-monoS step W U B (Caps.cSize (frameStep j′ c)))
  where
  step : Caps.cSize (frameStep j c) ≤ Caps.cSize (frameStep j′ c)
  step = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) hS le

-- THE SLOT HEADS, where a subscription reads the telescope rather
-- than descending.  A hot slot emits bookkeeping and no values; a cold
-- one emits its script, which is charged to the unit and not to the
-- expression; a shared one connects and re-enters the walk.
--
-- AND THE PREMISE THAT LOOKS ABSENT HERE IS ONLY THE WRITTEN ONE.  A
-- slot reference is replaced by its definition, so what gets subscribed
-- is the head's syntax with the payload IN it, and the value premise is
-- keyed on the written size, which at `input i` is one.  The closure
-- premise beside it reads the size with the telescope SUBSTITUTED IN,
-- which is what it was put there for -- so the arr-keyed face, whose
-- whole grant is read on that key, already proves this head, and what
-- is left is arithmetic: the arr grant doubles once per unit of the
-- key and a layer of the cap-keyed grant doubles the cap that many
-- times, so a key the cap dominates is dominated exponent and all.
--
-- REFUTED: `Refuted.Inner-Drain-Share-Nest` kills the caps-scaled
--   form, forty delivered against a charge of ZERO, at a queue holding
--   nothing but a reference to an observable-typed share.
--   `nestDᵉ (input i)` is zero and rightly so -- the syntax of a slot
--   reference says nothing about the slot -- and the node table does
--   not read the slots either, so the charged side is empty and every
--   factor is a multiple of nothing.  What that pins is the shape: the
--   factor AND a slots summand, each of which is dead on its own.
-- DEAD ROUTE: a ceiling of the walk's own -- keyed on the hop budget,
--   stepping by the caps face's `iterSize`, with every arrival read at
--   it -- is STRUCTURALLY DEAD at the face it hands its grant to.
--   Threading it is mechanical and goes green right up to the
--   flattening site, where the grant meets the delivery currency.  That
--   currency is a SQUARE of the cap per level, closed under the fan
--   recurrence and nothing wider, while one `iterSize` step iterates a
--   multiply once per unit of cap; no arithmetic reconciles them.
--   Minting a second currency here is the part that is dead, and it
--   stays dead however the step is priced.
-- RECOVERY: git show 09d8bf7 restores that ceiling's algebra -- the
--   gas-keyed tower, its two monotonicities, the drop a non-
--   substituting re-entry needs, and `subCaps`, which is the piece
--   worth having back if an arrival-side cap is ever wanted: it moves
--   the size field alone, since widening the width would weaken the
--   room record's queue conjunct.
subscribeE-nest-slot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas) (i : Fin n)
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  NestAt c d sl B W g (input i) κ id now sched st
subscribeE-nest-slot {e = e} c d sl B W g i κ id now sched st hsl hc hv hcl hn hw hd =
  0 , z≤n , nestTriple-widen
        (arrD≤nestB (Caps.cSize c) W (nestUnit e sl) B
           (slotClos sl i)
           (nestClosOK?-size c sl (input i) hcl))
        (subscribeE-nest-arr c sl B W g (input i) κ id now sched st
           hsl hc hv hcl hn hw)

subscribeE-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  NestAt c d sl B W g o κ id now sched st
subscribeE-nest c d sl B W g (input i) κ id now sched st =
  subscribeE-nest-slot c d sl B W g i κ id now sched st
subscribeE-nest {Γ = Γ} {t = t} {e = e} {u = u} c d sl B W g (ofᵉ ts) κ id now sched st
  hsl hc hv hcl hn hw hd =
  0 , z≤n ,
  ≤-trans (≤-reflexive (cong (nestDᵛˢ {u = u})
             (oneShot-vals {A = Val Γ t} (map (λ tm → evalTm tm) ts) id sched)))
    (≤-trans (≤-trans (ofVals-nest-sync ts) (*-monoʳ-≤ (2 ^ syncSizeᵗˢ ts) hn))
      (≤-trans (*-monoʳ-≤ (2 ^ syncSizeᵗˢ ts)
                  (m≤m+n B (nestB (Caps.cSize c) W (nestUnit e sl) B 0)))
               (nestB-frame (Caps.cSize c) W (nestUnit e sl) B
                  0 (syncSizeᵗˢ ts) (syncSizeᵉ (ofᵉ ts))
                  (nestValOK?-size c (ofᵉ ts) hv) (s≤s z≤n))))
  , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest c d sl B W g emptyᵉ κ id now sched st hsl hc hv hcl hn hw hd =
  0 , z≤n , z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest {e = e} c d sl B W g (mapᵉ f b) κ id now sched st hsl hc hv hcl hn hw hd =
  jIH
  , jB
  , ≤-trans (proj₁ push)
      (≤-trans (*-monoʳ-≤ (2 ^ syncSizeᵗ f) (+-mono-≤ hfB (proj₁ IH)))
               (nestB-frame S′ W (nestUnit e sl) B
                  (syncSizeᵉ b) (syncSizeᵗ f) (syncSizeᵉ (mapᵉ f b)) hk hm))
  , ≤-trans (proj₁ (proj₂ push))
      (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow))
  , (λ j → ≤-trans (proj₂ (proj₂ push) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow)))
  where
  res = subscribeE g b (map-f f ↠ κ) id now sched st

  push = pushBurst-nest-map g id now f κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH₀ = subscribeE-nest c d sl B W g b (map-f f ↠ κ) id now sched st
         hsl hc (nestValOK?-map c f b hv)
         (nestClosOK?-mono c sl b (mapᵉ f b)
            (≤-trans (m≤n+m _ _) (n≤1+n _)) hcl)
         (≤-trans (m≤n+m (nestDᵉ b) (nestDᵗ f)) hn)
         (≤-trans (descW-map g f b κ id now sched st) hw)
         (≤-trans (m≤m⊔n _ _) hd)

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)
  IH  = proj₂ (proj₂ IH₀)
  S′  = Caps.cSize (frameStep jIH c)

  cap≤ : Caps.cSize c ≤ S′
  cap≤ = iterSize-infl (Caps.cSize c)
           (≤-trans (syncSizeᵉ-pos (mapᵉ f b)) (nestValOK?-size c (mapᵉ f b) hv))
           jIH (Caps.cSize c)

  -- the function's own nesting is one summand of the head's, so the
  -- base the frame lemma adds is already paid for by the depth premise
  hfB : nestDᵗ f ≤ B
  hfB = ≤-trans (m≤m+n (nestDᵗ f) (nestDᵉ b)) hn

  -- and the frame is a strict subterm of the head, which is the level
  -- of the key this substitution spends
  hk : suc (syncSizeᵗ f) ≤ S′
  hk = ≤-trans (≤-trans (s≤s (m≤m+n (syncSizeᵗ f) (syncSizeᵉ b)))
                        (nestValOK?-size c (mapᵉ f b) hv))
               cap≤

  hm : suc (syncSizeᵉ b) ≤ syncSizeᵉ (mapᵉ f b)
  hm = s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f))

  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (mapᵉ f b))
  grow = nestB-mono S′ W (nestUnit e sl) B
           (≤-trans (n≤1+n (syncSizeᵉ b)) hm)
subscribeE-nest {e = e} c d sl B W g (takeᵉ cnt b) κ id now sched st hsl hc hv hcl hn hw hd
  with evalTm cnt in eqc
... | zero  = 0 , z≤n , z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
... | suc k =
  jIH
  , jB
  , ≤-trans (proj₁ push) (≤-trans (proj₁ IH) grow)
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
  inv₀ = nestCapsOK?-setNode c nid (take-st (suc k)) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  push = pushBurst-nest-take g id now nid κ
           (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

  IH₀ = subscribeE-nest c d sl B W g b (take-f nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-take c cnt b hv)
         (nestClosOK?-mono c sl b (takeᵉ cnt b)
            (≤-trans (m≤n+m _ _) (n≤1+n _)) hcl) hn
         (≤-trans (descW-take g cnt b κ id now sched st k eqc) hw)
         (≤-trans (m≤m⊔n _ _) hd)

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)
  IH  = proj₂ (proj₂ IH₀)
  S′  = Caps.cSize (frameStep jIH c)

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
  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (takeᵉ cnt b))
  grow = nestB-mono S′ W (nestUnit e sl) B
           (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ cnt)) (n≤1+n _))
subscribeE-nest c d sl B W g (scanᵉ f z b) κ id now sched st =
  subscribeE-nest-scan c d sl B W g f z b κ id now sched st
subscribeE-nest {e = e} {u = u} c d sl B W g (mergeAllᵉ lim b) κ id now sched st
  hsl hc hv hcl hn hw hd =
  J
  , Jb
  , proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (mergeAll-st {t = u} lim 0 [] false) st
  res    = subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (mergeAll-st {t = u} lim 0 [] false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH₀ = subscribeE-nest c d sl B W g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-merge c lim b hv)
         (nestClosOK?-mono c sl b (mergeAllᵉ lim b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-merge g lim b κ id now sched st) hw)
         (≤-trans (m≤m⊔n _ _) hd)

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)

  -- the level this arm reports -- the child's joined with the head's
  -- own written size, which is the level the FIT's arrivals cross by;
  -- `NestAt` carries why the join is the shape of the bound
  J   = jIH ⊔ Caps.cSize c
  S′  = Caps.cSize (frameStep J c)

  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (syncSizeᵉ-pos (mergeAllᵉ lim b)) (nestValOK?-size c (mergeAllᵉ lim b) hv)

  Jb : J ≤ sizeCount c d ⊔ Caps.cSize c
  Jb = ⊔-lub jB (m≤n⊔m (sizeCount c d) (Caps.cSize c))

  IH  = nestTriple-widen
          (nestB-monoS
             (iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
                (m≤m⊔n jIH (Caps.cSize c)))
             W (nestUnit e sl) B (syncSizeᵉ b))
          (proj₂ (proj₂ IH₀))

  -- the wall crosses here, and it is the ONE assertion of the clause
  FIT = thruFit-merge c J sl B W g lim b κ id now sched st (m≤n⊔m jIH (Caps.cSize c)) hsl hc hv hcl hn hw (proj₁ IH)

  PUSH = pushBurst-nest-thru
           (nestB S′ W (nestUnit e sl) B (syncSizeᵉ (mergeAllᵉ lim b)))
           g mergeAllᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT


  -- the queue this head installs is empty, so the table the child
  -- descends from is the table this head was handed
  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (mergeAll-st {t = u} lim 0 [] false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (mergeAll-st {t = u} lim 0 [] false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (mergeAllᵉ lim b))
  grow = nestB-mono S′ W (nestUnit e sl) B (n≤1+n (syncSizeᵉ b))
subscribeE-nest {e = e} {u = u} c d sl B W g (switchAllᵉ b) κ id now sched st
  hsl hc hv hcl hn hw hd =
  J
  , Jb
  , proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (switch-st nothing false) st
  res    = subscribeE g b (thru-outer switchᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (switch-st nothing false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH₀ = subscribeE-nest c d sl B W g b (thru-outer switchᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-switch c b hv)
         (nestClosOK?-mono c sl b (switchAllᵉ b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-switch g b κ id now sched st) hw)
         (≤-trans (m≤m⊔n _ _) hd)

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)

  -- the level this arm reports -- the child's joined with the head's
  -- own written size, which is the level the FIT's arrivals cross by;
  -- `NestAt` carries why the join is the shape of the bound
  J   = jIH ⊔ Caps.cSize c
  S′  = Caps.cSize (frameStep J c)

  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (syncSizeᵉ-pos (switchAllᵉ b)) (nestValOK?-size c (switchAllᵉ b) hv)

  Jb : J ≤ sizeCount c d ⊔ Caps.cSize c
  Jb = ⊔-lub jB (m≤n⊔m (sizeCount c d) (Caps.cSize c))

  IH  = nestTriple-widen
          (nestB-monoS
             (iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
                (m≤m⊔n jIH (Caps.cSize c)))
             W (nestUnit e sl) B (syncSizeᵉ b))
          (proj₂ (proj₂ IH₀))

  FIT = thruFit-switch c J sl B W g b κ id now sched st (m≤n⊔m jIH (Caps.cSize c)) hsl hc hv hcl hn hw (proj₁ IH)

  PUSH = pushBurst-nest-thru
           (nestB S′ W (nestUnit e sl) B (syncSizeᵉ (switchAllᵉ b)))
           g switchᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT


  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (switch-st nothing false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (switch-st nothing false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (switchAllᵉ b))
  grow = nestB-mono S′ W (nestUnit e sl) B (n≤1+n (syncSizeᵉ b))
subscribeE-nest {e = e} {u = u} c d sl B W g (exhaustAllᵉ b) κ id now sched st
  hsl hc hv hcl hn hw hd =
  J
  , Jb
  , proj₁ PUSH
  , ⊔-chain (proj₁ (proj₂ PUSH)) (≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ st₀≤ grow))
  , (λ j → ⊔-chain (proj₂ (proj₂ PUSH) j)
             (≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ (st₀at j) grow)))
  where
  nid    = proj₁ (mintNode sched)
  sched₀ = proj₂ (mintNode sched)
  st₀    = installNode nid (exhaust-st false false) st
  res    = subscribeE g b (thru-outer exhaustᵒ nid ↠ κ) id now sched₀ st₀

  inv₀ : nestCapsOK? c sched₀ st₀ ≡ true
  inv₀ = nestCapsOK?-setNode c nid (exhaust-st false false) sched₀ st refl
           (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc)

  IH₀ = subscribeE-nest c d sl B W g b (thru-outer exhaustᵒ nid ↠ κ) id now sched₀ st₀
         hsl inv₀ (nestValOK?-exhaust c b hv)
         (nestClosOK?-mono c sl b (exhaustAllᵉ b) (n≤1+n _) hcl)
         (≤-trans (n≤1+n (nestDᵉ b)) hn)
         (≤-trans (descW-exhaust g b κ id now sched st) hw)
         (≤-trans (m≤m⊔n _ _) hd)

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)

  -- the level this arm reports -- the child's joined with the head's
  -- own written size, which is the level the FIT's arrivals cross by;
  -- `NestAt` carries why the join is the shape of the bound
  J   = jIH ⊔ Caps.cSize c
  S′  = Caps.cSize (frameStep J c)

  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (syncSizeᵉ-pos (exhaustAllᵉ b)) (nestValOK?-size c (exhaustAllᵉ b) hv)

  Jb : J ≤ sizeCount c d ⊔ Caps.cSize c
  Jb = ⊔-lub jB (m≤n⊔m (sizeCount c d) (Caps.cSize c))

  IH  = nestTriple-widen
          (nestB-monoS
             (iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
                (m≤m⊔n jIH (Caps.cSize c)))
             W (nestUnit e sl) B (syncSizeᵉ b))
          (proj₂ (proj₂ IH₀))

  FIT = thruFit-exhaust c J sl B W g b κ id now sched st (m≤n⊔m jIH (Caps.cSize c)) hsl hc hv hcl hn hw (proj₁ IH)

  PUSH = pushBurst-nest-thru
           (nestB S′ W (nestUnit e sl) B (syncSizeᵉ (exhaustAllᵉ b)))
           g exhaustᵒ nid κ id now (proj₁ res)
           (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) FIT


  st₀≤ : nodesMax st₀ ≤ nodesMax st
  st₀≤ = ≤-trans (setNode-nodes nid (exhaust-st false false) (EvalSt.nodes st))
                 (⊔-lub z≤n ≤-refl)

  st₀at : ∀ (j : NodeId) → nodeNestAt j st₀ ≤ nodeNestAt j st
  st₀at j = ≤-trans (nodeNestAt-set j nid (exhaust-st false false) st)
                    (⊔-lub z≤n ≤-refl)

  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ b)
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (exhaustAllᵉ b))
  grow = nestB-mono S′ W (nestUnit e sl) B (n≤1+n (syncSizeᵉ b))
subscribeE-nest c d sl B W g0 (μᵉ body) κ id now sched st hsl hc hv hcl hn hw hd =
  0 , z≤n , z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeE-nest {e = e} c d sl B W (gs fuel) (μᵉ body) κ id now sched st hsl hc hv hcl hn hw hd =
  jIH
  , jB
  , ≤-trans (proj₁ IH) grow
  , ≤-trans (proj₁ (proj₂ IH)) (⊔-mono-≤ ≤-refl grow)
  , (λ j → ≤-trans (proj₂ (proj₂ IH) j) (⊔-mono-≤ ≤-refl grow))
  where
  -- the evaluator spends one gas AT the μ and subscribes the unfolding,
  -- so the recursive call is the same subscription and the whole clause
  -- is the three premises re-established across the substitution
  IH₀ = subscribeE-nest c d sl B W fuel (unfoldμ body) κ id now sched st hsl hc
         (≤ᵇ-true (syncSizeᵉ (unfoldμ body)) (Caps.cSize c)
           (≤-trans (≤-reflexive (syncSize-unfoldμ body))
             (≤-trans (n≤1+n (syncSizeᵉ body))
                      (nestValOK?-size c (μᵉ body) hv))))
         (nestClosOK?-mono c sl (unfoldμ body) (μᵉ body)
            (≤-trans (≤-reflexive (closSize-unfoldμ (slotClos sl) body))
                     (n≤1+n _))
            hcl)
         (≤-trans (≤-reflexive (nestD-unfoldμ body)) hn)
         (≤-trans (descW-mu fuel body κ id now sched st) hw) hd

  jIH = proj₁ IH₀
  jB  = proj₁ (proj₂ IH₀)
  IH  = proj₂ (proj₂ IH₀)
  S′  = Caps.cSize (frameStep jIH c)

  -- and the grant widens by the μ node the unfolding drops, which is
  -- the ONE thing this head spends: the sync spine is what the key is
  -- read on, and the unfolding leaves it exactly where it was
  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ (unfoldμ body))
           ≤ nestB S′ W (nestUnit e sl) B (syncSizeᵉ (μᵉ body))
  grow = nestB-mono S′ W (nestUnit e sl) B
           (≤-trans (≤-reflexive (syncSize-unfoldμ body)) (n≤1+n _))
subscribeE-nest c d sl B W g (varᵉ ()) κ id now sched st
subscribeE-nest c d sl B W g (deferᵉ body) κ id now sched st hsl hc hv hcl hn hw hd =
  0 , z≤n , z≤n
  , ≤-trans (setNode-nodes _ _ (EvalSt.nodes st)) (⊔-lub z≤n (m≤m⊔n _ _))
  , (λ j → ≤-trans (nodeNestAt-set j _ _ st) (⊔-lub z≤n (m≤m⊔n _ _)))

-- ONE SUBSCRIPTION, AT THE ARRIVAL'S OWN KEY.  A subscribe IS the
-- recursive descent under a `from-inner` frame, so the bound the
-- descent already proves transfers verbatim -- keyed on the arrival's
-- sync size, which is what a caller wanting to spend ONE level of key
-- needs and what flattening at the cap throws away.
subscribeInner-nest-tight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs s) o ≡ true →
  nestClosOK? c sl o ≡ true →
  nestDᵉ o ≤ B →
  innerW sf op allNid κ id now o sched st ≤ W →
  depthInner sf op allNid κ id now o sched st ≤ d →
  let r = subscribeInner sf op allNid κ id now o sched st in
  Σ ℕ λ j →
  let G = nestB (Caps.cSize (frameStep j c)) W (nestUnit e sl) B (syncSizeᵉ o) in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nestDᵛˢ (proj₁ (proj₂ r)) ≤ G)
  × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ G)
  × (∀ (k : NodeId) →
       nodeNestAt k (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodeNestAt k st ⊔ G)
subscribeInner-nest-tight c d sl B W g0 op allNid κ id now o sched st hsl hc hv hcl hn hw hd =
  0 , z≤n , z≤n , m≤m⊔n _ _ , (λ j → m≤m⊔n _ _)
subscribeInner-nest-tight {e = e} c d sl B W (gs fuel) op allNid κ id now o sched st
                          hsl hc hv hcl hn hw hd =
  subscribeE-nest c d sl B W fuel o
    (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st hsl
    (nestCapsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc) hv hcl hn
    (≤-trans (innerW-gs fuel op allNid κ id now o sched st) hw) hd

-- AND FLATTENED AT THE CAP, which is what the DRAIN wants and only the
-- drain: an inner the caps premise admits is no larger than the cap, so
-- a queue can be walked at ONE exponent instead of one per element.  The
-- bound is then ABSOLUTE -- re-established rather than read relative to
-- the store handed in, which is exactly what stops the factor
-- compounding once per queued inner.  A relative form would read
-- `2 ^ cSize` times the PREVIOUS store and raise the drain's cost to a
-- tower in the queue's length, which is not what a queue of independent
-- inners costs.
subscribeInner-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl → nestCapsOK? c sched st ≡ true →
  nestValOK? c (obs s) o ≡ true →
  nestClosOK? c sl o ≡ true →
  nestDᵉ o ≤ B →
  innerW sf op allNid κ id now o sched st ≤ W →
  depthInner sf op allNid κ id now o sched st ≤ d →
  let r = subscribeInner sf op allNid κ id now o sched st in
  Σ ℕ λ j →
  let S′ = Caps.cSize (frameStep j c)
      G = nestB S′ W (nestUnit e sl) B S′ in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nestDᵛˢ (proj₁ (proj₂ r)) ≤ G)
  × (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ G)
  × (∀ (k : NodeId) →
       nodeNestAt k (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≤ nodeNestAt k st ⊔ G)
subscribeInner-nest {e = e} c d sl B W sf op allNid κ id now o sched st hsl hc hv hcl hn hw hd =
  jT
  , proj₁ (proj₂ tight₀)
  , ≤-trans (proj₁ tight) grow
  , ≤-trans (proj₁ (proj₂ tight)) (⊔-mono-≤ ≤-refl grow)
  , (λ j → ≤-trans (proj₂ (proj₂ tight) j) (⊔-mono-≤ ≤-refl grow))
  where
  tight₀ = subscribeInner-nest-tight c d sl B W sf op allNid κ id now o sched st
             hsl hc hv hcl hn hw hd

  jT    = proj₁ tight₀
  tight = proj₂ (proj₂ tight₀)
  S′    = Caps.cSize (frameStep jT c)

  grow : nestB S′ W (nestUnit e sl) B (syncSizeᵉ o)
           ≤ nestB S′ W (nestUnit e sl) B S′
  grow = nestB-mono S′ W (nestUnit e sl) B
           (≤-trans (nestValOK?-size c o hv)
             (iterSize-infl (Caps.cSize c)
               (≤-trans (syncSizeᵉ-pos o) (nestValOK?-size c o hv))
               jT (Caps.cSize c)))

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
  (c : Caps) (d : ℕ) (sl : Slots Γ) (B W : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  capsDrainOK c sl sf allNid κ id now lim act q sched st →
  queueNest q ≤ B →
  drainW sf allNid κ id now q sched st ≤ W →
  depthDrain sf allNid κ id now q sched st ≤ d →
  let r = mergeAllDrain sf allNid κ id now lim act q sched st in
  Σ ℕ λ j →
  let S′ = Caps.cSize (frameStep j c)
      G = nestB S′ W (nestUnit e sl) B S′ in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nestDᵛˢ (proj₁ r) ≤ G)
  × ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
        ⊔ queueNest (proj₁ (proj₂ (proj₂ (proj₂ r))))) ≤ nodesMax st ⊔ G)
mergeAllDrain-nest {e = e} c d sl B W sf allNid κ id now lim act [] sched st hcd hq hw hd =
  0 , z≤n , z≤n , ⊔-lub (m≤m⊔n _ _) z≤n
mergeAllDrain-nest {e = e} c d sl B W sf allNid κ id now lim act (o ∷ q) sched st hcd hq hw hd
  with hasRoom lim act
... | false =
  0
  , z≤n
  , z≤n
  , ⊔-mono-≤ (≤-refl {nodesMax st})
             (≤-trans hq (nestB-base (Caps.cSize c) W (nestUnit e sl) B (Caps.cSize c)))
... | true  =
  jS ⊔ jI
  , ⊔-lub (proj₁ (proj₂ SUB₀)) (proj₁ (proj₂ IH₀))
  , ≤-trans (nestDᵛˢ-++ vs vs′) (⊔-lub SUBd IHd)
  , ≤-trans IHn (⊔-lub SUBn (m≤n⊔m (nodesMax st) _))
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
  splitW : innerW sf mergeAllᵒ allNid κ id now o sched st ≤ W
  splitW = ≤-trans (drainW-here sf allNid κ id now o q sched st) hw

  splitW′ : drainW sf allNid κ id now q sched₁ st₁ ≤ W
  splitW′ = ≤-trans (drainW-tail sf allNid κ id now o q sched st) hw

  SUB₀ = subscribeInner-nest c d sl B W sf mergeAllᵒ allNid κ id now o sched st
          (proj₁ hcd) (proj₁ (proj₂ hcd)) (proj₁ (proj₂ (proj₂ hcd)))
          (proj₁ (proj₂ (proj₂ (proj₂ hcd))))
          (≤-trans (m≤m⊔n (nestDᵉ o) (queueNest q)) hq) splitW
          (≤-trans (m≤m⊔n _ _) hd)

  IH₀ = mergeAllDrain-nest c d sl B W sf allNid κ id now lim
         (if done then act else suc act) q sched₁ st₁
         (proj₂ (proj₂ (proj₂ (proj₂ hcd))))
         (≤-trans (m≤n⊔m (nestDᵉ o) (queueNest q)) hq)
         splitW′
         (≤-trans (m≤n⊔m _ _) hd)

  jS = proj₁ SUB₀
  jI = proj₁ IH₀

  1≤S : 1 ≤ Caps.cSize c
  1≤S = ≤-trans (syncSizeᵉ-pos o)
                (nestValOK?-size c o (proj₁ (proj₂ (proj₂ hcd))))

  upS = nestFlat-level c (m≤m⊔n jS jI) W (nestUnit e sl) B 1≤S
  upI = nestFlat-level c (m≤n⊔m jS jI) W (nestUnit e sl) B 1≤S

  SUBd = ≤-trans (proj₁ (proj₂ (proj₂ SUB₀))) upS
  SUBn = ≤-trans (proj₁ (proj₂ (proj₂ (proj₂ SUB₀)))) (⊔-mono-≤ (≤-refl {nodesMax st}) upS)
  IHd  = ≤-trans (proj₁ (proj₂ (proj₂ IH₀))) upI
  IHn  = ≤-trans (proj₂ (proj₂ (proj₂ IH₀))) (⊔-mono-≤ (≤-refl {nodesMax st₁}) upI)

-- THE FINISH DISPATCH, AND ALL OF IT IS CHECKED.  `innerReact` reaches
-- here along exactly one route -- a `fin` whose inner is not held open
-- by a live registration -- so the frame's whole charge is this
-- statement's; and of the finish's own arms, every one but the
-- `mergeAllᵒ` drain either hands its inputs straight back or writes a
-- node whose `nodeNest` is zero, so the drain is the sole leaf and the
-- rest reduces.
innerFinish-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (W : ℕ) (sf : Gas) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (id : Id) (now : Tick)
  (vals : List (Val Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     drainW sf allNid p id now q sched st ≤ W) →
  depthFin sf op allNid inst p id now vals sched st
    (lookupNode allNid (EvalSt.nodes st)) ≤ d →
  let r = innerFinish sf op allNid inst p id now vals sched st
            (lookupNode allNid (EvalSt.nodes st)) in
  Σ ℕ λ j →
  let S′ = Caps.cSize (frameStep j c) in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
       ≤ nestFac S′ W * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU S′ (nestUnit e sl)))

innerFinish-nest {e = e} c d sl W sf switchᵒ allNid inst p id now vals sched st hsl hdr hw hdp
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)           = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)           = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st _ _ _ _) = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ _)      = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st nothing _) = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st (just c₀) od) with c₀ ≡ᵇ inst
...   | false = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
...   | true  =
  0 , z≤n ,
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (switch-st nothing od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl)))

innerFinish-nest {e = e} c d sl W sf exhaustᵒ allNid inst p id now vals sched st hsl hdr hw hdp
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)           = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)           = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st _ _ _ _) = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st _ _)       = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ od)     =
  0 , z≤n ,
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (exhaust-st false od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl)))

innerFinish-nest {e = e} {s = s} c d sl W sf mergeAllᵒ allNid inst p id now vals sched st hsl hdr hw hdp
  with lookupNode allNid (EvalSt.nodes st) in eq
... | nothing                = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (scan-st _)       = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (take-st _)       = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (switch-st _ _)   = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (exhaust-st _ _)  = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
...   | yes refl =
  proj₁ DR ,
  proj₁ (proj₂ DR) ,
  ⊔-lub (≤-trans (setNode-nodes allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′))
                 (≤-trans (⊔-lub (m≤n⊔m (nodesMax st′) (queueNest q′))
                                 (m≤m⊔n (nodesMax st′) (queueNest q′)))
                          drain≤))
        (≤-trans (nestDᵛˢ-++ vals vs)
                 (⊔-lub vals≤ (≤-trans (proj₁ (proj₂ (proj₂ DR))) G≤)))
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

  DR = mergeAllDrain-nest c d sl (nodesMax st) W sf allNid p id now lim (pred act) q sched st
         (hdr lim act q od refl) qbnd dw
         (≤-trans (n≤1+n _) hdp)

  S′ = Caps.cSize (frameStep (proj₁ DR) c)

  base : (nodesMax st ⊔ nestDᵛˢ vals)
           ≤ nestFac S′ W
               * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU S′ (nestUnit e sl))
  base = raiseN S′ W (nodesMax st ⊔ nestDᵛˢ vals)
                (nestU S′ (nestUnit e sl))

  vals≤ = ≤-trans (m≤n⊔m (nodesMax st) (nestDᵛˢ vals)) base

  -- the drain hands up its grant at the SIZE cap, which is exactly
  -- where the flattened factor is definitionally what this face spends
  G≤ : nestB S′ W (nestUnit e sl) (nodesMax st) S′
         ≤ nestFac S′ W
             * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU S′ (nestUnit e sl))
  G≤ = ≤-trans (nestB-at S′ W (nestUnit e sl) (nodesMax st))
               (*-monoʳ-≤ (nestFac S′ W)
                  (+-monoˡ-≤ (nestU S′ (nestUnit e sl))
                             (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))))

  drain≤ = ≤-trans (proj₂ (proj₂ (proj₂ DR)))
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
  (c : Caps) (d : ℕ) (sl : Slots Γ) (W : ℕ) (sf : Gas) (id : Id) (now : Tick) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     drainW sf allNid p id now q sched st ≤ W) →
  depthReact sf op allNid inst p id now vals sched st fin ≤ d →
  let r = stepFrame sf id now (from-inner op allNid inst) p vals fin sched st in
  Σ ℕ λ j →
  let S′ = Caps.cSize (frameStep j c) in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
       ≤ nestFac S′ W * ((nodesMax st ⊔ nestDᵛˢ vals) + nestU S′ (nestUnit e sl)))
stepFrame-nodes-inner {e = e} c d sl W sf id now op allNid inst p vals false sched st hsl hdr hw hdp =
  0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
stepFrame-nodes-inner {e = e} c d sl W sf id now op allNid inst p vals true sched st hsl hdr hw hdp
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = 0 , z≤n , raiseN (Caps.cSize c) W (nodesMax st ⊔ nestDᵛˢ vals) (nestU (Caps.cSize c) (nestUnit e sl))
... | false = innerFinish-nest c d sl W sf op allNid inst p id now vals sched st hsl hdr hw hdp

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
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) → Set
frameDrainOK c sl sf id now (map-f _)    p vals sched st = ⊤
frameDrainOK c sl sf id now (scan-f _ _) p vals sched st = ⊤
frameDrainOK c sl sf id now (take-f _)   p vals sched st = ⊤
frameDrainOK c sl sf id now (thru-outer op nid) p vals sched st =
  thruRoomQOK c sf op nid p id now vals sched st
frameDrainOK {Γ = Γ} {u = u} c sl sf id now (from-inner op allNid inst) p vals sched st =
  ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
    capsDrainOK c sl sf allNid p id now lim (pred act) q sched st

-- WHAT A SUBSCRIBING FRAME HAS TO BE HANDED, AND IT IS NOT WHAT THE
-- ARRIVAL'S SYNTAX SAYS.  A `thru-outer` subscribes each value it takes,
-- so what it delivers is a run of that value's DEFINITION, and an
-- arrival may name its definition instead of carrying it.  The size
-- premise beside this one bounds the telescope and cannot bound this:
-- a definition naming a slot twice pays for it twice, so the resolved
-- closure is multiplicative in the telescope's depth where the written
-- sum is flat.  The two are independent, and this is the one the
-- module's own proven consumer of a subscription takes.
--
-- IT IS A PER-FRAME PREDICATE BECAUSE THE OBLIGATION IS.  Four of the
-- five frames forward what they are given and owe nothing here, and
-- their arms discharge it by `tt`; only the one that re-enters the
-- subscribe machinery with an arrival in hand can be surprised by what
-- the arrival names.
frameClosOK : ∀ {n} {Γ : Ctx n} {s u}
  (c : Caps) (sl : Slots Γ) (f : Frame Γ s u) (vals : List (Val Γ s)) → Set
frameClosOK c sl (map-f _)          vals = ⊤
frameClosOK c sl (scan-f _ _)       vals = ⊤
frameClosOK c sl (take-f _)         vals = ⊤
frameClosOK c sl (from-inner _ _ _) vals = ⊤
frameClosOK c sl (thru-outer _ _)   vals = all (nestClosOK? c sl) vals ≡ true

-- AND THE DRAIN'S WIDTH, CARRIED THE SAME WAY AND AT THE SAME ONE
-- FRAME.  It is a second predicate rather than a conjunct of the one
-- above because the two say different things about the same queue --
-- what the inners may reference, and how wide their descents may run --
-- and a site that wants either would otherwise have to take the pair
-- apart.
frameDrainW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (W : ℕ) (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) → Set
frameDrainW W sf id now (map-f _)    p vals sched st = ⊤
frameDrainW W sf id now (scan-f _ _) p vals sched st = ⊤
frameDrainW W sf id now (take-f _)   p vals sched st = ⊤
frameDrainW W sf id now (thru-outer op nid) p vals sched st =
  thruRoomWOK W sf op nid p id now vals sched st
frameDrainW {Γ = Γ} {u = u} W sf id now (from-inner op allNid inst) p vals sched st =
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
-- REFUTED: `Refuted.Thru-Fit-Frame-Slot` kills the unit-only form at
--   a shared slot -- one hundred and twenty-eight against seventy-six,
--   sixty-four against sixty-eight one layer shorter, so a crossing
--   and not a scale error, the telescope being priced by a `nestU`
--   linear in the unit against a subscribe that doubles per layer.
--   It does NOT kill the statement below, and the same file says so
--   mechanically: those rows are read at a size cap of one, while the
--   head bounds the RESOLVED telescope by that cap, and the telescope
--   at the refuting witness measures one hundred and fifteen.  At the
--   smallest cap the premise admits, the factor is a tower in that
--   number and the delivery is eight.  So the resolved-size premise is
--   what the slot axis buys, here as at the fit head it delegates to,
--   and the axis is spent rather than open.
abstract
  stepFrame-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (sf : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    ⦃ _ : FaceOK c sl ⦄ →
    Sched.slots sched ≡ sl →
    1 ≤ W → length vals ≤ W → capsOK? c sched st ≡ true →
    all (valCaps? c sl s) vals ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    frameClosOK c sl f vals →
    frameDrainOK c sl sf id now f p vals sched st →
    frameDrainW W sf id now f p vals sched st →
    1 ≤ Caps.cSize c →
    depthFrame sf id now f p vals fin sched st ≤ d →
    let r = stepFrame sf id now f p vals fin sched st in
    length (proj₁ r) ≤ W →
    Σ ℕ λ j →
    let S′ = Caps.cSize (frameStep j c) in
    (j ≤ sizeCount c d ⊔ Caps.cSize c)
    × ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
         ≤ nestFac S′ W
           * (frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
              + nestU S′ (nestUnit e sl)))
  stepFrame-nodes {e = e} c d W sl sf id now (map-f fn) p vals fin sched st hsl 1≤W hlen hc hv hss hfc hfd hfw h1S hdp hw =
    0 , z≤n ,
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
  stepFrame-nodes {e = e} c d W sl sf id now (scan-f fn nid) p vals fin sched st hsl 1≤W hlen hc hv hss hfc hfd hfw h1S hdp hw =
    0 , z≤n ,
    ≤-trans (stepFrame-nodes-scan W sf id now fn nid p vals fin sched st hlen)
            (raiseN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl)))
  stepFrame-nodes {e = e} c d W sl sf id now (take-f nid) p vals fin sched st hsl 1≤W hlen hc hv hss hfc hfd hfw h1S hdp hw =
    0 , z≤n ,
    ≤-trans (≤-trans (stepFrame-nodes-take sf id now nid p vals fin sched st)
                     (zero-charge W _))
            (raiseN (Caps.cSize c) W _ (nestU (Caps.cSize c) (nestUnit e sl)))
  stepFrame-nodes {e = e} c d W sl sf id now (from-inner op allNid inst) p vals fin sched st hsl 1≤W hlen hc hv hss hfc hfd hfw h1S hdp hw =
    let INNER = stepFrame-nodes-inner c d sl W sf id now op allNid inst p vals fin sched st
                  hsl hfd hfw hdp
        S′ = Caps.cSize (frameStep (proj₁ INNER) c) in
    proj₁ INNER
    , proj₁ (proj₂ INNER)
    , ≤-trans (proj₂ (proj₂ INNER))
            (*-monoʳ-≤ (nestFac S′ W)
              (+-monoˡ-≤ (nestU S′ (nestUnit e sl)) (zero-charge W _)))
  stepFrame-nodes {e = e} c d W sl sf id now (thru-outer op nid) p vals fin sched st hsl 1≤W hlen hc hv hss hfc hfd hfw h1S hdp hw =
    0 , z≤n ,
    ≤-trans (stepFrame-nodes-thru c W sl sf id now op nid p vals fin sched st
               hsl 1≤W hlen hc hv hss hfc h1S hfw hfd hw)
            (*-monoʳ-≤ (nestFac (Caps.cSize c) W)
              (+-monoˡ-≤ (nestU (Caps.cSize c) (nestUnit e sl))
                (≤-trans (m≤m+n (nodesMax st ⊔ nestDᵛˢ vals) (W * 1))
                         (one-pow W ((nodesMax st ⊔ nestDᵛˢ vals) + W * 1)))))

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
-- AND, AT A SINK, THE SAME OBLIGATIONS FOR EVERY WALK THE FAN-OUT
-- RUNS: the dispatch admits a registration list and folds a walk per
-- entry, so the hypothesis mirrors that fold — an entry the state has
-- cancelled owes nothing, and a delivered one owes its own walk's bound
-- and then the rest of the fold at the state its walk left.  The gas
-- index is what ties the recursion off: a walk's sink dispatches at the
-- walk's own gas, and the fold underneath runs one level down.
mutual
  burstsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  burstsOK W sf gas id now root           vals fin sched st = length vals ≤ W
  burstsOK W sf gas id now (share-sink i) vals fin sched st =
    (length vals ≤ W)
    × dispatchBurstsOK W sf gas id now i vals fin sched st
  burstsOK W sf gas id now (f ↠ p)        vals fin sched st =
    (length vals ≤ W)
    × frameDrainW W sf id now f p vals sched st
    × burstsOK W sf gas id now p (proj₁ step)
        (proj₁ (proj₂ (proj₂ step)))
        (proj₁ (proj₂ (proj₂ (proj₂ step))))
        (proj₂ (proj₂ (proj₂ (proj₂ step))))
    where step = stepFrame sf id now f p vals fin sched st

  dispatchBurstsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  dispatchBurstsOK W sf zero      id now i vals fin sched st = ⊤
  dispatchBurstsOK W sf (suc gas) id now i vals fin sched st =
    shareBurstsOK W sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  shareBurstsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  shareBurstsOK W sf gas id now i vals fin [] sched st = ⊤
  shareBurstsOK W sf gas id now i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then shareBurstsOK W sf gas id now i vals fin ps sched st
    else (burstsOK W sf gas id now p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
          × shareBurstsOK W sf gas id now i vals fin ps
              (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
                       (if fin then close (toℕ i) exhausted ∷ [] else [])
                       fin sched (record st { delivered = rid ∷ EvalSt.delivered st }))))
              (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
                       (if fin then close (toℕ i) exhausted ∷ [] else [])
                       fin sched (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- THE HEAD OF A WALK'S BURST BOUND, WHICH EVERY SHAPE OF PATH CARRIES.
-- Each clause bounds the list it is handed before it says anything about
-- the rest of the walk, so the frame lemma's premise about what a frame
-- EMITS is already in hand one step down -- the walk's own recursion is
-- what supplies it, and no second hypothesis is owed.
burstsHead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  burstsOK W sf gas id now p vals fin sched st → length vals ≤ W
burstsHead W sf gas id now root           vals fin sched st h = h
burstsHead W sf gas id now (share-sink _) vals fin sched st h = proj₁ h
burstsHead W sf gas id now (_ ↠ _)        vals fin sched st h = proj₁ h

-- AND THE DRAIN OBLIGATION AT THE SAME HEAD, projected out so the frame
-- lemma's premise comes off the walk's own recursion rather than being
-- owed a second time.
burstsDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
  (W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  burstsOK W sf gas id now (f ↠ p) vals fin sched st →
  frameDrainW W sf id now f p vals sched st
burstsDrain W sf gas id now f p vals fin sched st h = proj₁ (proj₂ h)

-- AND THE CAPS THE TWO `*All` FRAMES SPEND, carried the same way and for
-- the same reason.  A frame that re-enters the subscribe machinery is
-- charged in the SIZE of what it substitutes, and that size lives in the
-- store rather than in the frame -- so the walk has to be handed the
-- store's bound at every state it passes through, not just at the one it
-- starts from.  Stating it by recursion on the path is what lets the
-- induction take its own hypothesis apart instead of re-deriving the
-- caps face's frame counter in a second currency.
mutual
  capsWalkOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  capsWalkOK c sl sf gas id now root           vals fin sched st = capsOK? c sched st ≡ true
  capsWalkOK c sl sf gas id now (share-sink i) vals fin sched st =
    (capsOK? c sched st ≡ true)
    × dispatchCapsOK c sl sf gas id now i vals fin sched st
  capsWalkOK {u = u} c sl sf gas id now (f ↠ p) vals fin sched st =
    (capsOK? c sched st ≡ true)
    × (all (valCaps? c sl u) vals ≡ true)
    × (slotsSize sl ≤ Caps.cSize c)
    × frameClosOK c sl f vals
    × frameDrainOK c sl sf id now f p vals sched st
    × capsWalkOK c sl sf gas id now p (proj₁ step)
        (proj₁ (proj₂ (proj₂ step)))
        (proj₁ (proj₂ (proj₂ (proj₂ step))))
        (proj₂ (proj₂ (proj₂ (proj₂ step))))
    where step = stepFrame sf id now f p vals fin sched st

  dispatchCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  dispatchCapsOK c sl sf zero      id now i vals fin sched st = ⊤
  dispatchCapsOK c sl sf (suc gas) id now i vals fin sched st =
    shareCapsOK c sl sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  shareCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (sl : Slots Γ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  shareCapsOK c sl sf gas id now i vals fin [] sched st = ⊤
  shareCapsOK c sl sf gas id now i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then shareCapsOK c sl sf gas id now i vals fin ps sched st
    else (capsWalkOK c sl sf gas id now p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
          × shareCapsOK c sl sf gas id now i vals fin ps
              (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
                       (if fin then close (toℕ i) exhausted ∷ [] else [])
                       fin sched (record st { delivered = rid ∷ EvalSt.delivered st }))))
              (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
                       (if fin then close (toℕ i) exhausted ∷ [] else [])
                       fin sched (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- THE SHARE SINK, WHICH IS WHERE THE PATH MEASURES HAVE NOTHING LEFT
-- TO SPEND, and where the deliver measures pay instead.  The sink fans
-- the arriving values into every registration the state admits, and
-- each of those walks a path that lives in the REGISTRY rather than in
-- the chain being charged — so the sink's budget must price the
-- registry, and the caps are the one thing that does: `capsOK?` bounds
-- every registered path's frames and length by `cSize` and the
-- registry's count by `cReg`, so one dispatch level spends at most
-- `cReg` walks of caps-priced charge plus whatever the NEXT level's
-- sinks spend — the `fanLen`/`fanSq` recurrences, indexed by the
-- dispatch gas that ties the descent off.  The fold obligations mirror
-- the cascade fold's: each admitted entry owes its own walk's burst and
-- caps hypotheses at the state the fold reaches it in.
--
-- AND THE UNIT TERM IS K-INDEXED BECAUSE THE FOLD'S OWN CHARGE IS.
-- Each admitted registration pays `suc (deliverLen …) * U` additively,
-- which the size premise caps at one `suc (cSize + fanLen gas)` per
-- entry -- so a budget naming the whole level's allowance ONCE cannot
-- close the induction: the step's payment would have to fit inside a
-- term it does not grow.  Spent at `suc (k * suc (cSize + fanLen
-- gas))` each step's payment is EXACT, and at the registry cap it is
-- the level allowance again, since that is what the length recurrence
-- multiplies out to.  The two budgets are one budget, read at one k.
--
-- AND THE SEALED ALLOWANCES DO NOT SHUT INSTANTIATION, only the direct
-- route: `fanLen`, `fanSq` and `delSq` do not reduce, so no row reads
-- THROUGH them -- but writing the recurrences out from their own
-- equations reaches the conclusion at concrete programs.
--
-- AND A WITNESS FOR THE STACKING AXIS CANNOT BE BUILT FROM PARALLEL
-- BRANCHES, which is worth carrying before anyone instantiates the
-- leaves below.  Registrations each install their OWN node and
-- `nodesMax` is a join, so identical branches cannot compound however
-- many are folded -- a family of them delivers the same store at three
-- registrations as at one.  Compounding needs a registration whose
-- subscription deepens a node a LATER registration is then read at, and
-- a branch parked at a spent merge never carries depth forward.  The
-- Set-valued walk premises are unreachable at numerals besides, so only
-- the conclusion and the decidable size premise are ever pinnable.
--
-- TWIN: `cascadeGo-nodes-chains` — the proven fold over a cascade's
--   chain list, whose skip/deliver arms and telescope arithmetic are
--   the route for this fold, with the fan allowances standing where its
--   per-list sums stand.
-- DEAD ROUTE: strengthening the fold to a PRESERVATION -- carry a
--   ceiling `K`, show each step re-establishes it, which is how the caps
--   face avoids exactly this stacking with a pointwise predicate over
--   the nodes map instead of a MAX.  It does not close here: a step also
--   REGISTERS the inners it subscribes, so the premise bounding the
--   registry's own wraps has to be re-established at the grown registry,
--   and that quantity provably grows -- it is what the parent charges a
--   whole width factor for.  A preservation over the nodes map alone is
--   not enough, and one over the store is false.
-- REFUTED: `Refuted.Share-Sink-Nodes` kills the unit-free flat form,
--   three against one, and against two when the whole store measure is
--   charged in place of the nodes map.
-- REFUTED: `Refuted.Share-Go-Path` kills the premise-free form, four
--   against two: with the registration list a bound variable no premise
--   prices, a `map-f` frame carrying a constant the program never
--   mentions stores a value no program-denominated charge covers, and
--   the gap grows a layer per layer of the constant.  Under the current
--   form that constant's size is priced by `admSz?`, which is why the
--   cap squared appears in the fan allowances.
-- REFUTED: `Refuted.Share-Go-Registry` kills the predecessor statement
--   (premise `chainsNestD ps ≤ nestUnit`, flat unit conclusion), four
--   against two: a top list of one bare `share-sink` hop is priced at
--   zero, and the sink then admits from the STATE's registry, which
--   that premise never priced.  The current premises price the state's
--   registry through `capsOK?`, which is this refutation's repair.
-- REFUTED: `Refuted.Share-Go-Stack` kills the max-premised repair of
--   the predecessor (add `regsNestMax st ≤ nestUnit`), three against
--   two: a branch that descends through TWO shares spends each hop's
--   whole allowance in SEQUENCE, so per-path independent pricing — any
--   max — stacks whatever it licensed once per level.  The gas-indexed
--   fan recurrences are the branch-structured charge that refutation
--   demands: each level's allowance contains the next level's whole.
-- RECOVERY: git show 7b5936b:agda/evidence/probed/Probed/Share-Go-Fold.agda
--   restores the harness -- the four-deep constant registration, the
--   written-out recurrences and the `admSz?` pins.

-- ONE ADMITTED REGISTRATION'S OWN GRANT, WIDENED INTO ONE UNIT OF THE
-- BRANCH BUDGET.  The entry's path measures are capped by the size
-- premise the fold carries for the whole admitted list: its length
-- fits one `suc (cSize + fanLen gas)`, its factor the square's power
-- of two and its depth the square, which is what makes a unit a unit.
-- The unit it prices sits one gas level below the level the fold's
-- conclusion prices, and the delivery caps grow with the gas.
-- AND THE FACTOR AND THE UNIT ARE READ AT A SECOND CAP, which is the
-- LEVEL the walk under this fold reported.  The path measures and the
-- fan allowances stay at the entry cap -- they price the PROGRAM's own
-- shape, which no substitution moves -- while the two quantities a
-- substituting head grows travel with the level.  The two are
-- independent, so the widening premise is componentwise and the proof
-- is the one-cap proof with the two readings renamed.
shareFold-unit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c c′ : Caps) (W : ℕ) (sl : Slots Γ) (gas : ℕ)
  (p : Path Γ u t) (X : ℕ) →
  1 ≤ Caps.cSize c → pathSz? (Caps.cSize c) p ≡ true →
  nestFac (Caps.cSize c′) W ^ deliverLen gas c p
    * (deliverNestF gas c p ^ W
       * (X + W * (deliverNestD gas c p
                   + suc (deliverLen gas c p)
                     * nestU (delSq gas c′) (nestUnit e sl))))
    ≤ nestFac (Caps.cSize c′) W ^ suc (Caps.cSize c + fanLen gas c)
      * ((2 ^ (Caps.cSize c * Caps.cSize c + fanSq gas c)) ^ W
         * (X + W * ((Caps.cSize c * Caps.cSize c + fanSq gas c)
                     + suc (Caps.cSize c + fanLen gas c)
                       * nestU (delSq (suc gas) c′) (nestUnit e sl))))
shareFold-unit {e = e} c c′ W sl gas p X 1≤S hsz =
  ≤-trans (*-monoʳ-≤ (Q ^ dL)
            (*-mono-≤ facLE
              (+-monoʳ-≤ X (*-monoʳ-≤ W (+-mono-≤ depLE (*-mono-≤ (s≤s lenLE) unitLE))))))
          (*-monoˡ-≤ ((2 ^ Sq) ^ W * (X + W * (Sq + Lu * U)))
            (pow-mono-exp Q (1≤nestFac S′ W)
              (≤-trans lenLE (n≤1+n (S + fanLen gas c)))))
  where
  S  = Caps.cSize c
  S′ = Caps.cSize c′
  Q  = nestFac S′ W
  Sq = S * S + fanSq gas c
  Lu = suc (S + fanLen gas c)
  U  = nestU (delSq (suc gas) c′) (nestUnit e sl)
  dL = deliverLen gas c p

  lenLE : dL ≤ S + fanLen gas c
  lenLE = ≤-trans (deliverLen-path gas c p)
                  (+-monoˡ-≤ (fanLen gas c) (pathSz?-len S p hsz))

  facLE : deliverNestF gas c p ^ W ≤ (2 ^ Sq) ^ W
  facLE = ^-monoˡ-≤ W
    (≤-trans (≤-reflexive (deliverNestF≡ gas c p))
             (pow-mono-exp 2 (s≤s z≤n)
               (≤-trans (deliverSzSum-path gas c p)
                        (+-monoˡ-≤ (fanSq gas c) (pathSzSum-cap S p hsz)))))

  depLE : deliverNestD gas c p ≤ Sq
  depLE = ≤-trans (deliverNestD-path gas c p)
    (+-monoˡ-≤ (fanSq gas c)
      (≤-trans (pathNestD-len S p 1≤S hsz)
               (*-monoˡ-≤ S (pathSz?-len S p hsz))))

  unitLE : nestU (delSq gas c′) (nestUnit e sl) ≤ U
  unitLE = nestU-mono (delSq gas c′) (delSq (suc gas) c′) (nestUnit e sl)
                      (delSq-mono gas c′)

-- AND THE TELESCOPE THE FOLD COMPOSES WITH, which is where the unit
-- term's `k` earns itself: a store already inside ONE unit, carried
-- through `k` of them, lands inside `k + 1`.  The two additive charges
-- meet exactly -- a unit's `Lu * U` IS the difference between
-- successive unit terms -- so the arithmetic below is an identity at
-- the boundary and not a bound with room in it.
shareFold-tele : (Q W Lu Sq U k X H : ℕ) → 1 ≤ Q →
  H ≤ Q ^ Lu * ((2 ^ Sq) ^ W * (X + W * (Sq + Lu * U))) →
  Q ^ (k * Lu) * ((2 ^ (k * Sq)) ^ W * (H + W * (k * Sq + suc (k * Lu) * U)))
    ≤ Q ^ (suc k * Lu)
      * ((2 ^ (suc k * Sq)) ^ W
         * (X + W * (suc k * Sq + suc (suc k * Lu) * U)))
shareFold-tele Q W Lu Sq U k X H 1≤Q hH =
  ≤-trans (*-monoʳ-≤ Fk (*-monoʳ-≤ Pk (+-monoˡ-≤ Y intoUnit)))
  (≤-trans (*-monoʳ-≤ Fk (nest-telescope (F * P) Pk X A Y 1≤FP))
           (≤-reflexive shuffle))
  where
  F  = Q ^ Lu
  P  = (2 ^ Sq) ^ W
  Fk = Q ^ (k * Lu)
  Pk = (2 ^ (k * Sq)) ^ W
  A  = W * (Sq + Lu * U)
  Y  = W * (k * Sq + suc (k * Lu) * U)

  1≤FP : 1 ≤ F * P
  1≤FP = *-mono-≤ (1≤pow≤ Q Lu 1≤Q) (1≤pow≤ (2 ^ Sq) W (m^n>0 2 Sq))

  intoUnit : H ≤ F * P * (X + A)
  intoUnit = ≤-trans hH (≤-reflexive (sym (*-assoc F P (X + A))))

  -- the two factors rejoin their own exponent, and the two additive
  -- charges rejoin as one step of the unit term
  facQ : Fk * F ≡ Q ^ (suc k * Lu)
  facQ = trans (sym (^-distribˡ-+-* Q (k * Lu) Lu))
               (cong (Q ^_) (+-comm (k * Lu) Lu))

  facP : Pk * P ≡ (2 ^ (suc k * Sq)) ^ W
  facP = trans (sym (pow-distrib-* W (2 ^ (k * Sq)) (2 ^ Sq)))
               (cong (_^ W) (trans (sym (^-distribˡ-+-* 2 (k * Sq) Sq))
                                   (cong (2 ^_) (+-comm (k * Sq) Sq))))

  charge : A + Y ≡ W * (suc k * Sq + suc (suc k * Lu) * U)
  charge = trans (sym (*-distribˡ-+ W (Sq + Lu * U) (k * Sq + suc (k * Lu) * U)))
                 (cong (W *_) inner)
    where
    inner : (Sq + Lu * U) + (k * Sq + suc (k * Lu) * U)
              ≡ suc k * Sq + suc (suc k * Lu) * U
    inner = solve 4 (λ sq lu u kk →
              (sq :+ lu :* u) :+ (kk :* sq :+ (con 1 :+ kk :* lu) :* u)
                := (sq :+ kk :* sq) :+ (con 1 :+ (lu :+ kk :* lu)) :* u)
              refl Sq Lu U k

  shuffle : Fk * (F * P * Pk * (X + (A + Y)))
              ≡ Q ^ (suc k * Lu)
                * ((2 ^ (suc k * Sq)) ^ W
                   * (X + W * (suc k * Sq + suc (suc k * Lu) * U)))
  shuffle =
    trans (solve 5 (λ fk f p pk z → fk :* (f :* p :* pk :* z)
                                      := (fk :* f) :* ((pk :* p) :* z))
             refl Fk F P Pk (X + (A + Y)))
    (trans (cong₂ (λ a b → a * (b * (X + (A + Y)))) facQ facP)
           (cong (λ z → Q ^ (suc k * Lu) * ((2 ^ (suc k * Sq)) ^ W * (X + z)))
                 charge))

shareGoFold-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (sf : Gas) (gas : ℕ)
    (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t)) (k : ℕ)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c →
    admSz? (Caps.cSize c) ps ≡ true →
    length ps ≤ k → k ≤ Caps.cReg c →
    shareBurstsOK W sf gas id now i vals fin ps sched st →
    shareCapsOK c sl sf gas id now i vals fin ps sched st →
    depthShareGo sf gas id now i vals fin ps sched st ≤ d →
  ⦃ _ : FaceOK c sl ⦄ →
    Σ ℕ λ j →
    let c′ = frameStep j c in
    (j ≤ sizeCount c d ⊔ Caps.cSize c)
    × (nodesMax (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
      ≤ nestFac (Caps.cSize c′) W ^ (k * suc (Caps.cSize c + fanLen gas c))
        * ((2 ^ (k * (Caps.cSize c * Caps.cSize c + fanSq gas c))) ^ W
           * ((nodesMax st ⊔ nestDᵛˢ vals)
              + W * (k * (Caps.cSize c * Caps.cSize c + fanSq gas c)
                     + suc (k * suc (Caps.cSize c + fanLen gas c))
                       * nestU (delSq (suc gas) c′) (nestUnit e sl)))))

-- The whole-list statement is the budgeted fold spent at the registry
-- cap: the allowances' own step equations convert the spent budget
-- into the sealed recurrences, and nothing else moves.
shareGo-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (sf : Gas) (gas : ℕ)
  (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c →
  admSz? (Caps.cSize c) ps ≡ true →
  length ps ≤ Caps.cReg c →
  shareBurstsOK W sf gas id now i vals fin ps sched st →
  shareCapsOK c sl sf gas id now i vals fin ps sched st →
  depthShareGo sf gas id now i vals fin ps sched st ≤ d →
  ⦃ _ : FaceOK c sl ⦄ →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
    ≤ nestFac (Caps.cSize c′) W ^ fanLen (suc gas) c
      * ((2 ^ fanSq (suc gas) c) ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (fanSq (suc gas) c
                   + suc (fanLen (suc gas) c) * nestU (delSq (suc gas) c′) (nestUnit e sl)))))
shareGo-nodes {e = e} c d W sl sf gas id now i vals fin ps sched st
  hsl 1≤W 1≤S hadm hlen hb hc hdp =
  proj₁ FOLD ,
  proj₁ (proj₂ FOLD) ,
  ≤-trans (proj₂ (proj₂ FOLD))
          (≤-reflexive (cong₂ (λ a b →
              nestFac (Caps.cSize (frameStep (proj₁ FOLD) c)) W ^ a
                * ((2 ^ b) ^ W
                   * ((nodesMax st ⊔ nestDᵛˢ vals)
                      + W * (b + suc a
                             * nestU (delSq (suc gas) (frameStep (proj₁ FOLD) c))
                                     (nestUnit e sl)))))
            (sym (fanLen-suc gas c)) (sym (fanSq-suc gas c))))
  where
  FOLD = shareGoFold-nodes c d W sl sf gas id now i vals fin ps (Caps.cReg c)
           sched st hsl 1≤W 1≤S hadm hlen ≤-refl hb hc hdp

-- AND THE SINK ITSELF IS THREE ARMS OVER THAT FOLD, none of which
-- touches the nodes map: out of dispatch gas the state is returned
-- untouched, and the finishing arm latches the share's source into the
-- dying and completed ledgers, which are not the map.  So the whole of
-- the sink's growth is the fold's, and the leaf is the fold.  The
-- admitted list's own pricing is read off `capsOK?` here — the admitted
-- registrations are a sublist of the registry, so they inherit its
-- `regsSz?` receipt and its count bound.
dispatchShare-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (sf : Gas) (gas : ℕ)
  (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c →
  capsOK? c sched st ≡ true →
  dispatchBurstsOK W sf gas id now i vals fin sched st →
  dispatchCapsOK c sl sf gas id now i vals fin sched st →
  depthDisp sf gas id now i vals fin sched st ≤ d →
  ⦃ _ : FaceOK c sl ⦄ →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
    ≤ nestFac (Caps.cSize c′) W ^ fanLen gas c
      * ((2 ^ fanSq gas c) ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (fanSq gas c
                   + suc (fanLen gas c) * nestU (delSq gas c′) (nestUnit e sl)))))
dispatchShare-nodes c d W sl sf zero id now i vals fin sched st hsl 1≤W 1≤S hcaps hdb hdc hdp
  rewrite fanLen-zero c | fanSq-zero c =
  0 , z≤n ,
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
dispatchShare-nodes c d W sl sf (suc gas) id now i vals false sched st hsl 1≤W 1≤S hcaps hdb hdc hdp =
  shareGo-nodes c d W sl sf gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sched st hsl 1≤W 1≤S
    (shareAdmit-sz i (Caps.cSize c) (EvalSt.registry st)
      (proj₁ (proj₂ (capsOK?-parts c sched st hcaps))))
    (≤-trans (shareAdmit-len i (EvalSt.registry st))
             (≤ᵇ⇒≤ (length (EvalSt.registry st)) (Caps.cReg c)
               (T-to (proj₂ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st hcaps))))))))
    hdb hdc hdp
dispatchShare-nodes c d W sl sf (suc gas) id now i vals true sched st hsl 1≤W 1≤S hcaps hdb hdc hdp =
  shareGo-nodes c d W sl sf gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) hsl 1≤W 1≤S
    (shareAdmit-sz i (Caps.cSize c) (EvalSt.registry st)
      (proj₁ (proj₂ (capsOK?-parts c sched st hcaps))))
    (≤-trans (shareAdmit-len i (EvalSt.registry st))
             (≤ᵇ⇒≤ (length (EvalSt.registry st)) (Caps.cReg c)
               (T-to (proj₂ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st hcaps))))))))
    hdb hdc hdp

foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ)
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c →
  burstsOK W sf gas id now path vals fin sched st →
  capsWalkOK c sl sf gas id now path vals fin sched st →
  depthFold sf gas id now envSrc path vals evs fin sched st ≤ d →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ (nestFac (Caps.cSize c′) W) ^ deliverLen gas c path
      * (deliverNestF gas c path ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (deliverNestD gas c path
                   + suc (deliverLen gas c path) * nestU (delSq gas c′) (nestUnit e sl)))))
foldPath-nodes c d W sl sf gas id now envSrc root vals evs fin sched st hsl 1≤W 1≤S hb hc hdp =
  0 , z≤n ,
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c d W sl sf gas id now envSrc (share-sink i) vals evs fin sched st hsl 1≤W 1≤S hb hc hdp =
  -- the sink arm IS the dispatch, level and all: every deliver measure
  -- at a `share-sink` reduces to the fan allowance the dispatch is
  -- already stated over, so the two conclusions are the same statement
  dispatchShare-nodes c d W sl sf gas id now i vals fin sched st hsl 1≤W 1≤S
    (proj₁ hc) (proj₂ hb) (proj₂ hc) hdp
foldPath-nodes {e = e} c d W sl sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl 1≤W 1≤S hb hc hdp =
  jt ,
  ⊔-lub (proj₁ (proj₂ IHr)) (proj₁ (proj₂ SFr)) ,
  ≤-trans IHw
    (≤-trans (*-monoʳ-≤ (Q ^ deliverLen gas c p)
                (*-monoʳ-≤ (deliverNestF gas c p ^ W)
                  (+-monoˡ-≤ (W * (deliverNestD gas c p + L * U))
                             (≤-trans SFw
                               (*-monoʳ-≤ Q (+-monoʳ-≤ A unit≤))))))
    (≤-trans (*-monoʳ-≤ (Q ^ deliverLen gas c p)
                (fac-hoist Q (deliverNestF gas c p ^ W) (A + U) (W * (deliverNestD gas c p + L * U))
                           1≤Q))
    (≤-trans (≤-reflexive (sym (*-assoc (Q ^ deliverLen gas c p) Q Inner)))
    (≤-trans (≤-reflexive (cong (_* Inner) (*-comm (Q ^ deliverLen gas c p) Q)))
             (*-monoʳ-≤ (Q ^ suc (deliverLen gas c p))
    (≤-trans (*-monoʳ-≤ (deliverNestF gas c p ^ W)
               (≤-trans (≤-reflexive (+-assoc A U (W * (deliverNestD gas c p + L * U))))
                        (+-monoʳ-≤ A widen)))
    (≤-trans (nest-telescope (frameNestF f ^ W) (deliverNestF gas c p ^ W) B
                             (W * frameNestD f) (W * (deliverNestD gas c p + L * U) + W * U)
                             (1≤pow≤ (frameNestF f) W (1≤frameNestF f)))
             (≤-reflexive
               (cong₂ _*_ (sym (pow-distrib-* W (frameNestF f) (deliverNestF gas c p)))
                          (cong (B +_) charge))))))))))
  where
  step   = stepFrame sf id now f p vals fin sched st
  vals′  = proj₁ step
  evs′   = proj₁ (proj₂ step)
  fin′   = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))

  IHr = foldPath-nodes c d W sl sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
          (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl)
          1≤W 1≤S (proj₂ (proj₂ hb)) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hc)))))
          (≤-trans (m≤n⊔m _ _) hdp)
  SFr = stepFrame-nodes c d W sl sf id now f p vals fin sched st
          hsl 1≤W (proj₁ hb) (proj₁ hc) (proj₁ (proj₂ hc))
          (proj₁ (proj₂ (proj₂ hc))) (proj₁ (proj₂ (proj₂ (proj₂ hc))))
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hc)))))
          (burstsDrain W sf gas id now f p vals fin sched st hb)
          1≤S
          (≤-trans (m≤m⊔n _ _) hdp)
          (burstsHead W sf gas id now p vals′ fin′ sched₁ st₁ (proj₂ (proj₂ hb)))
  jᵢ = proj₁ IHr
  jₛ = proj₁ SFr
  jt = jᵢ ⊔ jₛ
  c′ = frameStep jt c

  -- THE LEVEL IS A JOIN, and nothing more, because both sub-results
  -- report their own and the whole conclusion is increasing in it.  The
  -- size cap climbs with the count and the registry cap climbs
  -- linearly, so the delivery square climbs with both -- which is what
  -- the two widenings below spend, one per sub-result.
  sizeᵢ : Caps.cSize (frameStep jᵢ c) ≤ Caps.cSize c′
  sizeᵢ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S (m≤m⊔n jᵢ jₛ)

  sizeₛ : Caps.cSize (frameStep jₛ c) ≤ Caps.cSize c′
  sizeₛ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S (m≤n⊔m jᵢ jₛ)

  regᵢ : Caps.cReg (frameStep jᵢ c) ≤ Caps.cReg c′
  regᵢ = frameStep-reg-mono c (m≤m⊔n jᵢ jₛ)

  S      = Caps.cSize c′
  Q      = nestFac S W
  1≤Q    = 1≤nestFac S W
  A      = frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
  Inner  = deliverNestF gas c p ^ W * ((A + nestU (delSq gas c′) (nestUnit e sl))
                              + W * (deliverNestD gas c p + suc (deliverLen gas c p) * nestU (delSq gas c′) (nestUnit e sl)))
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestU (delSq gas c′) (nestUnit e sl)
  L      = suc (deliverLen gas c p)

  Uᵢ≤ : nestU (delSq gas (frameStep jᵢ c)) (nestUnit e sl) ≤ U
  Uᵢ≤ = nestU-mono (delSq gas (frameStep jᵢ c)) (delSq gas c′) (nestUnit e sl)
                   (delSq-monoᶜ gas (frameStep jᵢ c) c′ sizeᵢ regᵢ)

  IHw = ≤-trans (proj₂ (proj₂ IHr))
          (*-mono-≤ (^-monoˡ-≤ (deliverLen gas c p)
                       (nestFac-monoS sizeᵢ W))
            (*-monoʳ-≤ (deliverNestF gas c p ^ W)
              (+-monoʳ-≤ (nodesMax st₁ ⊔ nestDᵛˢ vals′)
                (*-monoʳ-≤ W
                  (+-monoʳ-≤ (deliverNestD gas c p)
                    (*-monoʳ-≤ (suc (deliverLen gas c p)) Uᵢ≤))))))

  SFw = ≤-trans (proj₂ (proj₂ SFr))
          (*-mono-≤ (nestFac-monoS sizeₛ W)
            (+-monoʳ-≤ (frameNestF f ^ W
                          * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f))
              (nestU-mono (Caps.cSize (frameStep jₛ c)) S (nestUnit e sl) sizeₛ)))

  -- the frame face prices its unit at the bare size cap; the walk
  -- prices it at the delivery square, which is the wider of the two --
  -- and both are read at the LEVEL, which is what makes the square
  -- contain the cap it is a square of
  unit≤ : nestU S (nestUnit e sl) ≤ U
  unit≤ = nestU-mono S (delSq gas c′) (nestUnit e sl)
                     (cSize≤delSq gas c′ (≤-trans 1≤S (iterSize-infl (Caps.cSize c) 1≤S jt (Caps.cSize c))))

  -- the frame's own summand is paid out of the extra `W * U` the path's
  -- coefficient gains at this level, and `1 ≤ W` is what makes it fit
  widen : U + W * (deliverNestD gas c p + L * U) ≤ W * (deliverNestD gas c p + L * U) + W * U
  widen = ≤-trans (≤-reflexive (+-comm U (W * (deliverNestD gas c p + L * U))))
                  (+-monoʳ-≤ (W * (deliverNestD gas c p + L * U))
                    (≤-trans (≤-reflexive (sym (*-identityˡ U)))
                             (*-monoˡ-≤ U 1≤W)))
  charge : W * frameNestD f + (W * (deliverNestD gas c p + L * U) + W * U)
             ≡ W * (deliverNestD gas c (f ↠ p) + suc L * U)
  charge =
    trans (cong (W * frameNestD f +_)
            (sym (*-distribˡ-+ W (deliverNestD gas c p + L * U) U)))
    (trans (sym (*-distribˡ-+ W (frameNestD f) ((deliverNestD gas c p + L * U) + U)))
           (cong (W *_) inner))
    where
    inner : frameNestD f + ((deliverNestD gas c p + L * U) + U)
              ≡ deliverNestD gas c (f ↠ p) + (U + L * U)
    inner =
      trans (cong (frameNestD f +_)
              (trans (+-assoc (deliverNestD gas c p) (L * U) U)
                     (cong (deliverNestD gas c p +_) (+-comm (L * U) U))))
      (trans (sym (+-assoc (frameNestD f) (deliverNestD gas c p) (U + L * U)))
             (cong (_+ (U + L * U)) (sym (deliverNestD-cons gas c f p))))

-- The fold's own three arms, which are `shareGo`'s: an empty list
-- returns the state it was handed, a cancelled registration is skipped
-- without spending any of the budget, and a delivered one spends
-- exactly one unit of it.  Only the last arm is an induction, and its
-- two halves are the walk that runs the entry and the fold that runs
-- the rest -- so the budget decrements where the list does.
shareGoFold-nodes {e = e} c d W sl sf gas id now i vals fin [] k sched st
                  hsl 1≤W 1≤S hadm hlen hk hb hc hdp =
  0 , z≤n ,
  ≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))
  (≤-trans (m≤m+n _ _)
  (≤-trans (grow ((2 ^ (k * (Caps.cSize c * Caps.cSize c + fanSq gas c))) ^ W) _
             (1≤pow≤ (2 ^ (k * (Caps.cSize c * Caps.cSize c + fanSq gas c))) W
               (m^n>0 2 (k * (Caps.cSize c * Caps.cSize c + fanSq gas c)))))
           (grow (nestFac (Caps.cSize c) W ^ (k * suc (Caps.cSize c + fanLen gas c))) _
             (1≤pow≤ (nestFac (Caps.cSize c) W)
               (k * suc (Caps.cSize c + fanLen gas c))
               (1≤nestFac (Caps.cSize c) W)))))
  where
  grow : ∀ (F Y : ℕ) → 1 ≤ F → Y ≤ F * Y
  grow F Y 1≤F = ≤-trans (≤-reflexive (sym (*-identityˡ Y))) (*-monoˡ-≤ Y 1≤F)
shareGoFold-nodes {e = e} c d W sl sf gas id now i vals fin ((rid , p) ∷ ps) (suc k)
                  sched st hsl 1≤W 1≤S hadm (s≤s hlen) hk hb hc hdp
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true  | hb′ | hc′ =
  shareGoFold-nodes c d W sl sf gas id now i vals fin ps (suc k) sched st hsl 1≤W 1≤S
    (proj₂ (∧-true _ _ hadm)) (≤-trans hlen (n≤1+n k)) hk hb′ hc′
    (≤-trans (m≤m⊔n _ _) hdp)
... | false | hb′ | hc′ =
  jt ,
  ⊔-lub (proj₁ (proj₂ TAILr)) (proj₁ (proj₂ HEADr)) ,
  ≤-trans TAILw
          (shareFold-tele Q W Lu Sq U k X (nodesMax st₁ ⊔ nestDᵛˢ vals)
             (1≤nestFac (Caps.cSize c′) W) fit)
  where
  st′  = record st { delivered = rid ∷ EvalSt.delivered st }
  evs  = if fin then close (toℕ i) exhausted ∷ [] else []
  r    = foldPath sf gas id now (toℕ i) p vals evs fin sched st′
  sched₁ = proj₁ (proj₂ r)
  st₁    = proj₂ (proj₂ r)

  -- THE FOLD'S LEVEL IS THE JOIN OF ITS TWO HALVES, exactly as the path
  -- fold's is: this entry's own walk reports one and the rest of the
  -- ring reports another, and neither half can be asked to have used
  -- the other's.  Both are widened to the join before they meet, which
  -- is the only place the ordering is spent.
  HEADr = foldPath-nodes c d W sl sf gas id now (toℕ i) p vals evs fin sched st′
            hsl 1≤W 1≤S (proj₁ hb′) (proj₁ hc′)
            (lub3-m (depthShareGo sf gas id now i vals fin ps sched st)
                    (depthFold sf gas id now (toℕ i) p vals evs fin sched st′)
                    (depthShareGo sf gas id now i vals fin ps sched₁ st₁) hdp)
  TAILr = shareGoFold-nodes c d W sl sf gas id now i vals fin ps k sched₁ st₁
            (trans (foldPath-slots sf gas id now (toℕ i) p vals evs fin sched st′) hsl)
            1≤W 1≤S (proj₂ (∧-true _ _ hadm)) hlen (≤-trans (n≤1+n k) hk)
            (proj₂ hb′) (proj₂ hc′)
            (lub3-r (depthShareGo sf gas id now i vals fin ps sched st)
                    (depthFold sf gas id now (toℕ i) p vals evs fin sched st′)
                    (depthShareGo sf gas id now i vals fin ps sched₁ st₁) hdp)
  jt = proj₁ TAILr ⊔ proj₁ HEADr
  c′ = frameStep jt c

  Q  = nestFac (Caps.cSize c′) W
  Lu = suc (Caps.cSize c + fanLen gas c)
  Sq = Caps.cSize c * Caps.cSize c + fanSq gas c
  U  = nestU (delSq (suc gas) c′) (nestUnit e sl)
  X  = nodesMax st ⊔ nestDᵛˢ vals

  grow : ∀ (F Y : ℕ) → 1 ≤ F → Y ≤ F * Y
  grow F Y 1≤F = ≤-trans (≤-reflexive (sym (*-identityˡ Y))) (*-monoˡ-≤ Y 1≤F)

  sizeₕ : Caps.cSize (frameStep (proj₁ HEADr) c) ≤ Caps.cSize c′
  sizeₕ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
            (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  regₕ : Caps.cReg (frameStep (proj₁ HEADr) c) ≤ Caps.cReg c′
  regₕ = frameStep-reg-mono c (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  sizeₜ : Caps.cSize (frameStep (proj₁ TAILr) c) ≤ Caps.cSize c′
  sizeₜ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
            (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  regₜ : Caps.cReg (frameStep (proj₁ TAILr) c) ≤ Caps.cReg c′
  regₜ = frameStep-reg-mono c (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  HEADw = ≤-trans (proj₂ (proj₂ HEADr))
            (*-mono-≤ (^-monoˡ-≤ (deliverLen gas c p) (nestFac-monoS sizeₕ W))
              (*-monoʳ-≤ (deliverNestF gas c p ^ W)
                (+-monoʳ-≤ (nodesMax st′ ⊔ nestDᵛˢ vals)
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (deliverNestD gas c p)
                      (*-monoʳ-≤ (suc (deliverLen gas c p))
                        (nestU-mono (delSq gas (frameStep (proj₁ HEADr) c))
                                    (delSq gas c′) (nestUnit e sl)
                          (delSq-monoᶜ gas (frameStep (proj₁ HEADr) c) c′ sizeₕ regₕ))))))))

  TAILw = ≤-trans (proj₂ (proj₂ TAILr))
            (*-mono-≤ (^-monoˡ-≤ (k * Lu) (nestFac-monoS sizeₜ W))
              (*-monoʳ-≤ ((2 ^ (k * Sq)) ^ W)
                (+-monoʳ-≤ (nodesMax st₁ ⊔ nestDᵛˢ vals)
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (k * Sq)
                      (*-monoʳ-≤ (suc (k * Lu))
                        (nestU-mono (delSq (suc gas) (frameStep (proj₁ TAILr) c))
                                    (delSq (suc gas) c′) (nestUnit e sl)
                          (delSq-monoᶜ (suc gas) (frameStep (proj₁ TAILr) c) c′
                                       sizeₜ regₜ))))))))

  unit : ℕ
  unit = Q ^ Lu * ((2 ^ Sq) ^ W * (X + W * (Sq + Lu * U)))

  Inner : ℕ
  Inner = X + W * (Sq + Lu * U)

  X≤unit : X ≤ unit
  X≤unit =
    ≤-trans (m≤m+n X (W * (Sq + Lu * U)))
    (≤-trans (grow ((2 ^ Sq) ^ W) Inner (1≤pow≤ (2 ^ Sq) W (m^n>0 2 Sq)))
             (grow (Q ^ Lu) ((2 ^ Sq) ^ W * Inner)
                   (1≤pow≤ Q Lu (1≤nestFac (Caps.cSize c′) W))))

  fit : (nodesMax st₁ ⊔ nestDᵛˢ vals) ≤ unit
  fit = ⊔-lub
    (≤-trans HEADw
             (shareFold-unit {e = e} c c′ W sl gas p X 1≤S (proj₁ (∧-true _ _ hadm))))
    (≤-trans (m≤n⊔m (nodesMax st) (nestDᵛˢ vals)) X≤unit)
