-- Verify-Budget-Sufficient.Nest-Walk
-- foldPath-nodes … frameNestD
module Verify-Budget-Sufficient.Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Data.Bool.ListAction using (any; all)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤;
   *-assoc; *-comm; m^n>0;
   *-identityˡ; *-identityʳ; *-zeroʳ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; +-mono-≤;
   *-distribˡ-+; ^-zeroˡ; +-identityʳ;
   m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub; ⊔-assoc; ⊔-mono-≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Tick; Id; Source; Gas; g0; gs; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; Fn; Exp; _×ᵗ_; obs; sizeᵗ; applyFn; _≟ᵗ_)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵗ; nestDᵛ; nestDᵉ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; foldPath; dispatchShare; stepFrame; shareGo; shareAdmit; shareLatch; RegId;
  NodeId; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeState; scan-st; take-st; takeVals; mergeAll-st;
  switch-st; exhaust-st; lookupNode; setNode; scanVals; innerFinish; aliveThroughᶠ;
  mergeAllDrain; subscribeInner; hasRoom; subscribeE; splitBurst)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps using (1≤pow≤; Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (capsOK?-nextNode)
open import Verify-Budget-Sufficient.Measures using (pathLen)
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
  addU : ∀ (S X U : ℕ) → 2 ^ S * X ≤ 2 ^ S * (X + U)
  addU S X U = *-monoʳ-≤ (2 ^ S) (m≤m+n X U)

  raiseU : ∀ (S X U : ℕ) → X ≤ 2 ^ S * (X + U)
  raiseU S X U = ≤-trans (pow-grow 2 S X (s≤s z≤n)) (addU S X U)

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
-- PROBED: `Probed.Subscribe-Nest` clears the restated form at the same
--   witness and the same tight cap, at the width this statement's own
--   hypotheses pin -- `1 ≤ W` and one value.  The crossing is the row
--   that could have failed: eighty delivered against forty-one at a
--   factor of one, which is the refutation directly above, and against
--   eighty-two at a factor of two, while the cap the value's size grants
--   is a hundred and seventy-three.  Not covered: one frame, one value,
--   and a node table holding the single ordinary node a subscribe
--   installs.
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
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ 2 ^ Caps.cSize c * ((nodesMax st ⊔ nestDᵛˢ vals) + W)

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
  (Sched.slots sched ≡ sl) × (capsOK? c sched st ≡ true)
capsDrainOK {s = s} c sl sf allNid κ id now lim act (o ∷ q) sched st =
  (Sched.slots sched ≡ sl) × (capsOK? c sched st ≡ true)
  × (valCaps? c sl (obs s) o ≡ true)
  × capsDrainOK c sl sf allNid κ id now lim
      (if proj₁ (proj₂ (proj₂ (proj₂ r))) then act else suc act) q
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
  where r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st

-- THE SUBSCRIPTION'S OWN DESCENT, and the leaf the arm finally rests on.
-- `subscribeInner` mints an instance id and hands the inner to
-- `subscribeE` under a `from-inner` frame; out of gas it emits a dry
-- event and touches nothing, so the whole charge is the descent's.
-- The `valCaps?` premise is what puts the subscribed observable inside
-- the exponent: the factor is two to a SIZE cap, and a cap the value
-- itself is not held to bounds the state and nothing that enters it.
--
-- REFUTED: `Refuted.Inner-Drain-Nest` kills the free form, eighty
--   against forty, at a queued `mapᵉ` whose step function names its
--   payload on both sides of the sum: `nestDᵉ` is additive there and the
--   substitution is not, so the emitted value is deeper than the whole
--   queue is charged.  The same witness kills the ASSEMBLY at the frame
--   above, whose charge reduces to exactly this bound.
-- REFUTED: `Refuted.Inner-Drain-Nest` also kills the repair this most
--   invites -- charging the arm the `nestUnit e sl` its own parent
--   already carries -- at a hundred and twenty against eighty-two, with
--   the queued observable AS the program so the unit is as large as the
--   currency admits.  A third occurrence of the payload in the step
--   function moves the emit and leaves the unit where it was, so what
--   is owed is a FACTOR in the substituted function's SIZE and no
--   summand in a depth currency is one.
-- REFUTED: `Refuted.Inner-Drain-Share-Nest` kills the caps-scaled form
--   from the other side, forty delivered against a charge of ZERO, at a
--   queue holding nothing but a reference to an observable-typed share.
--   `nestDᵉ (input i)` is zero and rightly so -- the syntax of a slot
--   reference says nothing about the slot -- and the node table does not
--   read the slots either, so the charged side is empty and every factor
--   is a multiple of nothing.  Taken with the row above it this pins the
--   shape exactly: the factor AND a slots summand, each of which is dead
--   on its own.
-- REFUTED: `Refuted.Subscribe-Caps-Nest` kills taking the exponent from
--   the STORE's cap alone, sixteen delivered against a charge of six at
--   `st-init`, where the node table is empty and so `capsOK? (caps 0 0
--   0)` holds outright and the factor collapses to one.  Each stacked
--   `mapᵉ` naming its payload twice doubles the delivered depth and
--   leaves the charge where it was -- eight, then sixteen -- so the gap
--   is unbounded rather than one crossing.  The same file pins
--   `valCaps?` FALSE at both programs, which is what makes the premise
--   load-bearing instead of merely present.
-- PROBED: `Probed.Subscribe-Nest` clears the restated form on exactly
--   the family that refuted every earlier one, at the SMALLEST cap the
--   `valCaps?` premise admits -- the value's own size and width, so
--   there is no slack in the choice -- with `B` taken to be `nestDᵉ o`
--   exactly.  What it measures rather than merely asserts is the
--   exponent SPENT: two of the three programs cross, needing one bit and
--   two, against the twenty-one to thirty-five the cap grants, and the
--   demand rises by ONE per stacked frame while the size it is read off
--   rises by SEVEN.  So the shape outruns the doubling with six of every
--   seven bits unspent.  Not covered: every subscription is at `root`
--   from an empty node table, so the queue-facing descent under a
--   `from-inner` is untouched -- rows do descend under that frame, from
--   tables holding nothing, a forty-deep queue, and a hundred-deep one
--   that DECIDES the `⊔` over what the descent emits.  That last is the
--   axis that could still have refuted, since the store is in the
--   premise and in the conclusion's left and in the right-hand side
--   nowhere; it does not, and the crossing moves by exactly the one bit
--   the larger store costs, which is the factor absorbing it linearly
--   rather than compounding.  What the rows also turn up: `stBounded?`
--   is what refuses a store deeper than the cap, so the axis is CAPPED
--   and not free.  Not covered: any cap above the value's own, except in
--   the one row whose store forces a wider one.
postulate
  subscribeE-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (sl : Slots Γ) (B : ℕ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → capsOK? c sched st ≡ true →
    valCaps? c sl (obs u) o ≡ true →
    nestDᵉ o ≤ B → nodesMax st ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl) →
    let r = subscribeE g o κ id now sched st in
    (nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ t} (proj₁ r))))
      ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl)

-- ONE SUBSCRIPTION, AND THE BOUND IS ABSOLUTE.  What the subscription
-- installs is read off `o`, whose depth the drain bounds by `B`, and off
-- the slots, which the unit covers -- so re-establishing the same bound
-- rather than one relative to the store handed in is exactly what stops
-- the factor compounding once per queued inner.  A relative form would
-- read `2 ^ cSize` times the PREVIOUS store and raise the drain's cost to
-- a tower in the queue's length, which is not what a queue of independent
-- inners costs.
subscribeInner-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (B : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → capsOK? c sched st ≡ true →
  valCaps? c sl (obs s) o ≡ true →
  nestDᵉ o ≤ B → nodesMax st ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl) →
  let r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ⊔ nestDᵛˢ (proj₁ (proj₂ r)))
    ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl)
subscribeInner-nest c sl B g0 allNid κ id now o sched st hsl hc hv hn hst =
  ⊔-lub hst z≤n
subscribeInner-nest c sl B (gs fuel) allNid κ id now o sched st hsl hc hv hn hst =
  subscribeE-nest c sl B fuel o
    (from-inner mergeAllᵒ allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st hsl
    (capsOK?-nextNode c (suc (Sched.nextNode sched)) sched st hc) hv hn hst

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
  (c : Caps) (sl : Slots Γ) (B : ℕ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  capsDrainOK c sl sf allNid κ id now lim act q sched st →
  queueNest q ≤ B → nodesMax st ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl) →
  let r = mergeAllDrain sf allNid κ id now lim act q sched st in
  ((nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ⊔ nestDᵛˢ (proj₁ r))
     ⊔ queueNest (proj₁ (proj₂ (proj₂ (proj₂ r)))))
    ≤ 2 ^ Caps.cSize c * (B + nestUnit e sl)
mergeAllDrain-nest {e = e} c sl B sf allNid κ id now lim act [] sched st hcd hq hst =
  ⊔-lub (⊔-lub hst z≤n) z≤n
mergeAllDrain-nest {e = e} c sl B sf allNid κ id now lim act (o ∷ q) sched st hcd hq hst
  with hasRoom lim act
... | false = ⊔-lub (⊔-lub hst z≤n) (≤-trans hq (raiseU (Caps.cSize c) B (nestUnit e sl)))
... | true  =
  ⊔-lub (⊔-lub (≤-trans (m≤m⊔n (nodesMax st₂) (nestDᵛˢ vs′))
                        (≤-trans (m≤m⊔n _ (queueNest q′)) IH))
               (≤-trans (nestDᵛˢ-++ vs vs′)
                        (⊔-lub (≤-trans (m≤n⊔m (nodesMax st₁) (nestDᵛˢ vs)) SUB)
                               (≤-trans (m≤n⊔m (nodesMax st₂) (nestDᵛˢ vs′))
                                        (≤-trans (m≤m⊔n _ (queueNest q′)) IH)))))
        (≤-trans (m≤n⊔m (nodesMax st₂ ⊔ nestDᵛˢ vs′) (queueNest q′)) IH)
  where
  r₁    = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  vs    = proj₁ (proj₂ r₁)
  done  = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

  r₂    = mergeAllDrain sf allNid κ id now lim (if done then act else suc act) q sched₁ st₁
  vs′   = proj₁ r₂
  q′    = proj₁ (proj₂ (proj₂ (proj₂ r₂)))
  st₂   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₂))))

  SUB = subscribeInner-nest c sl B sf allNid κ id now o sched st
          (proj₁ hcd) (proj₁ (proj₂ hcd)) (proj₁ (proj₂ (proj₂ hcd)))
          (≤-trans (m≤m⊔n (nestDᵉ o) (queueNest q)) hq) hst

  IH = mergeAllDrain-nest c sl B sf allNid κ id now lim
         (if done then act else suc act) q sched₁ st₁
         (proj₂ (proj₂ (proj₂ hcd)))
         (≤-trans (m≤n⊔m (nestDᵉ o) (queueNest q)) hq)
         (≤-trans (m≤m⊔n (nodesMax st₁) (nestDᵛˢ vs)) SUB)

-- THE FINISH DISPATCH, AND ALL OF IT IS CHECKED.  `innerReact` reaches
-- here along exactly one route -- a `fin` whose inner is not held open
-- by a live registration -- so the frame's whole charge is this
-- statement's; and of the finish's own arms, every one but the
-- `mergeAllᵒ` drain either hands its inputs straight back or writes a
-- node whose `nodeNest` is zero, so the drain is the sole leaf and the
-- rest reduces.
innerFinish-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (sf : Gas) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (id : Id) (now : Tick)
  (vals : List (Val Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → capsOK? c sched st ≡ true →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  let r = innerFinish sf op allNid inst p id now vals sched st
            (lookupNode allNid (EvalSt.nodes st)) in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ 2 ^ Caps.cSize c * ((nodesMax st ⊔ nestDᵛˢ vals) + nestUnit e sl)

innerFinish-nest {e = e} c sl sf switchᵒ allNid inst p id now vals sched st hsl hc hdr
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (scan-st _)           = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (take-st _)           = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (mergeAll-st _ _ _ _) = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (exhaust-st _ _)      = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (switch-st nothing _) = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (switch-st (just c₀) od) with c₀ ≡ᵇ inst
...   | false = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
...   | true  =
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (switch-st nothing od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl))

innerFinish-nest {e = e} c sl sf exhaustᵒ allNid inst p id now vals sched st hsl hc hdr
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (scan-st _)           = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (take-st _)           = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (mergeAll-st _ _ _ _) = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (switch-st _ _)       = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (exhaust-st _ od)     =
  ≤-trans (⊔-mono-≤ (setNode-nodes allNid (exhaust-st false od) (EvalSt.nodes st))
                    (≤-refl {nestDᵛˢ vals}))
          (raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl))

innerFinish-nest {e = e} {s = s} c sl sf mergeAllᵒ allNid inst p id now vals sched st hsl hc hdr
  with lookupNode allNid (EvalSt.nodes st) in eq
... | nothing                = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (scan-st _)       = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (take-st _)       = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (switch-st _ _)   = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (exhaust-st _ _)  = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
...   | yes refl =
  ⊔-lub (≤-trans (setNode-nodes allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′))
        (≤-trans (⊔-lub (m≤n⊔m (nodesMax st′ ⊔ nestDᵛˢ vs) (queueNest q′))
                        (≤-trans (m≤m⊔n (nodesMax st′) (nestDᵛˢ vs))
                                 (m≤m⊔n (nodesMax st′ ⊔ nestDᵛˢ vs) (queueNest q′))))
                 (≤-trans D up)))
        (≤-trans (nestDᵛˢ-++ vals vs)
                 (⊔-lub (≤-trans (m≤n⊔m (nodesMax st) (nestDᵛˢ vals))
                                 (raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals)
                                         (nestUnit e sl)))
                        (≤-trans (≤-trans (m≤n⊔m (nodesMax st′) (nestDᵛˢ vs))
                                          (m≤m⊔n (nodesMax st′ ⊔ nestDᵛˢ vs) (queueNest q′)))
                                 (≤-trans D up))))
  where
  r   = mergeAllDrain sf allNid p id now lim (pred act) q sched st
  vs   = proj₁ r
  act′ = proj₁ (proj₂ (proj₂ r))
  q′   = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st′  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))

  qbnd : queueNest q ≤ nodesMax st
  qbnd = lookupNode-nodes allNid (mergeAll-st lim act q od) (EvalSt.nodes st) eq

  D : ((nodesMax st′ ⊔ nestDᵛˢ vs) ⊔ queueNest q′)
        ≤ 2 ^ Caps.cSize c * (nodesMax st + nestUnit e sl)
  D = mergeAllDrain-nest c sl (nodesMax st) sf allNid p id now lim (pred act) q sched st
        (hdr lim act q od refl) qbnd
        (raiseU (Caps.cSize c) (nodesMax st) (nestUnit e sl))

  up : 2 ^ Caps.cSize c * (nodesMax st + nestUnit e sl)
         ≤ 2 ^ Caps.cSize c * ((nodesMax st ⊔ nestDᵛˢ vals) + nestUnit e sl)
  up = *-monoʳ-≤ (2 ^ Caps.cSize c)
         (+-monoˡ-≤ (nestUnit e sl) (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)))

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
  (c : Caps) (sl : Slots Γ) (sf : Gas) (id : Id) (now : Tick) (op : AllOp)
  (allNid : NodeId) (inst : NodeId) (p : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → capsOK? c sched st ≡ true →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c sl sf allNid p id now lim (pred act) q sched st) →
  let r = stepFrame sf id now (from-inner op allNid inst) p vals fin sched st in
  (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
    ≤ 2 ^ Caps.cSize c * ((nodesMax st ⊔ nestDᵛˢ vals) + nestUnit e sl)
stepFrame-nodes-inner {e = e} c sl sf id now op allNid inst p vals false sched st hsl hc hdr =
  raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
stepFrame-nodes-inner {e = e} c sl sf id now op allNid inst p vals true sched st hsl hc hdr
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = raiseU (Caps.cSize c) (nodesMax st ⊔ nestDᵛˢ vals) (nestUnit e sl)
... | false = innerFinish-nest c sl sf op allNid inst p id now vals sched st hsl hc hdr

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
    let r = stepFrame sf id now f p vals fin sched st in
    (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r))
      ≤ 2 ^ Caps.cSize c
        * (frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
           + nestUnit e sl)
  stepFrame-nodes {e = e} c W sl sf id now (map-f fn) p vals fin sched st hsl 1≤W hlen hc hv hfd =
    ≤-trans (⊔-lub (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _)) up)
          (≤-trans (mapVals-nest fn vals)
                   (*-mono-≤ (pow-grow¹ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn)) 1≤W)
                      (≤-trans (≤-reflexive (+-comm (nestDᵗ fn) (nestDᵛˢ vals)))
                               (+-mono-≤ (m≤n⊔m (nodesMax st) (nestDᵛˢ vals))
                                         (nest-inflate W (nestDᵗ fn) 1≤W))))))
            (raiseU (Caps.cSize c) _ (nestUnit e sl))
    where
    X : ℕ
    X = (nodesMax st ⊔ nestDᵛˢ vals) + W * nestDᵗ fn
    up : X ≤ (2 ^ sizeᵗ fn) ^ W * X
    up = ≤-trans (≤-reflexive (sym (*-identityˡ X)))
                 (*-monoˡ-≤ X (1≤pow≤ (2 ^ sizeᵗ fn) W (1≤frameNestF (map-f fn))))
  stepFrame-nodes {e = e} c W sl sf id now (scan-f fn nid) p vals fin sched st hsl 1≤W hlen hc hv hfd =
    ≤-trans (stepFrame-nodes-scan W sf id now fn nid p vals fin sched st hlen)
            (raiseU (Caps.cSize c) _ (nestUnit e sl))
  stepFrame-nodes {e = e} c W sl sf id now (take-f nid) p vals fin sched st hsl 1≤W hlen hc hv hfd =
    ≤-trans (≤-trans (stepFrame-nodes-take sf id now nid p vals fin sched st)
                     (zero-charge W _))
            (raiseU (Caps.cSize c) _ (nestUnit e sl))
  stepFrame-nodes {e = e} c W sl sf id now (from-inner op allNid inst) p vals fin sched st hsl 1≤W hlen hc hv hfd =
    ≤-trans (stepFrame-nodes-inner c sl sf id now op allNid inst p vals fin sched st hsl hc hfd)
            (*-monoʳ-≤ (2 ^ Caps.cSize c)
              (+-monoˡ-≤ (nestUnit e sl) (zero-charge W _)))
  stepFrame-nodes {e = e} c W sl sf id now (thru-outer op nid) p vals fin sched st hsl 1≤W hlen hc hv hfd =
    ≤-trans (stepFrame-nodes-thru c W sl sf id now op nid p vals fin sched st hsl 1≤W hlen hc hv)
            (≤-trans (*-monoʳ-≤ (2 ^ Caps.cSize c)
              (≤-trans (≤-reflexive (cong (_ +_) (sym (*-identityʳ W))))
                       (one-pow W (_ + W * 1))))
              (addU (Caps.cSize c) _ (nestUnit e sl)))

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
  × burstsOK W sf id now p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
  where step = stepFrame sf id now f p vals fin sched st

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
    ≤ (2 ^ Caps.cSize c) ^ pathLen path
      * (pathNestF path ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (pathNestD path + suc (pathLen path) * nestUnit e sl)))
foldPath-nodes c W sl sf gas id now envSrc root vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c W sl sf gas id now envSrc (share-sink i) vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (≤-trans (dispatchShare-nodes sl sf gas id now i vals fin sched st hsl)
                   (≤-trans (+-monoʳ-≤ (nodesMax st ⊔ nestDᵛˢ vals)
                              (≤-trans (nest-inflate W (nestUnit e sl) 1≤W)
                                       (*-monoʳ-≤ W (≤-reflexive
                                         (sym (*-identityˡ (nestUnit e sl)))))))
                            (one-pow W _)))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c W sl sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl 1≤W hb hc =
  ≤-trans (foldPath-nodes c W sl sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
             (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl)
             1≤W (proj₂ hb) (proj₂ (proj₂ (proj₂ hc))))
    (≤-trans (*-monoʳ-≤ ((2 ^ S) ^ pathLen p)
                (*-monoʳ-≤ (pathNestF p ^ W)
                  (+-monoˡ-≤ (W * (pathNestD p + L * U))
                             (stepFrame-nodes c W sl sf id now f p vals fin sched st
                                hsl 1≤W (proj₁ hb) (proj₁ hc) (proj₁ (proj₂ hc)) (proj₁ (proj₂ (proj₂ hc)))))))
    (≤-trans (*-monoʳ-≤ ((2 ^ S) ^ pathLen p)
                (fac-hoist (2 ^ S) (pathNestF p ^ W) (A + U) (W * (pathNestD p + L * U))
                           (1≤pow≤ 2 (Caps.cSize c) (s≤s z≤n))))
    (≤-trans (≤-reflexive (sym (*-assoc ((2 ^ S) ^ pathLen p) (2 ^ S) Inner)))
    (≤-trans (≤-reflexive (cong (_* Inner) (*-comm ((2 ^ S) ^ pathLen p) (2 ^ S))))
             (*-monoʳ-≤ ((2 ^ S) ^ suc (pathLen p))
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
  A      = frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
  Inner  = pathNestF p ^ W * ((A + nestUnit e sl)
                              + W * (pathNestD p + suc (pathLen p) * nestUnit e sl))
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestUnit e sl
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
