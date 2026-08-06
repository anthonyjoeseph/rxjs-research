------------------------------------------------------------------
-- SYMBOLIC ASSEMBLY for `depth-compositional`
-- (PROOF-STATE.md Task #13, Depth-Bound.agda:153-157)
--
-- LEDGER CLASS: LANDING: Verify-Budget-Sufficient/Depth-Compositional.agda
--
-- PURPOSE.  This file gives the PROOF SHAPE for `depth-compositional`
-- with every hard clause POSTULATED, so the assembly typechecks
-- symbolically before any clause is ground.  It is the outside-in
-- deliverable for the tier-1 attack on task #13.
--
-- CLAUSE CENSUS (all 16 subscribe-side heads):
--
-- BUCKET (a) — trivially zero, z≤n:
--   ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ), scripted slot, takeᵉ(zero)
--
-- BUCKET (b) — IH + arithmetic, no new mathematics:
--   mapᵉ   : depthBurst(map-f) = 0 (ARC-1 absent); IH + +-suc closes.
--   takeᵉ(suc k) : same shape with take-f frame (also 0 depth).
--   scanᵉ  : burst(scan-f) = 0; installNode(scan-st) raises
--             storeNestMax by sizeᵛ t (evalTm seed) ≤ sizeᵗ seed;
--             IH + +-suc closes.  Needs storeNestMax-installScan
--             sub-lemma.
--
-- BUCKET (d) — BLOCKED, three postulates:
--   depth-conn-storeNest : depthConn g i d κ ≤ storeNestMax.
--     Obstacle: applying main IH to d gives sizeᵉ d + storeNestMax
--     but we need just storeNestMax.  The IH double-counts because
--     slotNest(shared d) = sizeᵉ d is already IN storeNestMax.
--     Correct argument needs a TIGHTER secondary induction: either
--     depthConn ≤ slotNest(shared d) by gas induction, or a stronger
--     joint claim that bounds depthConn without the +storeNestMax term.
--   depth-all-bound : depthAll g op initSt b κ ≤ suc(sizeᵉ b) + pathLen κ + storeNestMax.
--     Obstacle: depthBurst's thru-outer frames each add suc; the
--     inner subscribes' depths involve emitted observable sizes and
--     the post-subscribe storeNestMax.  Requires the SECOND CONJUNCT
--     (storeNestMax preservation through subscribeE) proved
--     simultaneously — census finding (4) in Depth-Bound.agda:138-147.
--   depth-μ-bound : depthE fuel (unfoldμ body) κ ≤ sizeᵉ(μᵉ body) + pathLen κ + storeNestMax.
--     Obstacle: sizeᵉ(unfoldμ body) > sizeᵉ(μᵉ body) so direct IH
--     on size fails.  Correct argument: μ-variable occurrences in
--     body are all under deferᵉ (guarded-context discipline,
--     Rx.Exp:55-56, :78); deferᵉ b contributes 0 to depthE; so
--     unfoldμ body's depth equals body's depth modulo all recursive
--     references, which are structurally bounded by sizeᵉ body.
--
-- TERMINATION: depth-compositional is structurally recursive on `b`:
--   mapᵉ f b     → recursive call on b (strict subterm)
--   scanᵉ f sd b → recursive call on b (strict subterm)
--   takeᵉ c b    → recursive call on b (strict subterm)
-- All other cases dispatch to postulates (no recursion).
-- No {-# TERMINATING #-} needed.
------------------------------------------------------------------
module Depth-Compositional-Assembly where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; m≤n+m; +-mono-≤; ⊔-lub)
open import Data.Fin   using (Fin)
open import Data.Vec   using (lookup)
open import Data.List  using (List; []; _∷_)
open import Data.Bool  using (Bool; false; true)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp
  using (Ty; natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ;
         sizeᵉ; sizeᵗ; sizeᵛ;
         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
         mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
         μᵉ; varᵉ; deferᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream;
         Slot; scripted; shared;
         scan-st; merge-st; concat-st; switch-st; exhaust-st; take-st;
         mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
         root; share-sink; _↠_;
         map-f; scan-f; take-f; thru-outer;
         mintNode; installNode; subscribeE)

open import Verify-Budget-Sufficient.Depth-Bound
  using (storeNestMax)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthConn; depthAll; depthBurst)

-- Local pathLen — matches Measures.agda:5634-5637
pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink _) = 0
pathLen (_ ↠ p)        = suc (pathLen p)

------------------------------------------------------------------
-- BUCKET (d) — three hard postulates (schedule-blockers)
------------------------------------------------------------------

postulate
  -- depthConn (gs fuel') = depthE fuel' d (share-sink i).  Main IH
  -- gives sizeᵉ d + storeNestMax, but goal needs ≤ storeNestMax.
  -- Gap: sizeᵉ d ≤ slotsNestMax ≤ storeNestMax so the IH double-
  -- counts.  Requires a tighter gas-induction argument.
  depth-conn-storeNest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthConn g i d κ bid now sched st ≤ storeNestMax sched st

  -- depthAll's burst uses thru-outer (ARC 1 = spending arc).
  -- Bounding the inner subscribes requires storeNestMax preservation
  -- through subscribeE proved simultaneously (finding (4)).
  depth-all-bound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthAll g op initSt b κ bid now sched st
      ≤ suc (sizeᵉ b) + pathLen κ + storeNestMax sched st

  -- unfoldμ body has larger size than μᵉ body; direct IH on size fails.
  -- Correct argument: every μ-var occurrence in body is under deferᵉ,
  -- contributing 0 to depthE.
  -- NB: {r} is the outer path's tgt type (= {t} in depth-compositional);
  --     {u} is the μ's own recursive type.  These need not be equal.
  depth-μ-bound : ∀ {n} {Γ : Ctx n} {r u} {e : Closed Γ r}
    (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u r)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    depthE fuel (unfoldμ body) κ bid now sched st
      ≤ sizeᵉ (μᵉ body) + pathLen κ + storeNestMax sched st

------------------------------------------------------------------
-- BUCKET (b) — burst = 0 for non-thru-outer frames
-- (provable by structural induction on the stream list; each frame
-- clause in Caps-Depth:361-363 returns 0 definitionally)
------------------------------------------------------------------

postulate
  burst-mapf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (bid : Id) (now : Tick)
    (f : Fn Γ [] [] [] s u) (κ : Path Γ u t)
    (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    depthBurst fuel bid now (map-f f) κ stream sched st ≤ 0

  burst-scf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (bid : Id) (now : Tick)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
    (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    depthBurst fuel bid now (scan-f f nid) κ stream sched st ≤ 0

  burst-takef-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (bid : Id) (now : Tick)
    (nid : NodeId) (κ : Path Γ s t)
    (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    depthBurst fuel bid now (take-f nid) κ stream sched st ≤ 0

-- After mintNode + installNode(scan-st(evalTm seed)), storeNestMax
-- grows by at most sizeᵗ seed.  Proof: nodeNestMax(scan-st v) = sizeᵛ t v
-- ≤ sizeᵗ seed (by evalTm-sizeᵛ sub-lemma true for all Tm constructors);
-- mintNode only bumps nextNode, not slots.
postulate
  storeNestMax-installScan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sched : Sched Γ) (st : EvalSt e) (seed : Tm Γ [] [] [] u) →
    storeNestMax (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)
      ≤ storeNestMax sched st + sizeᵗ seed

-- After mintNode + installNode(take-st(suc k)), storeNestMax is
-- unchanged.  Proof: nodeNestMax(take-st _) = 0.
postulate
  storeNestMax-installTake : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
    storeNestMax (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
      ≤ storeNestMax sched st

------------------------------------------------------------------
-- ARITHMETIC HELPERS
-- Each is an immediate consequence of +-assoc/+-suc/m≤n+m.
-- Postulated to keep the main proof readable (BUCKET a).
------------------------------------------------------------------

postulate
  -- sizeᵉ b + suc(pathLen κ) + storeNestMax ≤ sizeᵉ(mapᵉ f b) + pathLen κ + storeNestMax
  -- Proof: sizeᵉ b + 1 ≤ 1 + sizeᵗ f + sizeᵉ b = sizeᵉ(mapᵉ f b)  (0 ≤ sizeᵗ f)
  map-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
      ≤ sizeᵉ (mapᵉ f b) + pathLen κ + storeNestMax sched st

  -- sizeᵉ b + suc(pathLen κ) + storeNestMax ≤ sizeᵉ(takeᵉ c b) + pathLen κ + storeNestMax
  -- Same shape as map-size-arith.
  take-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
      ≤ sizeᵉ (takeᵉ c b) + pathLen κ + storeNestMax sched st

  -- sizeᵉ b + suc(pathLen κ) + (storeNestMax + sizeᵗ seed)
  --   ≤ sizeᵉ(scanᵉ f seed b) + pathLen κ + storeNestMax
  -- Proof: sizeᵉ b + sizeᵗ seed ≤ sizeᵗ f + sizeᵗ seed + sizeᵉ b  (0 ≤ sizeᵗ f)
  scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + (storeNestMax sched st + sizeᵗ seed)
      ≤ sizeᵉ (scanᵉ f seed b) + pathLen κ + storeNestMax sched st

------------------------------------------------------------------
-- THE MAIN ASSEMBLY
-- Structurally recursive on `b`.  Dispatch order follows the clause
-- list in Caps-Depth.agda:214-251.
------------------------------------------------------------------

depth-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  depthE g b κ bid now sched st
    ≤ sizeᵉ b + pathLen κ + storeNestMax sched st

-- BUCKET (a): returns 0
depth-compositional g (ofᵉ _)    κ bid now sched st = z≤n
depth-compositional g emptyᵉ     κ bid now sched st = z≤n
depth-compositional g (deferᵉ _) κ bid now sched st = z≤n
depth-compositional g0 (μᵉ _)    κ bid now sched st = z≤n
depth-compositional g (varᵉ ())  κ bid now sched st

-- BUCKET (d): μ with gas — dispatched to depth-μ-bound
depth-compositional (gs fuel) (μᵉ body) κ bid now sched st =
  depth-μ-bound fuel body κ bid now sched st

-- BUCKET (d): input — slot dispatch, BLOCKED for shared case
depth-compositional g (input i) κ bid now sched st
  with Sched.slots sched i
... | scripted _ = z≤n
... | shared d   =
  -- depthConn ≤ storeNestMax  (by depth-conn-storeNest)
  -- storeNestMax ≤ 1 + pathLen κ + storeNestMax = sizeᵉ(input i) + pathLen κ + storeNestMax
  ≤-trans
    (depth-conn-storeNest g i d κ bid now sched st)
    (m≤n+m (storeNestMax sched st) (suc (pathLen κ)))

-- BUCKET (b): mapᵉ — burst(map-f) = 0 by frame clause; IH on b
depth-compositional fuel (mapᵉ f b) κ bid now sched st =
  ≤-trans
    (⊔-lub
      (depth-compositional fuel b (map-f f ↠ κ) bid now sched st)
      (≤-trans (burst-mapf-zero fuel bid now f κ
                  (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
               z≤n))
    (map-size-arith f b κ sched st)
  where r = subscribeE fuel b (map-f f ↠ κ) bid now sched st

-- BUCKET (a)/(b): takeᵉ — zero arm trivial; suc arm uses take-f burst = 0
depth-compositional fuel (takeᵉ c b) κ bid now sched st
  with evalTm c
... | zero  = z≤n
... | suc k =
  ≤-trans
    (⊔-lub
      (≤-trans
        (depth-compositional fuel b (take-f nid ↠ κ) bid now sched₁ st₀)
        (+-mono-≤ ≤-refl (storeNestMax-installTake sched st k)))
      (≤-trans (burst-takef-zero fuel bid now nid κ
                  (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
               z≤n))
    (take-size-arith c b κ sched st)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  r      = subscribeE fuel b (take-f nid ↠ κ) bid now sched₁ st₀

-- BUCKET (b): scanᵉ — burst(scan-f) = 0; storeNestMax grows by sizeᵗ seed
depth-compositional fuel (scanᵉ f seed b) κ bid now sched st =
  ≤-trans
    (⊔-lub
      (≤-trans
        (depth-compositional fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀)
        (+-mono-≤ ≤-refl (storeNestMax-installScan sched st seed)))
      (≤-trans (burst-scf-zero fuel bid now f nid κ
                  (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
               z≤n))
    (scan-size-arith f seed b κ sched st)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (scan-st (evalTm seed)) st
  r      = subscribeE fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀

-- BUCKET (d): *All — all four delegate to depth-all-bound
-- depth-all-bound gives suc(sizeᵉ b) + pathLen κ + storeNestMax
-- which definitionally equals sizeᵉ(*Allᵉ b) + pathLen κ + storeNestMax
depth-compositional fuel (mergeAllᵉ b) κ bid now sched st =
  depth-all-bound fuel mergeᵒ (merge-st 0 false) b κ bid now sched st

depth-compositional {u = u} fuel (concatAllᵉ b) κ bid now sched st =
  depth-all-bound fuel concatᵒ (concat-st {t = u} [] false false) b κ bid now sched st

depth-compositional fuel (switchAllᵉ b) κ bid now sched st =
  depth-all-bound fuel switchᵒ (switch-st nothing false) b κ bid now sched st

depth-compositional fuel (exhaustAllᵉ b) κ bid now sched st =
  depth-all-bound fuel exhaustᵒ (exhaust-st false false) b κ bid now sched st
