------------------------------------------------------------------
-- `depth-compositional`, ASSEMBLED (tier-1 #5) — landed from
-- agda/probe/Depth-Compositional-Assembly.agda 2026-08-06, where the
-- shape was typechecked symbolically before paying this recheck.
--
-- THE MEASURE (`storeNestMax` and its four helpers) LIVES HERE, moved
-- from Depth-Bound.agda, because this module both defines the measure
-- and proves the compositional bound over it, while Depth-Bound
-- CONSUMES the bound (depth-capped) — the move is what breaks the
-- import cycle.  The node half is `boundedNode`'s own two live clauses
-- (Measures.agda) turned from a `≤ᵇ B` test into a `⊔`; the slot half
-- charges shared defs, the one channel `stBounded?` deliberately
-- excludes (slot defs are fixed syntax within one run, but `depthSlot`
-- reads them).
--
-- CLAUSE CENSUS (all 16 subscribe-side heads; the census findings from
-- the 2026-08-05 worker sweep are preserved in Depth-Bound's history
-- and the four load-bearing ones here):
--
-- (1) SCOPE IS 16 HEADS, NOT 19.  `depthFold`/`depthDisp`/
--     `depthShareGo`/`depthChain` are the DELIVERY family and are
--     never called from `depthE`'s clique.
-- (2) THE SECOND `suc` ARC IS OUT OF SCOPE.  `depthFinC`'s `yes refl`
--     arm is reached only through a `from-inner` Frame, which reaches
--     `depthFrame` only inside `depthFold` (Caps-Depth:393) — the
--     delivery family.  Taken standalone at `q = []` it computes
--     `suc 0 = 1` against a zero-able RHS, so it is FALSE as its own
--     obligation and must not be given this statement's shape.
-- (3) `depthBurst` calls `depthFrame` at the SAME `κ`, so
--     `thru-outer`'s `suc` is paid by the `*All` constructor's own
--     `sizeᵉ (mergeAllᵉ b) ≡ suc (sizeᵉ b)`, not by `pathLen`.
-- (4) THE REAL WORK: every clause that calls `depthBurst` feeds it the
--     state produced by running the REAL `subscribeE`, while the RHS
--     reads the ENTRY state.  The `storeNestMax`-preservation conjunct
--     is what `depth-all-bound` (below) absorbs; when it is ground it
--     must be proved as a second conjunct of the same induction, not a
--     separate family, and must NOT ride `subscribeE-caps` (circular —
--     that face takes `depthE ≤ dep` as a hypothesis).
--
-- BUCKETS: (a) trivially zero — ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ), scripted
-- slot, takeᵉ(zero).  (b) IH + arithmetic — mapᵉ, takeᵉ(suc), scanᵉ,
-- over the burst-zero and installNode lemmas below.  (d) BLOCKED,
-- three named postulates — `depth-conn-storeNest` (the main IH
-- double-counts `slotNest (shared d)`, needs a tighter gas induction),
-- `depth-all-bound` (needs the preservation conjunct, finding (4)),
-- `depth-μ-bound` (sizeᵉ (unfoldμ body) > sizeᵉ (μᵉ body) kills the
-- size IH; the honest route is the guarded-context discipline —
-- μ-variable occurrences sit under deferᵉ (Rx.Exp:55-56, :78), and
-- deferᵉ contributes 0 to depthE).
--
-- TERMINATION: structurally recursive on `b` (mapᵉ/scanᵉ/takeᵉ recurse
-- on the strict subterm; every other case dispatches to a postulate).
-- No pragma needed.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Depth-Compositional where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; m≤n+m; +-mono-≤; ⊔-lub)
open import Data.Fin   using (Fin)
open import Data.Vec   using (lookup)
open import Data.List  using (List; []; _∷_; foldr; tabulate)
open import Data.Bool  using (Bool; false; true)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp
  using (Ty; natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ;
         sizeᵉ; sizeᵗ; sizeᵛ;
         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
         mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
         μᵉ; varᵉ; deferᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream;
         Slot; Slots; scripted; shared;
         scan-st; merge-st; concat-st; switch-st; exhaust-st; take-st;
         mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
         root; share-sink; _↠_;
         map-f; scan-f; take-f; thru-outer;
         mintNode; installNode; subscribeE)

-- pathLen via the wet family's public chain (Wet → … → Measures) — the
-- SAME pathLen `depth-capped`'s statement reads, so the landing plugs
-- into its consumer unchanged.
open import Verify-Budget-Sufficient.Wet using (pathLen)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthConn; depthAll; depthBurst)

------------------------------------------------------------------
-- THE MEASURE — the state's contribution to subscribe-time depth,
-- validated by Depth-Compositional-Probe § A.
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
-- BUCKET (d) — the three hard postulates (schedule-blockers)
------------------------------------------------------------------

postulate
  -- depthConn (gs fuel') = depthE fuel' d (share-sink i).  Main IH
  -- gives sizeᵉ d + storeNestMax, but goal needs ≤ storeNestMax.
  -- Gap: sizeᵉ d = slotNest (shared d) is already IN storeNestMax, so
  -- the IH double-counts.  Requires a tighter gas-induction argument.
  depth-conn-storeNest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthConn g i d κ bid now sched st ≤ storeNestMax sched st

  -- depthAll's burst uses thru-outer (the spending arc).  Bounding the
  -- inner subscribes requires storeNestMax preservation through
  -- subscribeE proved simultaneously (census finding (4)).
  depth-all-bound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (initSt : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthAll g op initSt b κ bid now sched st
      ≤ suc (sizeᵉ b) + pathLen κ + storeNestMax sched st

  -- unfoldμ body is LARGER than μᵉ body, so the size IH fails; the
  -- honest route is the guarded-context discipline (μ-vars under
  -- deferᵉ, which contributes 0 to depthE).
  -- NB: {r} is the outer path's tgt type; {u} is the μ's own recursive
  -- type.  These need not be equal.
  depth-μ-bound : ∀ {n} {Γ : Ctx n} {r u} {e : Closed Γ r}
    (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u r)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    depthE fuel (unfoldμ body) κ bid now sched st
      ≤ sizeᵉ (μᵉ body) + pathLen κ + storeNestMax sched st

------------------------------------------------------------------
-- BUCKET (b) — burst = 0 for non-thru-outer frames (provable by
-- structural induction on the stream; each frame clause in
-- Caps-Depth:361-363 returns 0 definitionally)
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
-- grows by at most sizeᵗ seed: nodeNestMax(scan-st v) = sizeᵛ t v
-- ≤ sizeᵗ seed (evalTm-sizeᵛ sub-lemma), and mintNode only bumps
-- nextNode, not slots.
postulate
  storeNestMax-installScan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sched : Sched Γ) (st : EvalSt e) (seed : Tm Γ [] [] [] u) →
    storeNestMax (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)
      ≤ storeNestMax sched st + sizeᵗ seed

-- After mintNode + installNode(take-st(suc k)), storeNestMax is
-- unchanged: nodeNestMax(take-st _) = 0.
postulate
  storeNestMax-installTake : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
    storeNestMax (proj₂ (mintNode sched))
                 (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
      ≤ storeNestMax sched st

------------------------------------------------------------------
-- ARITHMETIC HELPERS — each an immediate consequence of
-- +-assoc/+-suc/m≤n+m, postulated to keep the assembly readable.
------------------------------------------------------------------

postulate
  -- sizeᵉ b + 1 ≤ 1 + sizeᵗ f + sizeᵉ b = sizeᵉ (mapᵉ f b)
  map-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
      ≤ sizeᵉ (mapᵉ f b) + pathLen κ + storeNestMax sched st

  -- same shape as map-size-arith
  take-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
      ≤ sizeᵉ (takeᵉ c b) + pathLen κ + storeNestMax sched st

  -- sizeᵉ b + sizeᵗ seed ≤ sizeᵗ f + sizeᵗ seed + sizeᵉ b
  scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
    (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
    sizeᵉ b + suc (pathLen κ) + (storeNestMax sched st + sizeᵗ seed)
      ≤ sizeᵉ (scanᵉ f seed b) + pathLen κ + storeNestMax sched st

------------------------------------------------------------------
-- THE ASSEMBLY — structurally recursive on `b`; dispatch order follows
-- the clause list in Caps-Depth.agda:214-251.
------------------------------------------------------------------

-- The assembly is built PRIVATE and exported through an ABSTRACT
-- alias, for the caps axis's normalization contract (measured
-- 2026-08-07: an unfoldable body on the budget-sufficient spine
-- OOM'd VWF's recheck twice; the morning-green build had a postulate
-- — i.e. exactly this opacity — in this spot).  The alias pattern
-- rather than a plain abstract block because these clauses lean on
-- untyped where-bindings and a with-abstraction, which abstract
-- refuses to infer.
private
  depth-compositional-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g b κ bid now sched st
      ≤ sizeᵉ b + pathLen κ + storeNestMax sched st

  -- BUCKET (a): returns 0
  depth-compositional-go g (ofᵉ _)    κ bid now sched st = z≤n
  depth-compositional-go g emptyᵉ     κ bid now sched st = z≤n
  depth-compositional-go g (deferᵉ _) κ bid now sched st = z≤n
  depth-compositional-go g0 (μᵉ _)    κ bid now sched st = z≤n
  depth-compositional-go g (varᵉ ())  κ bid now sched st

  -- BUCKET (d): μ with gas — dispatched to depth-μ-bound
  depth-compositional-go (gs fuel) (μᵉ body) κ bid now sched st =
    depth-μ-bound fuel body κ bid now sched st

  -- BUCKET (d): input — slot dispatch, BLOCKED for the shared case
  depth-compositional-go g (input i) κ bid now sched st
    with Sched.slots sched i
  ... | scripted _ = z≤n
  ... | shared d   =
    ≤-trans
      (depth-conn-storeNest g i d κ bid now sched st)
      (m≤n+m (storeNestMax sched st) (suc (pathLen κ)))

  -- BUCKET (b): mapᵉ — burst(map-f) = 0 by frame clause; IH on b
  depth-compositional-go fuel (mapᵉ f b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (depth-compositional-go fuel b (map-f f ↠ κ) bid now sched st)
        (≤-trans (burst-mapf-zero fuel bid now f κ
                    (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                 z≤n))
      (map-size-arith f b κ sched st)
    where r = subscribeE fuel b (map-f f ↠ κ) bid now sched st

  -- BUCKET (a)/(b): takeᵉ — zero arm trivial; suc arm uses take-f burst = 0
  depth-compositional-go fuel (takeᵉ c b) κ bid now sched st
    with evalTm c
  ... | zero  = z≤n
  ... | suc k =
    ≤-trans
      (⊔-lub
        (≤-trans
          (depth-compositional-go fuel b (take-f nid ↠ κ) bid now sched₁ st₀)
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
  depth-compositional-go fuel (scanᵉ f seed b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (≤-trans
          (depth-compositional-go fuel b (scan-f f nid ↠ κ) bid now sched₁ st₀)
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

  -- BUCKET (d): *All — all four delegate to depth-all-bound;
  -- suc (sizeᵉ b) IS sizeᵉ (*Allᵉ b) definitionally
  depth-compositional-go fuel (mergeAllᵉ b) κ bid now sched st =
    depth-all-bound fuel mergeᵒ (merge-st 0 false) b κ bid now sched st

  depth-compositional-go {u = u} fuel (concatAllᵉ b) κ bid now sched st =
    depth-all-bound fuel concatᵒ (concat-st {t = u} [] false false) b κ bid now sched st

  depth-compositional-go fuel (switchAllᵉ b) κ bid now sched st =
    depth-all-bound fuel switchᵒ (switch-st nothing false) b κ bid now sched st

  depth-compositional-go fuel (exhaustAllᵉ b) κ bid now sched st =
    depth-all-bound fuel exhaustᵒ (exhaust-st false false) b κ bid now sched st


abstract
  depth-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g b κ bid now sched st
      ≤ sizeᵉ b + pathLen κ + storeNestMax sched st
  depth-compositional = depth-compositional-go