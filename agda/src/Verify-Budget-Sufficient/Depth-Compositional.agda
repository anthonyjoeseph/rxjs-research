------------------------------------------------------------------
-- `depth-compositional`, ASSEMBLED — landed from
-- Depth-Compositional-Assembly (DELETED; git history) 2026-08-06, where the
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
-- BUCKETS: (a) trivially zero — ofᵉ, emptyᵉ, deferᵉ, g0(μᵉ),
-- takeᵉ(zero).  (b) IH + arithmetic — mapᵉ, takeᵉ(suc), scanᵉ,
-- over the burst-zero and installNode lemmas below.  (d) BLOCKED,
-- three named postulates — `depth-conn-input` (the main IH
-- double-counts `slotNest (shared d)`, needs a tighter gas induction;
-- its predecessor took the def as a free argument and was refuted for
-- it — Refuted.Depth-Conn, and the scripted slot moved into this leaf
-- with the repair),
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
  using (ℕ; zero; suc; _+_; _≤_; _⊔_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; m≤n+m; +-mono-≤; ⊔-lub;
         m≤m⊔n; m≤n⊔m; +-suc; ≤-reflexive)
open import Data.Fin   using (Fin)
open import Data.Vec   using (lookup)
open import Data.List  using (List; []; _∷_; foldr; tabulate)
open import Data.Nat.ListAction using (sum)
open import Data.Bool  using (false; true)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; InstEmit)
open import Rx.Exp
  using (natᵗ; _×ᵗ_; Ctx; Closed; Exp; Tm; Fn; Val; obs; evalTm; unfoldμ; sizeᵉ; sizeᵗ; sizeᵛ; input;
  ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ;
  deferᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; AllOp; NodeId; Path; Stream; scan-st; merge-st; concat-st;
  switch-st; exhaust-st; take-st; mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; _↠_; map-f; scan-f;
  take-f; mintNode; installNode; subscribeE; splitEvents; stepFrame; setNode)
open import Rx.Slots using (scripted; shared; Slot; Slots)

-- pathLen, imported from .Measures where it is defined — the
-- SAME pathLen `depth-capped`'s statement reads, so the landing plugs
-- into its consumer unchanged.
open import Verify-Budget-Sufficient.Measures using
  (pathLen)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst)

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

slotNest : ∀ {n} {Γ : Ctx n} {k t} → Slot Γ k t → ℕ
slotNest (shared d)   = sizeᵉ d
slotNest (scripted _) = 0

-- A SUM OVER THE SLOTS, AND THE `foldr _⊔_ 0` IT REPLACES WAS
-- REFUTED — Refuted.Depth-Chain, and the defect was the CURRENCY
-- rather than any statement written over it.  Slots are STRATIFIED, so
-- slot k's def may reference inputs strictly below k and the connects
-- CHAIN; each link is traversed by one `thru-outer` frame and the arcs
-- ADD.  A max over the slots does not grow with the chain at all, so
-- the two sides grew in different variables — the left in the chain
-- LENGTH, the right in one def's SIZE — and a chain longer than its
-- largest def crossed: nine links of size 5 over a base of size 7
-- measured depth 9 against a store of 7, and against the parent's own
-- right-hand side of 8.
--
-- A SUM IS THE RIGHT CURRENCY BECAUSE THE CHAIN CANNOT REVISIT.
-- Stratification makes the connect indices strictly decreasing, so
-- each slot is entered at most once along any path and `Σ slotNest`
-- pays for the whole chain; pointwise `slotNest ≤ slotSize` then keeps
-- it under the caps, which is what `slots-nest-≤-size` and
-- `storeNest-capped` do — and the sum form makes that proof SMALLER,
-- since it is sum monotonicity rather than max-of-tabulate ≤
-- sum-of-tabulate.
--
-- NOT A WEAKENING: the max was false, so this replaces a refuted
-- measure rather than retreating from a true one.  Every statement
-- written over `storeNestMax` keeps its text verbatim, which is why
-- the refutation cost no clause below it.
--
-- THE NODE HALF IS NOT COVERED BY THAT ARGUMENT and is unprobed:
-- `storeNestMax` still joins the two halves with `⊔`, because `+`
-- there would need `slotsSize + nodeCeil ≤ cSize` and the caps supply
-- each side separately.  Whether reads of parked observables chain the
-- way slot defs do wants a state the evaluator actually REACHED, so it
-- is a separate build.
slotsNestSum : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestSum {n} sl = sum (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestSum (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

------------------------------------------------------------------
-- BUCKET (d) — the three hard postulates (schedule-blockers)
------------------------------------------------------------------

postulate
  -- STATED AT `input i`, NOT AT THE DEF, and that is a repair rather
  -- than a convenience.  The predecessor took the def `d` as its own
  -- argument, quantified over every `Closed Γ (lookup Γ i)` there is
  -- with nothing tying it to `sched` — and REFUTED:
  -- Refuted.Depth-Conn.  THIS STATEMENT WAS THEN REFUTED TOO, over the
  -- max that `storeNestMax` used to be (Refuted.Depth-Chain), and
  -- repaired by changing the MEASURE rather than the statement: the
  -- text below is unchanged and the chain witness no longer reaches
  -- it, 9 against a sum of 47 where the max gave 7.
  -- The bound is believable only through
  -- `sizeᵉ d = slotNest (shared d) ≤ slotsNestMax (Sched.slots sched)`,
  -- which holds when `d` IS slot i's def and is a size the right-hand
  -- side has never heard of when it is not: at a program whose every
  -- slot is `scripted`, the store measures 0 while any `d` with one
  -- `thru-outer` arc connects at 1.  The caller reached the def by
  -- `with Sched.slots sched i` and so always had the missing fact,
  -- which is the classic shape — a statement admitting instances its
  -- caller cannot make.  Reading the slot INSIDE the statement is
  -- better than conditioning on a provenance equation: there is no free
  -- variable left to instantiate wrongly, the `scripted` branch comes
  -- along for free (`0 ≤ _`), and the caller loses its `with`.
  --
  -- WHAT SURVIVES THE REPAIR is the obstacle the predecessor's header
  -- described, unchanged.  depthConn (gs fuel') = depthE fuel' d
  -- (share-sink i), and pathLen (share-sink i) = 0 definitionally, so
  -- depth-compositional gives ≤ sizeᵉ d + 0 + storeNestMax sched st'
  -- = sizeᵉ d + storeNestMax sched st (register doesn't touch nodes).
  -- The goal is ≤ storeNestMax sched st, so the gap is exactly the
  -- sizeᵉ d that is now known to be ≤ the right-hand side — and
  -- natural-number arithmetic cannot absorb the double-count.  Needs a
  -- JOINT induction with depth-all-bound (both require storeNestMax
  -- preservation through subscribeE — census finding (4)).
  --
  -- AND A `⊔` IS THE WRONG INSTINCT — MEASURED, NOT ARGUED.  The
  -- earlier reading of the double-count was that the two currencies
  -- alternate rather than compose (a store read enters at
  -- `share-sink`, which resets the path), so
  -- `(sizeᵉ b + pathLen κ) ⊔ storeNestMax` would make this clause
  -- arithmetic.  That shape is refuted a fortiori by
  -- Refuted.Depth-Chain, which gives `1 ⊔ 7 = 7` against a depth of 9:
  -- a max cannot pay for a CHAIN of connects, and it was the max in
  -- `storeNestMax` itself that had to become a sum.  Recorded here
  -- because it was the plausible next move and it is dead.
  --
  -- WHAT THE SUM DOES *NOT* FIX IS THIS CLAUSE.  The double-count is
  -- untouched: the goal after `depth-compositional` is still
  -- `sizeᵉ d + storeNestMax ≤ storeNestMax`.  What the sum ADDS is that
  -- the right-hand side now SPLITS, so the shape to test is a sharper
  -- leaf bounded by the slots at or below `i` — strictly decreasing
  -- down the chain by stratification, with `sizeᵉ d` absorbed by the
  -- summand for `i` itself.  That is a JOINT restatement with
  -- `depth-compositional`, whose own right-hand side would have to
  -- carry the partial sum, so it is a design leg and a measurement
  -- before it is a route: nothing here is evidence that it closes.
  depth-conn-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n)
    (κ : Path Γ (lookup Γ i) t) (bid : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    depthE g (input i) κ bid now sched st ≤ storeNestMax sched st

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

-- depthFrame returns 0 definitionally for map-f/scan-f/take-f (Caps-Depth:361-363),
-- so depthBurst over these frames is a fold of (0 ⊔ IH) — provable by list induction.
burst-mapf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] s u) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (map-f f) κ stream sched st ≤ 0
burst-mapf-zero fuel bid now f κ [] sched st = z≤n
burst-mapf-zero {Γ = Γ} {u = u} fuel bid now f κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-mapf-zero fuel bid now f κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (map-f f) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

burst-scf-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (bid : Id) (now : Tick)
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (scan-f f nid) κ stream sched st ≤ 0
burst-scf-zero fuel bid now f nid κ [] sched st = z≤n
burst-scf-zero {Γ = Γ} {u = u} fuel bid now f nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-scf-zero fuel bid now f nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ u} (InstEmit.events em)
  r      = stepFrame fuel bid now (scan-f f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

burst-takef-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (take-f nid) κ stream sched st ≤ 0
burst-takef-zero fuel bid now nid κ [] sched st = z≤n
burst-takef-zero {Γ = Γ} {s = s} fuel bid now nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-takef-zero fuel bid now nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ s} (InstEmit.events em)
  r      = stepFrame fuel bid now (take-f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))

-- setNode with take-st never increases nodesNestMax: nodeNestMax(take-st _) = 0.
private
  setNode-take-nodesNestMax : ∀ {n} {Γ : Ctx n}
    (nid : NodeId) (k : ℕ)
    (nodes : List (NodeId × NodeState Γ)) →
    nodesNestMax (setNode nid (take-st k) nodes) ≤ nodesNestMax nodes
  setNode-take-nodesNestMax nid k [] = z≤n
  setNode-take-nodesNestMax nid k ((j , ns) ∷ rest) with j ≡ᵇ nid
  ... | true  = ⊔-lub z≤n (m≤n⊔m _ _)
  ... | false = ⊔-lub (m≤m⊔n _ _)
                      (≤-trans (setNode-take-nodesNestMax nid k rest) (m≤n⊔m _ _))

-- After mintNode + installNode(take-st(suc k)), storeNestMax is
-- unchanged: nodeNestMax(take-st _) = 0, and mintNode preserves slots.
storeNestMax-installTake : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (k : ℕ) →
  storeNestMax (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
    ≤ storeNestMax sched st
storeNestMax-installTake sched st k =
  ⊔-lub (m≤m⊔n _ _)
        (≤-trans (setNode-take-nodesNestMax (Sched.nextNode sched) (suc k)
                   (EvalSt.nodes st))
                 (m≤n⊔m _ _))

-- INSTALL-INVARIANCE for scan: installing a scan node does not increase
-- the subscribe-side depth beyond the ENTRY store bound.
--
-- depthFrame(scan-f fn nid) = 0 definitionally (Caps-Depth:362), so
-- the scan accumulator's value is never read during subscribe.  The IH
-- on b runs against (sched₁, installNode nid (scan-st v) st), but the
-- storeNestMax bound refers to the ENTRY (sched, st) — no size of v
-- appears on the RHS.
--
-- PROBED 2026-08-07: Install-Scan-Depth-Probe.agda §2 confirms
-- depthE = 0 at b=emptyᵉ with storeNestMax(post-install)=5 > 2=RHS,
-- ruling out any hidden dependence of depthE on the scan accumulator.
-- Shapes NOT covered: shared-slot inner b, post-cascade state.
-- AND THE FIGURE 5 WAS MEASURED UNDER THE OLD MAX.  `storeNestMax`'s
-- slot half is now a SUM (Refuted.Depth-Chain forced it), and the two
-- agree only when the probe's slots contributed 0 apiece — which that
-- probe's program is not recorded as having guaranteed, and the probe
-- is deleted.  The CONCLUSION it drew is unaffected either way: the 5
-- came from `nodeNestMax(scan-st v)`, the half that did not move, and
-- what the row ruled out was a dependence of `depthE` on the
-- accumulator.  It is the arithmetic of the number that is no longer
-- pinned.
-- NOTE: nodeNestMax(scan-st v) = sizeᵛ t v (NOT 0), so storeNestMax
-- increases when installing with a non-trivial value.  The proof cannot
-- go through depth-compositional at (sched₁, st₀) directly; it needs
-- an install-invariance argument showing depthE ignores the fresh node.
postulate
  installScan-depth-bound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (b : Closed Γ s)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u)
    (κ : Path Γ u t) (bid : Id) (now : Tick)
    (v : Val Γ u) (sched : Sched Γ) (st : EvalSt e) →
    depthE g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) bid now
               (proj₂ (mintNode sched))
               (installNode (proj₁ (mintNode sched)) (scan-st v) st)
      ≤ sizeᵉ b + suc (pathLen κ) + storeNestMax sched st

------------------------------------------------------------------
-- ARITHMETIC HELPERS — proved here.
------------------------------------------------------------------

-- Core step: a + suc p ≤ suc (c + a) + p.
-- Used by map-size-arith and take-size-arith.
private
  arith-step : ∀ (a p c : ℕ) → a + suc p ≤ suc (c + a) + p
  arith-step a p c =
    ≤-trans (≤-reflexive (+-suc a p))
            (s≤s (+-mono-≤ (m≤n+m a c) ≤-refl))

-- sizeᵉ b + 1 ≤ 1 + sizeᵗ f + sizeᵉ b = sizeᵉ (mapᵉ f b)
map-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
    ≤ sizeᵉ (mapᵉ f b) + pathLen κ + storeNestMax sched st
map-size-arith f b κ sched st =
  +-mono-≤ (arith-step (sizeᵉ b) (pathLen κ) (sizeᵗ f)) ≤-refl

-- same shape as map-size-arith
take-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
    ≤ sizeᵉ (takeᵉ c b) + pathLen κ + storeNestMax sched st
take-size-arith c b κ sched st =
  +-mono-≤ (arith-step (sizeᵉ b) (pathLen κ) (sizeᵗ c)) ≤-refl

-- scan: same shape as map-size-arith (no sizeᵗ seed on LHS)
-- because installScan-depth-bound routes the IH through the ENTRY
-- store (storeNestMax sched st), bypassing the installed scan value.
scan-size-arith : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u) (b : Closed Γ s)
  (κ : Path Γ u t) (sched : Sched Γ) (st : EvalSt e) →
  sizeᵉ b + suc (pathLen κ) + storeNestMax sched st
    ≤ sizeᵉ (scanᵉ f seed b) + pathLen κ + storeNestMax sched st
scan-size-arith f seed b κ sched st =
  +-mono-≤ (arith-step (sizeᵉ b) (pathLen κ) (sizeᵗ f + sizeᵗ seed)) ≤-refl

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

  -- BUCKET (d): input — BLOCKED.  No `with` on the slot: the leaf reads
  -- it, which is what stops a free def from being instantiated against a
  -- store that does not hold it (Refuted.Depth-Conn).
  depth-compositional-go g (input i) κ bid now sched st =
    ≤-trans
      (depth-conn-input g i κ bid now sched st)
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

  -- BUCKET (b): scanᵉ — burst(scan-f) = 0; IH routed through ENTRY store
  -- via installScan-depth-bound (install-invariance: depthE never reads
  -- the freshly-installed scan accumulator on the subscribe side).
  depth-compositional-go fuel (scanᵉ f seed b) κ bid now sched st =
    ≤-trans
      (⊔-lub
        (installScan-depth-bound fuel b f κ bid now (evalTm seed) sched st)
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