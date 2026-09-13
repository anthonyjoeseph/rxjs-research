------------------------------------------------------------------
-- THE SUBSCRIPTION WALK NEVER GOES DRY, assembled clause by clause
-- against the entry invariant.
--
-- WHY THIS IS A REAL BODY AND NOT A POSTULATE: a guard that never
-- fails is a claim about a BRANCH THAT IS NEVER TAKEN, and the only
-- way to say that in Agda is to stand in the branch and derive a
-- contradiction.  So each settled peel appears here exactly once, as
-- the `no` arm of the machine's own decision, refuted out of the
-- invariant — which is what makes the edge lemmas load-bearing rather
-- than merely true.  A postulate over the whole walk would typecheck
-- and instantiate neither.
--
-- WHAT IS STILL OWED is the DRY half of the three FLATTENERS, and
-- nothing else.  Every clause of the walk now carries its report as a
-- real body — the flatteners included, whose arms stand on the walk's
-- own conclusion at the source plus one frame leaf — so what is left is
-- the single claim that the pipeline under a flattener builds no dry
-- close.  `opShape` is what keeps that leaf honest: it answers for the
-- flatteners alone, so no clause proven below can be quietly supplied
-- by it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Dry where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (_<?_; ≤-refl; ≤-trans; ≤-reflexive;
  ⊔-identityʳ; m≤n+m; m≤n⇒m≤1+n; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong)

open import Rx.Prim using (Tick; Id; hot; cold; init; close; exhausted)
open import Rx.Exp using (Ctx; Exp; Closed; evalTm; inputsBelowᵉ; syncSizeᵉ;
  unfoldμ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (shared; scripted)
open import Rx.Strat-Order using (_≺_; ltS; ltU)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE;
  subscribeSharedSlot; sharedConnect; register; share-sink; burstCompleted;
  mintSource; mintNode; installNode; take-st; scan-st; mergeAll-st;
  switch-st; exhaust-st;
  map-f; scan-f; take-f; thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ;
  _↠_;
  hasDry; memberSource; unconn; stHop)
open import Rx.Hop-Depth using (depthᵉ; hopOf; ε; rd-unfoldμ)
open import Rx.Slot-Read using (slotRd; slotRd-fix)
open import Verify-Rank-Sufficient.Entry using (EntryReads; hop-mapᵉ; hop-scanᵉ)
open import Verify-Rank-Sufficient.Sync-Edge using (mu-guard)
open import Verify-Rank-Sufficient.Connect-Edge using (connect-guard)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-if; oneShotBurst-dry;
  cold-tail-dry; connect-emit-dry)
open import Verify-Rank-Sufficient.Push-Dry using (pushBurst-dry;
  map-frame-dry; scan-frame-dry; take-frame-dry)
open import Verify-Rank-Sufficient.Carried using (emitHop-map;
  oneShotBurst-hop; installNode-hop; burstHop-plumb; valsHop-data;
  WalkCarries; burstHop-if; stHop-if)
open import Verify-Rank-Sufficient.Push-Carried using (pushBurst-carried;
  map-frame-carried; scan-frame-carried; take-frame-carried;
  thru-outer-frame-carried)
open import Verify-Rank-Sufficient.Leaf-Carried using (ofᵉ-carried;
  scan-seed-carried)

-- the shapes the operator leaf is allowed to answer for: the three
-- flatteners, and nothing else.  Everything the walk re-enters through
-- a burst used to be here; four of those shapes are proven below, so
-- admitting them would let the leaf supply a clause that is settled.
opShape : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} → Exp Γ Δᵍ Δ Θ u → Bool
opShape (mergeAllᵉ _ _)  = true
opShape (switchAllᵉ _)   = true
opShape (exhaustAllᵉ _)  = true
opShape _                = false

-- THE FLATTENERS' OWN DRY-FREEDOM, which is where the rank peel is spent
-- and so is the tier's remaining reading rather than this module's.  A
-- flattener holds the witness FIXED and re-enters through `subscribeAll`
-- and the rank peel inside `subscribeInner` — so nothing goes dry at the
-- node itself and the leaf is about the pipeline underneath it.
--
-- AND THE RESIDUE IS EXACTLY THE HOPPING CLAUSES, which is what makes
-- this leaf's region nameable at all.  Of the frames `stepFrame`
-- dispatches, `map-f` emits no events and reaches no subscribe, `scan-f`
-- returns `[]` on every arm, and `take-f`'s only closes are `cutThrough`'s
-- `cut` and `cutPending`; `deferᵉ` subscribes nothing, minting a hop and
-- announcing it.  `subscribeInner`, reached through `thru-outer` alone,
-- is the pipeline's ONLY rank drop — so the four shapes that cannot
-- reach it need no rank reading whatever, and they are proven below.
--
-- WHAT THE RANK CONJUNCT BUYS AND WHAT IS LEFT OVER.  Carrying only the
-- unconnected count and the syncSize, the leaf is quantified over a
-- triple whose rank is ZERO — and at rank zero the inner-subscribe
-- clause subscribes nothing at all: it returns the dry close outright.
-- Bounding the term's own hop reading by the rank refuses that entry for
-- every shape `opShape` admits, since each of the three reads `suc` of
-- its source.  So the zero case is closed, and what remains is the
-- clause's own peel.
--
-- AND WHY THIS HALF IS STILL A LEAF WHILE THE REPORT HALF IS A BODY.
-- The arms below assemble the flatteners' CARRIED report out of the
-- walk's own conclusion at the source plus one frame leaf, and the same
-- route is not available here: `FrameDry` is unconditional in the values
-- the frame is handed, and `thru-outer` at rank ZERO genuinely emits a
-- dry close, so no frame-level dry lemma about it can be true.  What
-- refuses that entry is the rank conjunct of the entry invariant, which
-- is a hypothesis about the frame's INPUTS — a quantity `FrameDry` has
-- nowhere to put.  So the assembly wanted here is not a fourth dry
-- frame lemma but a JOINT walk, the dry claim and the report proven in
-- one induction so the dry arm can spend the bound the report arm
-- carries.  That is a restatement of `pushBurst-dry`'s own shelf, not of
-- this statement, which is why the row stands unchanged.
--
-- DEAD ROUTE: a rank SEEDED off the term, which is what every earlier
--   form of this conjunct compared against — a power of two in the
--   term's syntactic size plus the slot telescope's, at the root and
--   again at each connect.  It is dead in two
--   independent ways, and the second is the one that cannot be patched:
--   a size seed cannot survive the μ clause at all, since an unfolding
--   is LARGER in that size than its redex while the witness keeps its
--   rank; and a seed grows with the SYNTAX while what has to be
--   dominated is what the run DELIVERS, which a fold multiplies once per
--   delivery.  Both are gone rather than repaired: the rank IS the hop
--   reading now, so the two sides are one quantity and there is nothing
--   left to bridge.
-- DEAD ROUTE: pricing the plug with a SLOPE — a coefficient times a
--   power of the store bound — which put the crossing between the door
--   and the first thing the loop does.  The marker landed in the
--   SUBSCRIBE burst, at no arrival and no drain step, so nothing carried
--   BETWEEN cascades could reach it: the carried depth climbed one per
--   source literal while the reading the frame entered at was flat in
--   source length.  The environment reading closed it by ITERATING over
--   the refold instead, and the same root entry now carries no dry
--   marker at any length measured — so what is dead is the slope, not
--   the leaf, and the strengthened return type it also killed is open
--   again (`Verify-Rank-Sufficient.Entry` carries that half).
-- REFUTED: `Refuted.Sync-Count` — the synchronous size as a bound on a
--   burst's deliveries.  A doubling fold over a live seed delivers 2, 6,
--   14, 30 as the source lengthens by one literal, against a measure
--   that gains one per literal: the first three rows HOLD the bound, so
--   it is not an off-by-one that a tighter constant repairs.
-- DEAD ROUTE: the inner-under-emitter comparison taken in NESTING,
--   killed by machine while `src` still had that measure — a scan over
--   a three-element synchronous source whose step re-wraps the
--   accumulator in one merge layer reads 1 at the program and 3 at its
--   burst.  The NON-STRICT comparison goes and the strict one the peel
--   needs goes with it, which is what says the surviving form has to be
--   read at a measure that tracks the REFOLD.  It is a dead route
--   rather than a standing refutation because the claim does not
--   survive the change of currency: the iterating clause charges that
--   scan for what it folds over, so the same witness comes back TRUE in
--   the hop reading and what it refuted was the nesting, which died
--   with it.
-- PROBED: `Probed.Operator-Root` — the only rows this leaf has at a root
--   it ANSWERS for, since every earlier one sat at a root `opShape`
--   refuses.  A run whose inner fold triples its deliveries per literal
--   and whose outer fold turns that width into depth, flattened at the
--   root so every layer is entered: the leaf comes back dry-free at one
--   literal, and across four source lengths the entry reading reads 5,
--   21, 85, 329 against carried depths of 3, 12, 39, 120.  It dominates
--   at every length and the margin WIDENS, which is the same family that
--   used to read a flat figure and cross at twelve literals.  THE
--   BOUNDARY, and it is an infrastructure limit: subscribing a burst
--   costs unlike measuring one, so the rate is instantiated at four
--   lengths and the SUBSCRIBE at one — a leaf row at two literals
--   stalled for eleven minutes with the resident set flat.
-- RECOVERY: `git show 919f115:agda/src/Rx/Clos-Size.agda` restores
--   `syncSizeᵉ` with the slot telescope substituted in, also postulate-free
--   — the μ guard reads the UNSUBSTITUTED size, and a slot reference is one
--   symbol standing for a definition of any size, so this is where that gap
--   was already measured.
postulate
  dry-operator : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
    EntryReads τ o
      (Sched.slots sched) (EvalSt.connectedShares st) →
    hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

mutual
  subscribe-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EntryReads τ o
      (Sched.slots sched) (EvalSt.connectedShares st) →
    stHop (slotRd (Sched.slots sched)) st ≤ proj₁ (proj₂ τ) →
    WalkCarries (slotRd (Sched.slots sched)) u
      (subscribeE ac o κ id now sched st)
      (depthᵉ (slotRd (Sched.slots sched)) o) (proj₁ (proj₂ τ))

  -- THE μ PEEL.  The machine asks whether the unfolding fits under the
  -- component it is standing at; the invariant says the redex already
  -- did, and `mu-guard` is the strict drop that composes with it.  The
  -- recursive call re-seeds the component at the unfolding's own
  -- reading, so the invariant is restored by reflexivity.  The rank is
  -- untouched by the step, and `rd-unfoldμ` is what says so: the whole
  -- reading of the redex and of its unfolding are EQUAL, so nothing is
  -- spent to re-establish that conjunct.  A measure that GREW here is
  -- what ruled out every seeded form.
  subscribe-dry-free {τ = U , r , sz} (acc rec) (μᵉ body) κ id now sched st
                     inv hst
    with syncSizeᵉ (unfoldμ body) <? sz
  ... | no  ¬p = ⊥-elim (¬p (mu-guard body (proj₂ (proj₂ inv))))
  ... | yes p  =
        proj₁ ih
        , ≤-trans (proj₁ (proj₂ ih))
                  (≤-reflexive (cong hopOf (rd-unfoldμ _ ε body)))
        , proj₂ (proj₂ ih)
    where
    ih = subscribe-dry-free (rec (ltS p)) (unfoldμ body) κ id now sched st
           ( proj₁ inv
           , ≤-trans (≤-reflexive (cong hopOf (rd-unfoldμ _ ε body)))
                     (proj₁ (proj₂ inv))
           , ≤-refl )
           hst

  subscribe-dry-free ac (ofᵉ ts) κ id now sched st inv hst =
    oneShotBurst-dry (map (λ tm → evalTm tm) ts) id sched
    , ≤-trans (≤-reflexive
                (oneShotBurst-hop _ _ (map (λ tm → evalTm tm) ts) id sched))
              (ofᵉ-carried _ ts)
    , hst
  subscribe-dry-free {u = u} ac emptyᵉ κ id now sched st inv hst =
    oneShotBurst-dry {u = u} [] id sched , z≤n , hst
  subscribe-dry-free ac (varᵉ ()) κ id now sched st inv hst

  -- THE THREE NON-FLATTENING FRAMES, and a defer that subscribes
  -- nothing.  Each is `pushBurst` over a frame that cannot build a dry
  -- close — established once in `Push-Dry` — so the whole reading is
  -- the source's, transported through the measure clause the operator
  -- contributes.  The rank is never spent: none of these frames reaches
  -- `subscribeInner`, which is the only hop in the pipeline.
  subscribe-dry-free {τ = τ} ac (mapᵉ f b) κ id now sched st inv hst =
    pushBurst-dry ac id now (map-f f) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (map-frame-dry ac id now f κ) (proj₁ ih)
    , proj₁ pc , proj₂ pc
    where
    ψ = slotRd (Sched.slots sched)
    r = subscribeE ac b (map-f f ↠ κ) id now sched st

    ih = subscribe-dry-free ac b (map-f f ↠ κ) id now sched st
           ( proj₁ inv
           , ≤-trans (hop-mapᵉ _ f b) (proj₁ (proj₂ inv))
           , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) )
           hst

    pc = pushBurst-carried ac id now (map-f f) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ (mapᵉ f b)) (depthᵉ ψ (mapᵉ f b)) (proj₁ (proj₂ τ))
           (map-frame-carried ac id now f κ ψ
             (depthᵉ ψ (mapᵉ f b)) (proj₁ (proj₂ τ)))
           (≤-trans (proj₁ (proj₂ ih)) (hop-mapᵉ ψ f b))
           (proj₂ (proj₂ ih))

  subscribe-dry-free {u = u} {τ = τ} ac (takeᵉ c b) κ id now sched st inv hst
    with evalTm c
  ... | zero  = oneShotBurst-dry {u = u} [] id sched , z≤n , hst
  ... | suc k =
    pushBurst-dry ac id now (take-f nid) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (take-frame-dry ac id now nid κ) (proj₁ ih)
    , proj₁ pc , proj₂ pc
    where
    ψ      = slotRd (Sched.slots sched)
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (take-st (suc k)) st
    r      = subscribeE ac b (take-f nid ↠ κ) id now sched₁ st₁

    -- a take node reads zero by construction, so the store bound is
    -- untouched by the install
    hst₁ = installNode-hop ψ nid (take-st (suc k)) st
             (proj₁ (proj₂ τ)) z≤n hst

    ih = subscribe-dry-free ac b (take-f nid ↠ κ) id now sched₁ st₁
           ( proj₁ inv
           , proj₁ (proj₂ inv)
           , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) )
           hst₁

    pc = pushBurst-carried ac id now (take-f nid) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ (takeᵉ c b)) (depthᵉ ψ (takeᵉ c b)) (proj₁ (proj₂ τ))
           (take-frame-carried ac id now nid κ ψ
             (depthᵉ ψ (takeᵉ c b)) (proj₁ (proj₂ τ)))
           (proj₁ (proj₂ ih))
           (proj₂ (proj₂ ih))

  subscribe-dry-free {τ = τ} ac (scanᵉ f z b) κ id now sched st inv hst =
    pushBurst-dry ac id now (scan-f f nid) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (scan-frame-dry ac id now f nid κ) (proj₁ ih)
    , proj₁ pc , proj₂ pc
    where
    ψ      = slotRd (Sched.slots sched)
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (scan-st (evalTm z)) st
    r      = subscribeE ac b (scan-f f nid ↠ κ) id now sched₁ st₁

    -- the seed is the one thing a subscribe writes that can read at
    -- all, and the entry invariant already puts the scan term under
    -- the rank
    hst₁ = installNode-hop ψ nid (scan-st (evalTm z)) st (proj₁ (proj₂ τ))
             (≤-trans (scan-seed-carried ψ f z b) (proj₁ (proj₂ inv))) hst

    ih = subscribe-dry-free ac b (scan-f f nid ↠ κ) id now sched₁ st₁
           ( proj₁ inv
           , ≤-trans (hop-scanᵉ _ f z b) (proj₁ (proj₂ inv))
           , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) )
           hst₁

    pc = pushBurst-carried ac id now (scan-f f nid) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ (scanᵉ f z b)) (depthᵉ ψ (scanᵉ f z b))
           (proj₁ (proj₂ τ))
           (scan-frame-carried ac id now f nid κ ψ
             (depthᵉ ψ (scanᵉ f z b)) (proj₁ (proj₂ τ))
             (proj₁ (proj₂ inv)))
           (≤-trans (proj₁ (proj₂ ih)) (hop-scanᵉ ψ f z b))
           (proj₂ (proj₂ ih))

  -- a defer subscribes nothing at all: it mints the hop and announces
  -- it, so its burst is one `init` and there is nothing to read; the
  -- node it installs holds an empty queue, which reads zero
  subscribe-dry-free {u = u} {τ = τ} ac (deferᵉ b) κ id now sched st inv hst =
    refl , z≤n
    , installNode-hop (slotRd (Sched.slots sched)) (proj₁ (mintNode sched))
        (mergeAll-st {t = u} nothing 0 [] false) st (proj₁ (proj₂ τ)) z≤n hst

  -- THE THREE FLATTENERS, and the report half is now an assembly.
  -- `subscribeAll` has the same shape as the three arms above — mint,
  -- install, subscribe the source under a frame, push the burst — so
  -- the walk's own conclusion at `b` supplies the burst bound and the
  -- residue is one FRAME leaf.  What separates them from the arms
  -- above is the currency the frame changes: the source delivers
  -- OBSERVABLES read at `depthᵉ ψ b`, and what the frame hands back is
  -- read one `suc` higher, which is exactly the flattener's own clause
  -- of the reading.  The entry invariant pays for that `suc`, and the
  -- `suc` is what the rank descent inside `subscribeInner` spends.
  subscribe-dry-free {u = u} {τ = τ} ac (mergeAllᵉ lim b) κ id now sched st
                     inv hst =
    dry-operator ac (mergeAllᵉ lim b) κ id now sched st refl inv
    , proj₁ pc , proj₂ pc
    where
    ψ      = slotRd (Sched.slots sched)
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (mergeAll-st {t = u} lim 0 [] false) st
    r      = subscribeE ac b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₁ st₁

    hst₁ = installNode-hop ψ nid (mergeAll-st {t = u} lim 0 [] false) st
             (proj₁ (proj₂ τ)) z≤n hst

    ih = subscribe-dry-free ac b (thru-outer mergeAllᵒ nid ↠ κ) id now
           sched₁ st₁
           ( proj₁ inv
           , ≤-trans (n≤1+n _) (proj₁ (proj₂ inv))
           , ≤-trans (n≤1+n _) (proj₂ (proj₂ inv)) )
           hst₁

    pc = pushBurst-carried ac id now (thru-outer mergeAllᵒ nid) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ b) (depthᵉ ψ (mergeAllᵉ lim b)) (proj₁ (proj₂ τ))
           (thru-outer-frame-carried ac id now mergeAllᵒ nid κ ψ
             (depthᵉ ψ b) (proj₁ (proj₂ τ)) (proj₁ (proj₂ inv)))
           (proj₁ (proj₂ ih))
           (proj₂ (proj₂ ih))

  subscribe-dry-free {τ = τ} ac (switchAllᵉ b) κ id now sched st inv hst =
    dry-operator ac (switchAllᵉ b) κ id now sched st refl inv
    , proj₁ pc , proj₂ pc
    where
    ψ      = slotRd (Sched.slots sched)
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (switch-st nothing false) st
    r      = subscribeE ac b (thru-outer switchᵒ nid ↠ κ) id now sched₁ st₁

    hst₁ = installNode-hop ψ nid (switch-st nothing false) st
             (proj₁ (proj₂ τ)) z≤n hst

    ih = subscribe-dry-free ac b (thru-outer switchᵒ nid ↠ κ) id now
           sched₁ st₁
           ( proj₁ inv
           , ≤-trans (n≤1+n _) (proj₁ (proj₂ inv))
           , ≤-trans (n≤1+n _) (proj₂ (proj₂ inv)) )
           hst₁

    pc = pushBurst-carried ac id now (thru-outer switchᵒ nid) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ b) (depthᵉ ψ (switchAllᵉ b)) (proj₁ (proj₂ τ))
           (thru-outer-frame-carried ac id now switchᵒ nid κ ψ
             (depthᵉ ψ b) (proj₁ (proj₂ τ)) (proj₁ (proj₂ inv)))
           (proj₁ (proj₂ ih))
           (proj₂ (proj₂ ih))

  subscribe-dry-free {τ = τ} ac (exhaustAllᵉ b) κ id now sched st inv hst =
    dry-operator ac (exhaustAllᵉ b) κ id now sched st refl inv
    , proj₁ pc , proj₂ pc
    where
    ψ      = slotRd (Sched.slots sched)
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (exhaust-st false false) st
    r      = subscribeE ac b (thru-outer exhaustᵒ nid ↠ κ) id now sched₁ st₁

    hst₁ = installNode-hop ψ nid (exhaust-st false false) st
             (proj₁ (proj₂ τ)) z≤n hst

    ih = subscribe-dry-free ac b (thru-outer exhaustᵒ nid ↠ κ) id now
           sched₁ st₁
           ( proj₁ inv
           , ≤-trans (n≤1+n _) (proj₁ (proj₂ inv))
           , ≤-trans (n≤1+n _) (proj₂ (proj₂ inv)) )
           hst₁

    pc = pushBurst-carried ac id now (thru-outer exhaustᵒ nid) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ψ (depthᵉ ψ b) (depthᵉ ψ (exhaustAllᵉ b)) (proj₁ (proj₂ τ))
           (thru-outer-frame-carried ac id now exhaustᵒ nid κ ψ
             (depthᵉ ψ b) (proj₁ (proj₂ τ)) (proj₁ (proj₂ inv)))
           (proj₁ (proj₂ ih))
           (proj₂ (proj₂ ih))

  -- A SLOT REFERENCE IS WHERE THE CONNECT PEEL LIVES, and three of its
  -- four outcomes announce and register without subscribing anything.
  subscribe-dry-free ac (input i) κ id now sched st inv hst
    with Sched.slots sched i in eqi
  -- the reference and the definition it stands for read the same, so
  -- the bound crosses the slot boundary in both directions
  ... | shared d {ok} =
        proj₁ w
        , ≤-trans (proj₁ (proj₂ w))
                  (≤-reflexive (sym (cong hopOf
                    (slotRd-fix (Sched.slots sched) i d ok))))
        , proj₂ (proj₂ w)
        where
        w = sharedSlot-dry ac i d κ id now sched st eqi (proj₁ inv)
              (≤-trans (≤-reflexive
                         (sym (cong hopOf
                           (slotRd-fix (Sched.slots sched) i d ok))))
                       (proj₁ (proj₂ inv)))
              hst
  ... | scripted {ok = ok} (cold sync [])       =
        oneShotBurst-dry sync id sched
        , ≤-trans (≤-reflexive
                    (trans (oneShotBurst-hop _ _ sync id sched)
                           (valsHop-data _ _ sync ok)))
                  z≤n
        , hst
  ... | scripted {ok = ok} (cold sync (x ∷ xs)) =
        cold-tail-dry sync id (proj₁ (mintSource sched))
        , ≤-trans (≤-reflexive
                    (trans (trans (⊔-identityʳ _) (emitHop-map _ _ sync))
                           (valsHop-data _ _ sync ok)))
                  z≤n
        , hst
  ... | scripted (hot as)
        with memberSource (toℕ i) (EvalSt.completedSources st)
  ...   | true  = refl , z≤n , hst
  ...   | false = refl , z≤n , hst

  -- joining a live or a spent share announces and returns; only the
  -- first subscriber connects, and that is the guarded clause
  sharedSlot-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
    (ac : Acc _≺_ τ) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick) (sched : Sched Γ)
    (st : EvalSt e) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    unconn (Sched.slots sched) (EvalSt.connectedShares st) ≤ proj₁ τ →
    depthᵉ (slotRd (Sched.slots sched)) d ≤ proj₁ (proj₂ τ) →
    stHop (slotRd (Sched.slots sched)) st ≤ proj₁ (proj₂ τ) →
    WalkCarries (slotRd (Sched.slots sched)) (lookup Γ i)
      (subscribeSharedSlot ac i d κ id now sched st)
      (depthᵉ (slotRd (Sched.slots sched)) d) (proj₁ (proj₂ τ))
  sharedSlot-dry ac i d κ id now sched st eqi ule hle hst
    with memberSource (toℕ i) (EvalSt.completedSources st)
  ... | true = refl , z≤n , hst
  ... | false with memberSource (toℕ i) (EvalSt.connectedShares st) in fresh
  ...   | true  = refl , z≤n , hst
  ...   | false =
          sharedConnect-dry ac i d κ id now sched st eqi fresh ule hle hst

  -- THE CONNECT PEEL.  The machine asks whether latching this slot
  -- keeps the unconnected count under the component it entered at; the
  -- invariant says the count already was, and `connect-guard` is the
  -- strict drop a fresh latch buys.  The count is the OUTERMOST
  -- component, so the step is `ltU` and the other two ride along free:
  -- the connected branch re-enters at the same rank and the same sync,
  -- and what it has to show is that the DEF reads under them.  Sync is
  -- reflexivity, and the rank arrives as a premise — transferred from
  -- the reference to the definition it stands for at the slot clause
  -- above, which is the one place the telescope has been matched.
  sharedConnect-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
    (ac : Acc _≺_ τ) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick) (sched : Sched Γ)
    (st : EvalSt e) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
    unconn (Sched.slots sched) (EvalSt.connectedShares st) ≤ proj₁ τ →
    depthᵉ (slotRd (Sched.slots sched)) d ≤ proj₁ (proj₂ τ) →
    stHop (slotRd (Sched.slots sched)) st ≤ proj₁ (proj₂ τ) →
    WalkCarries (slotRd (Sched.slots sched)) (lookup Γ i)
      (sharedConnect ac i d κ id now sched st)
      (depthᵉ (slotRd (Sched.slots sched)) d) (proj₁ (proj₂ τ))
  sharedConnect-dry {Γ = Γ} {e = e} {τ = U , r , s}
                    (acc rec) i d κ id now sched st eqi fresh ule hle hst
    with unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st) <? U
  ... | no  ¬p = ⊥-elim (¬p (connect-guard (Sched.slots sched)
                              (EvalSt.connectedShares st) i eqi fresh ule))
  ... | yes p  =
    hasDry-if (burstCompleted burst) _ _
      (connect-emit-dry (init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
        id (toℕ i) burst refl hb)
      (connect-emit-dry (init (toℕ i) ∷ []) id (toℕ i) burst refl hb)
    , burstHop-if ψ (burstCompleted burst) _ _ (depthᵉ ψ d) bh bh
    , stHop-if ψ (burstCompleted burst) _ _ r
        (proj₂ (proj₂ w)) (proj₂ (proj₂ w))
    where
    ψ = slotRd (Sched.slots sched)

    st₁ : EvalSt e
    st₁ = register (toℕ i) κ
            (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })

    burst : Stream Γ (lookup Γ i)
    burst = proj₁ (subscribeE (rec (ltU {r′ = r} {s′ = syncSizeᵉ d} p))
                     d (share-sink i) id now sched st₁)

    -- neither the latch nor the registration touches a node, so the
    -- store bound the caller came in with is the one the definition is
    -- subscribed under
    w = subscribe-dry-free (rec (ltU {r′ = r} {s′ = syncSizeᵉ d} p))
          d (share-sink i) id now sched st₁
          (≤-refl , hle , ≤-refl) hst

    hb : hasDry burst ≡ false
    hb = proj₁ w

    -- plumbing retags and nothing else, and the bookkeeping emit in
    -- front of it carries no value at all
    bh = ≤-trans (≤-reflexive (burstHop-plumb ψ (lookup Γ i) burst))
                 (proj₁ (proj₂ w))
