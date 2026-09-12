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
-- WHAT IS STILL OWED is the three FLATTENERS, and nothing else.  The
-- shelf used to be every clause that re-enters through a burst; four
-- of those never hop, so `Push-Dry` settles them outright and the
-- residue is exactly the clauses that reach `subscribeInner` — which
-- is where the rank peel is spent and so is the tier's reading rather
-- than this module's.  `opShape` is what keeps the leaf honest: it
-- answers for the flatteners alone, so no clause proven below can be
-- quietly supplied by it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Dry where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _^_)
open import Data.Nat.Properties using (_<?_; ≤-refl; ≤-trans; ≤-reflexive;
  m≤n+m; m≤n⇒m≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Id; hot; cold; init; close; exhausted)
open import Rx.Exp using (Ctx; Exp; Closed; evalTm; inputsBelowᵉ; sizeᵉ; syncSizeᵉ;
  unfoldμ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (shared; scripted; slotsSize)
open import Rx.Strat-Order using (_≺_; ltS; ltU)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE;
  subscribeSharedSlot; sharedConnect; register; share-sink; burstCompleted;
  mintSource; mintNode; installNode; take-st; scan-st; map-f; scan-f; take-f;
  _↠_;
  hasDry; memberSource; unconn; stNest)
open import Rx.Nest-Depth using (nestD-unfoldμ)
open import Verify-Rank-Sufficient.Entry using (EntryReads; seed-reads)
open import Verify-Rank-Sufficient.Sync-Edge using (mu-guard)
open import Verify-Rank-Sufficient.Connect-Edge using (connect-guard)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-if; oneShotBurst-dry;
  cold-tail-dry; connect-emit-dry)
open import Verify-Rank-Sufficient.Push-Dry using (pushBurst-dry;
  map-frame-dry; scan-frame-dry; take-frame-dry)

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
-- THE RANK CONJUNCT BOUGHT THE FLOOR AND NOT THE STATEMENT, and the
-- distance between those two is the whole of what is known here.
-- Carrying only the unconnected count and the syncSize, the leaf is
-- quantified over a triple whose rank is ZERO — and at rank zero the
-- inner-subscribe clause subscribes nothing at all: it returns the dry
-- close outright.  Bounding `nestDᵉ o` by the rank refuses that entry
-- for every shape `opShape` admits, since each carries at least the
-- layer its own inner is entered through.  What the bound does not do is
-- SCALE.  It reads the TERM; a term is charged for its step function
-- once; a fold applies that step once per delivery — so two deliveries
-- are already one more than the syntax knows about, and the leaf is
-- false at three conjuncts exactly as it was at two.

-- AND THIS LEAF HAS NEVER ONCE BEEN INSTANTIATED IN THE REGION THAT
-- CARRIES ITS RISK, which is a finding about the evidence rather than
-- about the statement, and it is why the receipts are gone rather than
-- retargeted.  Every row ever taken against it — ten of them, across
-- four probes — was rooted at a `takeᵉ` or a `scanᵉ`, and those are
-- precisely the shapes just proven: a root that cannot reach
-- `subscribeInner` cannot spend the rank, so no row of that shape could
-- have failed however deep the program under it ran.  Narrowing
-- `opShape` did not invalidate the coverage; it made visible that the
-- coverage was zero, since `refl : opShape (scanᵉ …) ≡ true` is now not
-- even stateable.  What is owed is a row at a flattening ROOT, and the
-- probes that reach one reach it only through the drain leaf.

-- SO THE REPAIR IS A CHANGE OF CURRENCY AND NOT A FOURTH CONJUNCT OF
-- THE SAME KIND.  No measure of syntax can serve, and that is settled
-- rather than suspected: the counterexample scales by lengthening the
-- run, which moves the deliveries and leaves the term fixed.  What has
-- to be carried down is that the rank still dominates what the run can
-- DELIVER.
--
-- AND THE DELIVERIES ARE NOT ALL BOUGHT WITH FUEL, WHICH IS WHAT RULES
-- OUT READING THE STATE HANDED IN.  A recursive source buys them with
-- fuel and a re-seed at each arrival would cover that; a LITERAL source
-- makes every one of them inside ONE cascade, so the store reads zero
-- at the entry the statement is made at and deepens only afterwards.  A
-- conjunct denominated in the state handed in is therefore dead for the
-- same reason a `suc` is: both are read before the growth they would
-- have to pay for.  The quantity that looked like it survived both was
-- the SYNCHRONOUS size — already the third component, already re-seeded
-- at the μ guard — and it does not: a burst's deliveries are exponential
-- in the source length where that measure is linear in it, so no
-- additive reading of the syntax bounds them.
--
-- A SIZE BOUND IS THE OBVIOUS CONJUNCT AND IT IS DEAD.
-- `2 ^ (sizeᵉ o + slotsSize sl) ≤ r` holds at the root by reflexivity and
-- cannot be re-established across the μ clause, since `unfoldμ body` is
-- LARGER in `sizeᵉ` than `μᵉ body` while the witness keeps the same rank.
-- What survives is a measure the unfolding leaves EQUAL, which is why the
-- conjunct is a nesting.  And the peel's own `≺`-witness is `ltR`
-- applied to its hypothesis and so says nothing — every gram of this
-- reading is establishing the hypothesis, which is the whole asymmetry
-- between this leaf and the two peels proven below.
--
-- AND THE BURST DOES NOT READ UNDER ITS EMITTER, SO THE HOP IS NOT PAID
-- IN SYNTAX AT ALL.  What a fold hands out is deeper than the term it
-- came from, and no measure of the emitter repairs that, because the
-- fold count is not in the term.
--
-- SO THE RESTATEMENT OWED HERE IS ABOUT THE WITNESS AND NOT THE
-- CONJUNCT.  The triples this leaf is entered at are CHOSEN to satisfy
-- the invariant rather than reached by a run, and `EntryReads` permits
-- that because it reads the term alone.  The walk's two settled peels
-- enjoy the opposite — they stand where the machine seeded them — which
-- is why they landed as one-line arms.  Pinning this leaf to the
-- witnesses the machine mints is what would put it in their position;
-- what it waits on is a bound on what a burst CARRIES, since that is the
-- quantity such a seeding would have to read, and it is a strengthened
-- return type on the burst-producing functions rather than a conjunct
-- anywhere.
--
-- REFUTED: `Refuted.Sync-Count` — the synchronous size as a bound on a
--   burst's deliveries, which is the reading the paragraphs above left
--   standing.  A doubling fold over a live seed delivers 2, 6, 14, 30 as
--   the source lengthens by one literal, against a measure that gains
--   one per literal: the first three rows HOLD the bound, so it is not
--   an off-by-one that a tighter constant repairs.
-- REFUTED: `Refuted.Burst-Nesting` — the inner-under-emitter reading, by
--   a scan over a three-element synchronous source whose step re-wraps
--   the accumulator in one merge layer: the program reads 1 and its
--   burst reads 3.  It kills the NON-STRICT comparison, so the strict
--   one the peel needs goes with it.
-- REFUTED: `Refuted.Rank-Entry` — the two-conjunct invariant, refuted by
--   the smallest merge over a synchronous one-element outer, entered at a
--   triple whose rank is zero with both of those conjuncts satisfied at
--   their tightest: the unconnected count is zero over the empty context
--   and the syncSize holds by reflexivity.  Its burst is one emit long
--   and that emit is the dry close.  Its reading is one against the
--   nesting, which is `suc 0` there.
-- REFUTED: `Refuted.Rank-Fold` — the THREE-conjunct form, which the row
--   above bought.  A scan whose step re-wraps its accumulator, under a
--   flattener that subscribes what it emits: the program reads two and
--   the triple is entered at THREE, so the conjunct holds with a peel to
--   spare and the crossing is not an off-by-one.  Three deliveries, all
--   of them inside one cascade off a literal source, so the store reads
--   zero where the statement is made; the third accumulator is entered
--   below the peels left and the burst carries the dry close.  It kills
--   a `suc` in the conjunct and a conjunct reading the state handed in,
--   together, and the state is reached by running rather than written.
-- RECOVERY: `git show 919f115:agda/src/Rx/Clos-Size.agda` restores
--   `syncSizeᵉ` with the slot telescope substituted in, also postulate-free
--   — the μ guard reads the UNSUBSTITUTED size, and a slot reference is one
--   symbol standing for a definition of any size, so this is where that gap
--   was already measured.
postulate
  dry-operator : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
    EntryReads τ o (Sched.slots sched) (EvalSt.connectedShares st) →
    hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

mutual
  subscribe-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    EntryReads τ o (Sched.slots sched) (EvalSt.connectedShares st) →
    hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

  -- THE μ PEEL.  The machine asks whether the unfolding fits under the
  -- component it is standing at; the invariant says the redex already
  -- did, and `mu-guard` is the strict drop that composes with it.  The
  -- recursive call re-seeds the component at the unfolding's own
  -- reading, so the invariant is restored by reflexivity.  The rank is
  -- untouched by the step, and `nestD-unfoldμ` is what says the nesting
  -- conjunct survives the substitution: the measure reads the redex and
  -- its unfolding EQUAL, so nothing is spent to re-establish it.
  subscribe-dry-free {τ = U , r , sz} (acc rec) (μᵉ body) κ id now sched st inv
    with syncSizeᵉ (unfoldμ body) <? sz
  ... | no  ¬p = ⊥-elim (¬p (mu-guard body (proj₂ (proj₂ inv))))
  ... | yes p  = subscribe-dry-free (rec (ltS p)) (unfoldμ body) κ id now sched st
                   ( proj₁ inv
                   , ≤-trans (≤-reflexive (nestD-unfoldμ body)) (proj₁ (proj₂ inv))
                   , ≤-refl )

  subscribe-dry-free ac (ofᵉ ts) κ id now sched st inv =
    oneShotBurst-dry (map (λ tm → evalTm tm) ts) id sched
  subscribe-dry-free {u = u} ac emptyᵉ κ id now sched st inv =
    oneShotBurst-dry {u = u} [] id sched
  subscribe-dry-free ac (varᵉ ()) κ id now sched st inv

  -- THE THREE NON-FLATTENING FRAMES, and a defer that subscribes
  -- nothing.  Each is `pushBurst` over a frame that cannot build a dry
  -- close — established once in `Push-Dry` — so the whole reading is
  -- the source's, transported through the measure clause the operator
  -- contributes.  The rank is never spent: none of these frames reaches
  -- `subscribeInner`, which is the only hop in the pipeline.
  subscribe-dry-free ac (mapᵉ f b) κ id now sched st inv =
    pushBurst-dry ac id now (map-f f) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (map-frame-dry ac id now f κ)
      (subscribe-dry-free ac b (map-f f ↠ κ) id now sched st
        ( proj₁ inv
        , ≤-trans (m≤n+m _ _) (proj₁ (proj₂ inv))
        , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) ))
    where
    r = subscribeE ac b (map-f f ↠ κ) id now sched st

  subscribe-dry-free {u = u} ac (takeᵉ c b) κ id now sched st inv with evalTm c
  ... | zero  = oneShotBurst-dry {u = u} [] id sched
  ... | suc k =
    pushBurst-dry ac id now (take-f nid) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (take-frame-dry ac id now nid κ)
      (subscribe-dry-free ac b (take-f nid ↠ κ) id now sched₁ st₁
        ( proj₁ inv
        , proj₁ (proj₂ inv)
        , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) ))
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (take-st (suc k)) st
    r      = subscribeE ac b (take-f nid ↠ κ) id now sched₁ st₁

  subscribe-dry-free ac (scanᵉ f z b) κ id now sched st inv =
    pushBurst-dry ac id now (scan-f f nid) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
      (scan-frame-dry ac id now f nid κ)
      (subscribe-dry-free ac b (scan-f f nid ↠ κ) id now sched₁ st₁
        ( proj₁ inv
        , ≤-trans (m≤n+m _ _) (proj₁ (proj₂ inv))
        , ≤-trans (m≤n⇒m≤1+n (m≤n+m _ _)) (proj₂ (proj₂ inv)) ))
    where
    nid    = proj₁ (mintNode sched)
    sched₁ = proj₂ (mintNode sched)
    st₁    = installNode nid (scan-st (evalTm z)) st
    r      = subscribeE ac b (scan-f f nid ↠ κ) id now sched₁ st₁

  -- a defer subscribes nothing at all: it mints the hop and announces
  -- it, so its burst is one `init` and there is nothing to read
  subscribe-dry-free ac (deferᵉ b) κ id now sched st inv = refl

  subscribe-dry-free ac (mergeAllᵉ lim b) κ id now sched st inv =
    dry-operator ac (mergeAllᵉ lim b) κ id now sched st refl inv
  subscribe-dry-free ac (switchAllᵉ b) κ id now sched st inv =
    dry-operator ac (switchAllᵉ b) κ id now sched st refl inv
  subscribe-dry-free ac (exhaustAllᵉ b) κ id now sched st inv =
    dry-operator ac (exhaustAllᵉ b) κ id now sched st refl inv

  -- A SLOT REFERENCE IS WHERE THE CONNECT PEEL LIVES, and three of its
  -- four outcomes announce and register without subscribing anything.
  subscribe-dry-free ac (input i) κ id now sched st inv
    with Sched.slots sched i in eqi
  ... | shared d {ok} = sharedSlot-dry ac i d κ id now sched st eqi (proj₁ inv)
  ... | scripted (cold sync [])       = oneShotBurst-dry sync id sched
  ... | scripted (cold sync (x ∷ xs)) =
        cold-tail-dry sync id (proj₁ (mintSource sched))
  ... | scripted (hot as)
        with memberSource (toℕ i) (EvalSt.completedSources st)
  ...   | true  = refl
  ...   | false = refl

  -- joining a live or a spent share announces and returns; only the
  -- first subscriber connects, and that is the guarded clause
  sharedSlot-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
    (ac : Acc _≺_ τ) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick) (sched : Sched Γ)
    (st : EvalSt e) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    unconn (Sched.slots sched) (EvalSt.connectedShares st) ≤ proj₁ τ →
    hasDry (proj₁ (subscribeSharedSlot ac i d κ id now sched st)) ≡ false
  sharedSlot-dry ac i d κ id now sched st eqi ule
    with memberSource (toℕ i) (EvalSt.completedSources st)
  ... | true = refl
  ... | false with memberSource (toℕ i) (EvalSt.connectedShares st) in fresh
  ...   | true  = refl
  ...   | false = sharedConnect-dry ac i d κ id now sched st eqi fresh ule

  -- THE CONNECT PEEL.  The machine asks whether latching this slot
  -- keeps the unconnected count under the component it entered at; the
  -- invariant says the count already was, and `connect-guard` is the
  -- strict drop a fresh latch buys.  The connected branch re-seeds all
  -- three components at the def's own reading — two by reflexivity, the
  -- rank through the size it is exponential in, exactly as the root
  -- seeding does, since a connect IS a second root.
  sharedConnect-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
    (ac : Acc _≺_ τ) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick) (sched : Sched Γ)
    (st : EvalSt e) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    Sched.slots sched i ≡ shared d {ok = ok} →
    memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
    unconn (Sched.slots sched) (EvalSt.connectedShares st) ≤ proj₁ τ →
    hasDry (proj₁ (sharedConnect ac i d κ id now sched st)) ≡ false
  sharedConnect-dry {Γ = Γ} {e = e} {τ = U , r , s}
                    (acc rec) i d κ id now sched st eqi fresh ule
    with unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st) <? U
  ... | no  ¬p = ⊥-elim (¬p (connect-guard (Sched.slots sched)
                              (EvalSt.connectedShares st) i eqi fresh ule))
  ... | yes p  =
    hasDry-if (burstCompleted burst) _ _
      (connect-emit-dry (init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
        id (toℕ i) burst refl hb)
      (connect-emit-dry (init (toℕ i) ∷ []) id (toℕ i) burst refl hb)
    where
    st₁ : EvalSt e
    st₁ = register (toℕ i) κ
            (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })

    burst : Stream Γ (lookup Γ i)
    seed : ℕ
    seed = 2 ^ (sizeᵉ d + slotsSize (Sched.slots sched) + stNest st₁)

    burst = proj₁ (subscribeE (rec (ltU {r′ = seed} {s′ = syncSizeᵉ d} p))
                     d (share-sink i) id now sched st₁)

    hb : hasDry burst ≡ false
    hb = subscribe-dry-free (rec (ltU {r′ = seed} {s′ = syncSizeᵉ d} p))
           d (share-sink i) id now sched st₁
           (≤-refl , seed-reads d (Sched.slots sched) (stNest st₁) , ≤-refl)
