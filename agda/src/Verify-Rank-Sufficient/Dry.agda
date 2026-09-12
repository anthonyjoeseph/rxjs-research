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
-- WHAT IS STILL OWED is the operator shelf: every clause that holds
-- its witness fixed and re-enters through a burst.  Those are not
-- guard readings at all — nothing can go dry at a `mapᵉ` node itself
-- — so what they wait on is dry-freedom of the burst pipeline
-- (`pushBurst`, `subscribeAll`, and the rank peel inside
-- `subscribeInner`), which is a separate induction over a different
-- family.  `opShape` is what keeps the leaf honest: it cannot be
-- spent at `input`, at `μᵉ`, or at either one-shot source, so the
-- clauses that ARE proven cannot be quietly supplied by it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Dry where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (_≤_; _^_)
open import Data.Nat.Properties using (_<?_; ≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Id; hot; cold; init; close; exhausted)
open import Rx.Exp using (Ctx; Exp; Closed; evalTm; inputsBelowᵉ; sizeᵉ; syncSizeᵉ;
  unfoldμ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (shared; scripted)
open import Rx.Strat-Order using (_≺_; ltS; ltU)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE;
  subscribeSharedSlot; sharedConnect; register; share-sink; burstCompleted;
  mintSource;
  hasDry; memberSource; unconn)
open import Verify-Rank-Sufficient.Entry using (EntryReads)
open import Verify-Rank-Sufficient.Sync-Edge using (mu-guard)
open import Verify-Rank-Sufficient.Connect-Edge using (connect-guard)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-if; oneShotBurst-dry;
  cold-tail-dry; connect-emit-dry)

-- the shapes the operator leaf is allowed to answer for: everything the
-- walk re-enters through a burst.  A source and either settled peel are
-- excluded by construction, so the clauses proven below cannot be
-- supplied by the postulate instead.
opShape : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} → Exp Γ Δᵍ Δ Θ u → Bool
opShape (input _) = false
opShape (ofᵉ _)   = false
opShape emptyᵉ    = false
opShape (μᵉ _)    = false
opShape (varᵉ _)  = false
opShape _         = true

-- THE BURST PIPELINE'S OWN DRY-FREEDOM, which is where the rank peel is
-- spent and so is the tier's remaining reading rather than this module's.
-- An operator holds the witness FIXED and re-enters through a burst —
-- `pushBurst`, `subscribeAll`, and the rank peel inside `subscribeInner`
-- — so nothing goes dry at the node itself and the leaf is about the
-- pipeline underneath it.
--
-- THE STATEMENT IS SHORT BY A CONJUNCT AND IS FALSE AS IT STANDS.  The
-- entry invariant bounds the unconnected count and the syncSize and says
-- nothing whatever about the RANK, so this leaf is quantified over a
-- triple whose rank is ZERO — and at rank zero the inner-subscribe clause
-- subscribes nothing at all: it returns the dry close outright.  Nothing
-- about the top-line claim moves, since every run the evaluator performs
-- enters at `rootTri`, whose rank is `2 ^ (sizeᵉ e + slotsSize sl)` and is
-- never zero.  What is dead is DERIVING that claim from a lemma
-- universally quantified over the triple: the seeding is the only thing
-- holding the rank off the floor, and the invariant is where seeding facts
-- are supposed to travel.  So the row is SHAPE, the restatement is
-- guaranteed, and the third conjunct is a hypothesis that has been EARNED
-- below rather than a weakening.
--
-- AND THE CHEAP CONJUNCT DOES NOT SURVIVE THE WALK, WHICH IS WHY THE
-- REPAIR IS DESIGN WORK RATHER THAN A LINE.  `2 ^ (sizeᵉ o + slotsSize sl)
-- ≤ r` holds at the root by reflexivity and cannot be re-established
-- across the μ clause, since `unfoldμ body` is LARGER in `sizeᵉ` than
-- `μᵉ body` while the witness keeps the same rank.  The inner is a runtime
-- VALUE — an observable a sibling call emitted — structurally unrelated to
-- the term the caller was subscribing, so no equation on syntax reaches
-- it.  What does reach it is where it came FROM: it rode a burst some
-- subscribe produced, so its nesting can travel as a STRENGTHENED RETURN
-- TYPE on the burst-producing functions, invariant in the motive, rather
-- than as a fourth measure nobody has.  And the peel's own `≺`-witness is
-- `ltR` applied to its hypothesis and so says nothing — every gram of this
-- reading is establishing the hypothesis, which is the whole asymmetry
-- between this leaf and the two peels proven below.
--
-- AND THE SEED IS EXPONENTIAL IN PROGRAM SIZE, WHICH IS THE PART NO
-- RECOVERED APPARATUS HANDS OVER.  The machine seeds the rank at
-- `2 ^ (sizeᵉ e + slotsSize sl)`, re-seeds it at `2 ^ sizeᵉ d` on a
-- connect, and peels ONE per nesting hop, so the conclusion owed is that
-- the count is never spent — not a comparison.  The generation that
-- measured nesting before this one carried a hop DEPTH under its own cap,
-- a different currency answering a different question, so its rows are a
-- lead to read rather than a statement to cite.
--
-- REFUTED: `Refuted.Rank-Entry` — the smallest merge over a synchronous
--   one-element outer, entered at a triple whose rank is zero with both
--   conjuncts satisfied at their tightest: the unconnected count is zero
--   over the empty context and the syncSize holds by reflexivity.  Its
--   burst is one emit long and that emit is the dry close.
-- PROBED: `Probed.Descent` — three rows, each at an operator ROOT, which
--   is the only point this leaf can be instantiated at from outside: the
--   walk reaches it elsewhere only under a witness a probe cannot write
--   down.  They are a `takeᵉ` over plain recursion, over a recursion
--   reaching a share, and over a share HOLDING a recursion, so the frame
--   is walked with the connect peel live and with the nesting the rank
--   peel is about.  THE BOUNDARY, and it is the sharp one: a row here
--   covers the SUBSCRIBE FRAME and no drain at all, so an emitted inner
--   arriving on a later tick is outside every one of them — which is the
--   region the rank reading is actually about, and it is reached only
--   through the drain leaf's rows.
-- RECOVERY: `git show 919f115:agda/src/Rx/Layer-Count.agda` restores a
--   payload-blind layer count and a μ depth, BOTH POSTULATE-FREE, whose two
--   unfold equations are this reading's currency proven at the operation
--   the guard is about: the layer count is INVARIANT under `unfoldμ`, and
--   the μ depth drops exactly one.  A measure surviving the unfold is the
--   half of a nesting descent that is not bookkeeping.
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
  -- reading, so the invariant is restored by reflexivity.
  subscribe-dry-free {τ = U , r , sz} (acc rec) (μᵉ body) κ id now sched st inv
    with syncSizeᵉ (unfoldμ body) <? sz
  ... | no  ¬p = ⊥-elim (¬p (mu-guard body (proj₂ inv)))
  ... | yes p  = subscribe-dry-free (rec (ltS p)) (unfoldμ body) κ id now sched st
                   (proj₁ inv , ≤-refl)

  subscribe-dry-free ac (ofᵉ ts) κ id now sched st inv =
    oneShotBurst-dry (map (λ tm → evalTm tm) ts) id sched
  subscribe-dry-free {u = u} ac emptyᵉ κ id now sched st inv =
    oneShotBurst-dry {u = u} [] id sched
  subscribe-dry-free ac (varᵉ ()) κ id now sched st inv

  subscribe-dry-free ac (mapᵉ f b) κ id now sched st inv =
    dry-operator ac (mapᵉ f b) κ id now sched st refl inv
  subscribe-dry-free ac (takeᵉ c b) κ id now sched st inv =
    dry-operator ac (takeᵉ c b) κ id now sched st refl inv
  subscribe-dry-free ac (scanᵉ f z b) κ id now sched st inv =
    dry-operator ac (scanᵉ f z b) κ id now sched st refl inv
  subscribe-dry-free ac (mergeAllᵉ lim b) κ id now sched st inv =
    dry-operator ac (mergeAllᵉ lim b) κ id now sched st refl inv
  subscribe-dry-free ac (switchAllᵉ b) κ id now sched st inv =
    dry-operator ac (switchAllᵉ b) κ id now sched st refl inv
  subscribe-dry-free ac (exhaustAllᵉ b) κ id now sched st inv =
    dry-operator ac (exhaustAllᵉ b) κ id now sched st refl inv
  subscribe-dry-free ac (deferᵉ b) κ id now sched st inv =
    dry-operator ac (deferᵉ b) κ id now sched st refl inv

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
  -- three components at the def's own reading, so its invariant is
  -- reflexivity on both conjuncts.
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
    burst = proj₁ (subscribeE (rec (ltU {r′ = 2 ^ sizeᵉ d} {s′ = syncSizeᵉ d} p))
                     d (share-sink i) id now sched st₁)

    hb : hasDry burst ≡ false
    hb = subscribe-dry-free (rec (ltU {r′ = 2 ^ sizeᵉ d} {s′ = syncSizeᵉ d} p))
           d (share-sink i) id now sched st₁ (≤-refl , ≤-refl)
