------------------------------------------------------------------
-- THE BUILDER: WHERE THE ARITHMETIC GOES ONCE THE MACHINE STOPS DOING
-- IT.
------------------------------------------------------------------

-- WHAT A BUILDER IS, AND WHY IT IS NOT THE TOTALITY PROOF NEXT DOOR.
-- That one builds a derivation at `subscribeE`'s OWN RESULT, so it has
-- to follow the machine into the test and answer the negative arm with
-- `⊥-elim` — an arm proven unreachable, writeable only where the fact
-- happens to be in hand.  Here the result is not fixed by a machine:
-- the builder RETURNS the pair, so it chooses which clause ran, and a
-- clause it does not write is a run that does not exist.  The `⊥-elim`
-- has nothing to eliminate because the `with` is gone.
--
-- SO THE EVALUATOR BECOMES A PROJECTION, AND THAT IS THE CUTOVER.
-- `evaluate` today is a recursion carrying `Acc _≺_ τ`; after, it is
-- `proj₁` of this, and every reading of a rank, every `<?`, every
-- `dryBurst` and the marker `dried` itself leave the evaluator
-- entirely.  `hasDry` then reads `false` of every run because no
-- constructor of the relation builds a dry emit — not because a number
-- came out large enough.
--
-- AND THE ORDER THIS FORCES IS THE ONE CONSTRAINT THE DEAD ROUTE IN
-- `Verify-Rank-Sufficient` NAMES.  A projection computes only if the
-- thing projected is a real body: leave any of the leaves below a
-- postulate and the bug cache, the oracle and every probe's `refl` get
-- stuck at the first match.  So the leaves land before `evaluate` is
-- re-pointed, and until then both machines exist side by side.
--
-- WHY IT SITS BELOW THE MACHINE RATHER THAN BESIDE THE PROOF THAT
-- CONSUMES IT.  Nothing here needs the recursion it replaces, and the
-- recursion does not compile — so a builder placed above it inherits a
-- cone the dev loop cannot warm and stops being iterable at exactly the
-- point where it is being written.  Below, the cone is `Rx.Evaluator`,
-- `Rx.Evaluator.Domain` and `Rx.Evaluator.Doorless`, all of which check
-- in seconds.
module Rx.Evaluator.Builder where

open import Data.Bool using (false)
open import Data.Fin using (Fin)
open import Data.List using ([]; _++_)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n)
open import Data.Product using (∃; _,_; proj₁)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Fuel; Id; Tick)
open import Rx.Exp using (Ctx; Closed; obs; unfoldμ; evalTm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeState; Frame; root; _↠_; map-f; take-f; scan-f;
  thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; take-st;
  scan-st; installNode; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  drain⇓; evaluate⇓; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all;
  subs-μ; subs-defer; sub-all; eval-run)
open import Rx.Evaluator.Doorless using (μ-edge; μ-entry; rootWitness;
  EntryOK; inner-ok; under-ok)

------------------------------------------------------------------
-- WHAT A BUILDER RETURNS.  The result and the derivation together, so
-- that "which clause ran" is an output rather than something the
-- builder has to agree with.
------------------------------------------------------------------

Runs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
     → Closed Γ u → Path Γ lo u t → Id → Tick → Sched Γ → EvalSt e → Set
Runs {e = e} b κ id now sched st =
  ∃ λ r → subscribeE⇓ {e = e} b κ id now sched st r

PushRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
         → Id → Tick → Frame Γ s u → Path Γ lo u t
         → Stream Γ s → Sched Γ → EvalSt e → Set
PushRuns {e = e} id now fr κ bs sched st =
  ∃ λ r → pushBurst⇓ {e = e} id now fr κ bs sched st r

AllRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
        → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ lo u t
        → Id → Tick → Sched Γ → EvalSt e → Set
AllRuns {e = e} op ns b κ id now sched st =
  ∃ λ r → subscribeAll⇓ {e = e} op ns b κ id now sched st r

------------------------------------------------------------------
-- THE LEAVES, WHICH ARE WHAT MAKE THE ASSEMBLY CHECKABLE TODAY.
------------------------------------------------------------------

-- THE FRAME WALK, STILL A LEAF, AND IT IS THE LARGEST OF THEM.  Every
-- clause of the machine that steps a burst through a frame lands under
-- this one name, the inner subscribe among them — which is why the hop
-- clause, the one place the deleted door used to ask its question, is
-- not written here yet: its only consumer is inside this leaf, and a
-- proof handed to a postulate as its only use earns no reachability and
-- checks nothing.  It comes back in the commit that turns this into a
-- body.
--
-- RECOVERY: `git show 0bfaccc:agda/src/Verify-Rank-Sufficient/Doorless.agda`
--   holds `subscribeInner!`, which is that hop clause written out — four
--   lines against the machine's, the `with obsDepthᵉ o <? r` and its dry
--   arm deleted and the descent witness taken from the report instead.
postulate
  pushBurst! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fr : Frame Γ s u)
    (κ : Path Γ lo u t) (bs : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
    PushRuns {e = e} id now fr κ bs sched st

-- AND THE TWO ENDS OF THE RUN.  An input's subscribe reads the slot
-- table and branches on what is registered there, and the drain spends
-- fuel over the schedule; neither is in the recursion this module is
-- for, so neither is written here.
postulate
  subscribeE!-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
    (ac : Acc _≺_ τ) (i : Fin n) → EntryOK {Γ = Γ} (input i) τ →
    (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    Runs {e = e} (input i) κ id now sched st

  drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    ∃ λ rest → drain⇓ {e = e} fuel id sched st rest

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE'S ENTRY, WITH THE μ PEEL'S TEST GONE.
------------------------------------------------------------------

-- EVERY OPERATOR CLAUSE DESCENDS ON THE TERM AND CARRIES THE SAME τ,
-- so the accessibility is passed through untouched and only the entry
-- invariant has to travel.  `inner-ok` and `under-ok` are that
-- travelling: the two measures read an operator as `suc (template +
-- source)` and `template ⊔ source` respectively, and what the source
-- needs is the right half of each.  The one clause that moves τ is the
-- μ peel below, and it is the only place a witness is spent.
subscribeE! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → Runs {e = e} b κ id now sched st

subscribeAll! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (op : AllOp) (ns : NodeState Γ) (b : Closed Γ (obs u)) →
  EntryOK b τ → (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  AllRuns {e = e} op ns b κ id now sched st

subscribeE! ac (input i) ok κ id now sched st =
  subscribeE!-input ac i ok κ id now sched st
subscribeE! ac (ofᵉ ts)  ok κ id now sched st = _ , subs-of refl
subscribeE! ac emptyᵉ    ok κ id now sched st = _ , subs-empty refl

subscribeE! ac (mapᵉ f b) ok κ id now sched st =
  let ((burst , sched₁ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (map-f f ↠ κ) id now sched st
      (r , p) = pushBurst! ac id now (map-f f) κ burst sched₁ st₁
  in r , subs-map d p

subscribeE! ac (takeᵉ c b) ok κ id now sched st
  with evalTm c in eq
... | zero  = _ , subs-take-zero eq refl
... | suc k =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (take-f nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid (take-st (suc k)) st)
      (r , p) = pushBurst! ac id now (take-f nid) κ burst sched₂ st₁
  in r , subs-take-suc eq refl d p

subscribeE! ac (scanᵉ f z b) ok κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b (inner-ok ok) (scan-f f nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid (scan-st (evalTm z)) st)
      (r , p) = pushBurst! ac id now (scan-f f nid) κ burst sched₂ st₁
  in r , subs-scan refl d p

subscribeE! ac (mergeAllᵉ lim b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac mergeAllᵒ (mergeAll-st lim 0 [] false)
                              b (under-ok ok) κ id now sched st
  in r , subs-merge-all a
subscribeE! ac (switchAllᵉ b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac switchᵒ (switch-st nothing false)
                              b (under-ok ok) κ id now sched st
  in r , subs-switch-all a
subscribeE! ac (exhaustAllᵉ b) ok κ id now sched st =
  let (r , a) = subscribeAll! ac exhaustᵒ (exhaust-st false false)
                              b (under-ok ok) κ id now sched st
  in r , subs-exhaust-all a

-- THE μ PEEL.  Against the machine the deletion is the whole clause's
-- `with`: `unfoldμ-shrinks` is a fact about the term and needs no
-- number handed in, so `μ-edge` is the descent outright.  The entry
-- invariant travels with it through `μ-entry`, which is the same
-- composition the old totality proof wrote under `⊥-elim`.
subscribeE! (acc rec) (μᵉ body) (sz≤ , r≤) κ id now sched st =
  let (r , d) = subscribeE! (rec (μ-edge body sz≤ r≤)) (unfoldμ body)
                            (≤-refl , μ-entry body r≤) κ id now sched st
  in r , subs-μ d

subscribeE! ac (varᵉ ()) ok κ id now sched st
subscribeE! ac (deferᵉ body) ok κ id now sched st = _ , subs-defer refl refl refl

-- THE FLATTENER'S OUTER SUBSCRIBE, WHICH HAS EXACTLY ONE CLAUSE.  All
-- three `*All` operators install their own node state and then run the
-- same outer subscribe through a `thru-outer` frame, so the operator is
-- carried as a value and the shape is shared.
subscribeAll! ac op ns b ok κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d) =
        subscribeE! ac b ok (thru-outer op nid ↠ κ) id now
                    (record sched { nextNode = suc nid })
                    (installNode nid ns st)
      (r , p) = pushBurst! ac id now (thru-outer op nid) κ burst sched₂ st₁
  in r , sub-all refl d p

------------------------------------------------------------------
-- THE TOP LINE, AND WHAT IT STOPS SAYING.
------------------------------------------------------------------

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, AND THE RELATION
-- SAYS SO IN ONE CONSTRUCTOR — so this is the assembly and the two
-- builders are its leaves.  The root's entry invariant is discharged by
-- `evaluate`'s own seeding, exactly as it is today.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
  (ins : Slots Γ) → ∃ λ out → evaluate⇓ fuel e ins out
evaluate! {n = n} fuel e ins =
  let ((burst , sched₀ , st₀) , s) =
        subscribeE! {lo = n} (rootWitness e ins) e (≤-refl , m≤m⊔n _ _)
                    root 0 0 (sched-init e ins) (st-init e)
      (rest , d) = drain! fuel 1 sched₀ st₀
  in (burst ++ rest) , eval-run s d

-- AND THE EVALUATOR AFTER THE CUTOVER.  Not a new machine — the SAME
-- machine with three clauses' worth of question removed, reached
-- through the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
