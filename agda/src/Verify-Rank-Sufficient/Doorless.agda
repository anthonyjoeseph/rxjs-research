------------------------------------------------------------------
-- THE BUILDER: WHERE THE ARITHMETIC GOES ONCE THE MACHINE STOPS DOING
-- IT.  A sketch — nothing here typechecks and nothing imports it; it is
-- deleted by the commit that makes the change.
------------------------------------------------------------------

-- THE TOTALITY PROOF NEXT DOOR ALREADY HAS THIS SHAPE AND ONE THING
-- WRONG WITH IT: it builds a derivation at `subscribeE`'s OWN RESULT,
-- so it has to follow the machine into the test and answer the negative
-- arm with `⊥-elim`.  That is meaning ONE of killing the door — the arm
-- proven unreachable — and it is only writeable where the fact happens
-- to be in hand.  Here the result is not fixed by the machine: the
-- builder RETURNS the pair, so it chooses which clause ran, and a
-- clause it does not write is a run that does not exist.  The `⊥-elim`
-- has nothing to eliminate because the `with` is gone.
--
-- SO THE EVALUATOR BECOMES A PROJECTION, AND THAT IS THE CUTOVER.
-- `evaluate` today is a recursion carrying `Acc _≺_ τ`; after, it is
-- `proj₁` of this, and every reading of a rank, every `<?`, every
-- `dryBurst` and the marker `dried` itself leave `Rx.Evaluator`
-- entirely.  `hasDry` then reads `false` of every run because no
-- constructor of the relation builds a dry emit — not because a
-- number came out large enough.
--
-- AND THE ORDER THIS FORCES IS THE ONE CONSTRAINT THE DEAD ROUTE IN
-- `Verify-Rank-Sufficient` NAMES.  A projection computes only if the
-- thing projected is a real body: leave any of the leaves below a
-- postulate and the bug cache, the oracle and every probe's `refl` get
-- stuck at the first match.  So the leaves land before `evaluate` is
-- re-pointed, and until then both machines exist side by side.
module Verify-Rank-Sufficient.Doorless where

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Fuel; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; obs; unfoldμ; input; ofᵉ; emptyᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; NodeId; AllOp; root; from-inner; _↠_; splitBurst; sched-init;
  st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; drain⇓; evaluate⇓; subs-of; subs-empty; subs-μ; subs-defer;
  inner; eval-run)
open import Rx.Evaluator.Doorless using (μ-edge; μ-entry; hop-edge; rootWitness)
open import Verify-Rank-Sufficient using (EntryOK; HandedOK; hop-guard)

------------------------------------------------------------------
-- WHAT A BUILDER RETURNS.  The result and the derivation together, so
-- that "which clause ran" is an output rather than something the
-- builder has to agree with.
------------------------------------------------------------------

Runs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
     → Closed Γ u → Path Γ lo u t → Id → Tick → Sched Γ → EvalSt e → Set
Runs {e = e} b κ id now sched st =
  Σ[ r ∈ _ ] subscribeE⇓ {e = e} b κ id now sched st r

InnerRuns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
          → AllOp → NodeId → Path Γ lo u t → Id → Tick
          → Val Γ (obs u) → Sched Γ → EvalSt e → Set
InnerRuns {e = e} op allNid κ id now o sched st =
  Σ[ r ∈ _ ] subscribeInner⇓ {e = e} op allNid κ id now o sched st r

------------------------------------------------------------------
-- THE HOP, WITH NO TEST IN IT.
------------------------------------------------------------------

-- THE CLAUSE THE WHOLE TIER IS ABOUT, AND IT IS FOUR LINES.  Against
-- the machine's `subscribeInner` the diff is three deletions and one
-- substitution: the `with obsDepthᵉ o <? r` goes, the `no` arm and its
-- `close drySource dried ∷ []` go, and the descent witness — which the
-- `yes` branch used to take from the test's own proof — comes from the
-- REPORT instead.  The report is an argument to the builder and is not
-- an argument to the machine, which is the line this repo does not
-- cross: a proof may be proof-carrying, an evaluator may not.
subscribeInner! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (op : AllOp) (allNid : NodeId) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u)) → HandedOK (o ∷ []) τ →
  (sched : Sched Γ) (st : EvalSt e) →
  InnerRuns {e = e} op allNid κ id now o sched st
subscribeInner! (acc rec) op allNid κ id now o hk sched st =
  let inst = Sched.nextNode sched
      ((burst , sched′ , st′) , d) =
        subscribeE! (rec (hop-edge o (hop-guard o hk))) o (≤-refl , ≤-refl)
                    (from-inner op allNid inst ↠ κ) id now
                    (record sched { nextNode = suc inst }) st
      (vs , bs , done) = splitBurst burst
  in (inst , vs , bs , done , sched′ , st′)
   , inner refl d refl

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE'S ENTRY, WITH THE μ PEEL'S TEST GONE TOO.
------------------------------------------------------------------

-- THIRTEEN OF THE SIXTEEN BUILDERS ARE LEAVES HERE, WHICH IS THE
-- ASSEMBLY-FIRST SHAPE AND NOT AN OMISSION.  Each is an ordinary
-- structural recursion the day its siblings exist; what this body is
-- for is the three clauses where the machine asks a question, so those
-- are the ones written out.
postulate
  subscribeE!-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
    (ac : Acc _≺_ τ) (i : Fin n) → EntryOK {Γ = Γ} (input i) τ →
    (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    Runs {e = e} (input i) κ id now sched st

subscribeE! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
  (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → Runs {e = e} b κ id now sched st
subscribeE! ac (input i) ok κ id now sched st =
  subscribeE!-input ac i ok κ id now sched st
subscribeE! ac (ofᵉ ts)  ok κ id now sched st = _ , subs-of refl
subscribeE! ac emptyᵉ    ok κ id now sched st = _ , subs-empty refl

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

------------------------------------------------------------------
-- THE TOP LINE, AND WHAT IT STOPS SAYING.
------------------------------------------------------------------

postulate
  drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    Σ[ rest ∈ Stream Γ t ] drain⇓ {e = e} fuel id sched st rest

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, AND THE RELATION
-- SAYS SO IN ONE CONSTRUCTOR — so this is the assembly and the two
-- builders are its leaves.  The root's entry invariant is discharged by
-- `evaluate`'s own seeding, exactly as it is today.
evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
  (ins : Slots Γ) → Σ[ out ∈ Stream Γ t ] evaluate⇓ fuel e ins out
evaluate! {n = n} fuel e ins =
  let ((burst , sched₀ , st₀) , s) =
        subscribeE! {lo = n} (rootWitness e ins) e (≤-refl , m≤m⊔n _ _)
                    root 0 0 (sched-init e ins) (st-init e)
      (rest , d) = drain! fuel 1 sched₀ st₀
  in (burst ++ rest) , eval-run s d

-- AND THE EVALUATOR AFTER THE CUTOVER.  Not a new machine — the SAME
-- machine with three clauses' worth of question removed, reached
-- through the builder rather than through a witness it seeds itself.
-- `rank-sufficient` is then not a theorem about numbers at all: it is
-- the observation that no constructor of the relation builds a dry
-- emit, which is what `Verify-Rank-Sufficient.evaluate⇓-nodry` already
-- proves of every derivation.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
