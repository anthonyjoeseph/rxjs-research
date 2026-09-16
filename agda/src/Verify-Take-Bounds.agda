-- TAKE BOUNDS THE STREAM.  A program whose outermost node is `take k`
-- emits at most k values, whatever sits underneath it and whatever the
-- slots deliver.  It is the smallest claim in this repo that is about
-- the EVALUATOR's own bookkeeping rather than about a correspondence:
-- no spec, no batching, no second run to compare against.
--
-- WHICH IS WHY IT IS THE REHEARSAL (Anthony).  Every other claim on
-- this face needs the run relation to be a function before a statement
-- about "the" output means anything; this one does not, because it is
-- an inequality about the one output the builder produces and holds of
-- any output at all.  So it exercises the take node's budget --
-- `take-st`, the frame, the dispatch split -- with none of the
-- determinacy apparatus in the way, and what it rehearses is the
-- induction over the drain that every well-formedness leaf also owes.
--
-- AND IT IS THE CHEAPEST THING HERE THAT CAN BE FALSE.  The budget is
-- decremented at the dispatch and the cut is emitted from the frame, so
-- an off-by-one between those two points, or a path that delivers
-- before it spends, is a counterexample rather than a hard proof -- and
-- it is reachable at a scripted slot with two entries and a take at one.
module Verify-Take-Bounds where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-assoc; length-++; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤; +-assoc; ≤-refl;
  ≤-reflexive)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim using (Fuel; InstEmit; _at_from_as_; InstEvent; value; init; close; handoff; complete)
open import Rx.Exp using (Ctx; Closed; nat̂; takeᵉ; Val; Tm; natᵗ; evalTm)
open import Rx.Evaluator using (Stream; Sched; EvalSt; take-st; lookupNode;
  sched-init; st-init; root; Path; takeVals; takeDispatch; NodeId;
  NodeState; take-f; retagEvents; splitEvents; scan-st; mergeAll-st;
  switch-st; exhaust-st)
open import Rx.Evaluator.Reducible using (reducible)
open import Rx.Evaluator.Builder using (evaluate↓; drain!)
open import Rx.Slots using (Slots)
open import Rx.Evaluator.Freshness using (lookup-set; PreservedBelow)
open import Rx.Evaluator.Freshness.Preserve using (subscribeE-preserves)
open import Rx.Evaluator.Domain using (subscribeE⇓; pushBurst⇓; stepFrame⇓;
  push-nil; push-cons; step-take; subs-take-zero; subs-take-suc)
open import Spec using (valuesOf)
open import Readme-Theorems using (emitValues)

----------------------------------------------------------------------
-- CONCATENATION IS WHAT THE TWO HALVES SHARE.  `emitValues` flattens
-- each instant's events in place, so it commutes with appending runs --
-- and nothing in the repo said so, because every consumer until now
-- read a whole run at once rather than a burst and a drain separately.
----------------------------------------------------------------------

emitValues-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  emitValues (xs ++ ys) ≡ emitValues xs ++ emitValues ys
emitValues-++ []                            ys = refl
emitValues-++ ((es at i from src as κ) ∷ xs) ys =
  trans (cong (valuesOf es ++_) (emitValues-++ xs ys))
        (sym (++-assoc (valuesOf es) (emitValues xs) (emitValues ys)))

----------------------------------------------------------------------
-- AND AN INSTANT'S VALUES ARE THE FRAME'S OUT-VALUES AND NOTHING
-- ELSE.  A frame reassembles its instant out of four pieces, and only
-- one of them can carry a value: the protocol half of the arriving
-- split holds no `value` by construction, the step's own events are
-- RETAGGED to the outgoing type and retagging drops values outright,
-- and the completion flag contributes at most a `complete`.  So the
-- length of what an instant emits is the length of what the dispatch
-- let through, which is the quantity the node's budget is spent in.
----------------------------------------------------------------------

valuesOf-++ : ∀ {A : Set} (es fs : List (InstEvent A)) →
  valuesOf (es ++ fs) ≡ valuesOf es ++ valuesOf fs
valuesOf-++ []             fs = refl
valuesOf-++ (value v  ∷ es) fs = cong (v ∷_) (valuesOf-++ es fs)
valuesOf-++ (init s   ∷ es) fs = valuesOf-++ es fs
valuesOf-++ (close s r ∷ es) fs = valuesOf-++ es fs
valuesOf-++ (handoff s ∷ es) fs = valuesOf-++ es fs
valuesOf-++ (complete ∷ es) fs = valuesOf-++ es fs

valuesOf-retag : ∀ {A B : Set} (es : List (InstEvent A)) →
  valuesOf (retagEvents {A} {B} es) ≡ []
valuesOf-retag []             = refl
valuesOf-retag (value v  ∷ es) = valuesOf-retag es
valuesOf-retag (init s   ∷ es) = valuesOf-retag es
valuesOf-retag (close s r ∷ es) = valuesOf-retag es
valuesOf-retag (handoff s ∷ es) = valuesOf-retag es
valuesOf-retag (complete ∷ es) = valuesOf-retag es

valuesOf-prot : ∀ {n} {Γ : Ctx n} {u} {A : Set} (es : List (InstEvent (Val Γ u))) →
  valuesOf {A} (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ []
valuesOf-prot []             = refl
valuesOf-prot (value v  ∷ es) = valuesOf-prot es
valuesOf-prot (init s   ∷ es) = valuesOf-prot es
valuesOf-prot (close s r ∷ es) = valuesOf-prot es
valuesOf-prot (handoff s ∷ es) = valuesOf-prot es
valuesOf-prot (complete ∷ es) = valuesOf-prot es

valuesOf-vals : ∀ {A : Set} (vs : List A) → valuesOf (map value vs) ≡ vs
valuesOf-vals []       = refl
valuesOf-vals (v ∷ vs) = cong (v ∷_) (valuesOf-vals vs)

valuesOf-fin : ∀ {A : Set} (b : Bool) →
  valuesOf {A} (if b then complete ∷ [] else []) ≡ []
valuesOf-fin true  = refl
valuesOf-fin false = refl

-- AND THE FOUR PIECES, ASSEMBLED.  This is the shape every frame's
-- cons clause splices, so the lemma is stated over the pieces rather
-- than over any one frame: the protocol half is a hypothesis because
-- it is the only piece whose emptiness depends on where it came from.
frame-values : ∀ {A B : Set} (bs : List (InstEvent B)) (es : List (InstEvent A))
  (vs : List B) (fin : Bool) → valuesOf bs ≡ [] →
  valuesOf (bs ++ retagEvents {A} {B} es ++ map value vs
             ++ (if fin then complete ∷ [] else [])) ≡ vs
frame-values bs es vs fin bq =
  trans (valuesOf-++ bs _)
    (trans (cong (_++ valuesOf (retagEvents {A = _} {B = _} es ++ map value vs
                                 ++ (if fin then complete ∷ [] else []))) bq)
      (trans (valuesOf-++ (retagEvents es) _)
        (trans (cong (_++ valuesOf (map value vs
                                     ++ (if fin then complete ∷ [] else [])))
                     (valuesOf-retag es))
          (trans (valuesOf-++ (map value vs) _)
            (trans (cong₂ _++_ (valuesOf-vals vs) (valuesOf-fin fin))
                   (++-identityʳ vs))))))

----------------------------------------------------------------------
-- THE RUN, IN ITS TWO HALVES.  `evaluate↓` is a subscribe frame followed
-- by a drain, and the take node's budget is the ONLY thing that crosses
-- between them -- so these name the three components the builder threads
-- and nothing else.  They are definitions rather than a shared Σ because
-- a Σ shared by the two leaves would be satisfied by enlarging the
-- witness, and what has to be pinned is that both leaves speak of the
-- SAME budget.
----------------------------------------------------------------------

-- RECOVERY: git show 6ca41995 restores the transport lift -- an
--   equation identifying this run with `redExpAcc` applied at the
--   indices `reducible` instantiates, got by pulling the `subst` at
--   `reducible`'s head off the triple it does not occur in.  Wanted
--   again only by a claim that must see the WALK's clauses rather
--   than the derivation's constructors.
rootRun : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt (takeᵉ (nat̂ k) e)
rootRun {n = n} k e ins =
  proj₁ (reducible (takeᵉ (nat̂ k) e) (root {lo = n}) 0 0
          (sched-init (takeᵉ (nat̂ k) e) ins) (st-init (takeᵉ (nat̂ k) e)))

rootBurst : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
rootBurst k e ins = proj₁ (rootRun k e ins)

drainRest : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
  (ins : Slots Γ) → Stream Γ t
drainRest fuel k e ins =
  proj₁ (drain! fuel 1 (proj₁ (proj₂ (rootRun k e ins))) (proj₂ (proj₂ (rootRun k e ins))))

-- THE BUDGET THE FRAME HANDS THE DRAIN.  The root's take node is minted
-- at `nextNode` of the initial schedule, which is zero, so the node is
-- named by a numeral rather than by a lookup of its own.  A state with
-- no such node reads as zero, which is the honest reading: the drain
-- then has nothing to spend.  Read off a TRIPLE rather than off the run,
-- so that a statement about the budget transports along an equation
-- between two runs -- which is what the frame's zero arm needs.
budgetIn : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → ℕ
budgetIn (just (take-st b)) = b
budgetIn _                  = zero

nodeBudget : ∀ {n} {Γ : Ctx n} {u} {E : Closed Γ u} → NodeId → EvalSt E → ℕ
nodeBudget nid st = budgetIn (lookupNode nid (EvalSt.nodes st))

budgetOf : ∀ {n} {Γ : Ctx n} {t u} {E : Closed Γ u} →
  Stream Γ t × Sched Γ × EvalSt E → ℕ
budgetOf r = nodeBudget 0 (proj₂ (proj₂ r))

takeBudget : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) → ℕ
takeBudget k e ins = budgetOf (rootRun k e ins)

-- A RUN IS ITS BURST FOLLOWED BY ITS DRAIN, DEFINITIONALLY.  Pinned
-- rather than assumed, because every line below reads the two halves
-- separately and nothing else says they reassemble into the one stream
-- the statement is about.
run-splits : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
  (ins : Slots Γ) →
  evaluate↓ fuel (takeᵉ (nat̂ k) e) ins ≡ rootBurst k e ins ++ drainRest fuel k e ins
run-splits _ _ _ _ = refl

takeVals-spends : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vals : List (Val Γ s)) →
  length (proj₁ (takeVals k vals)) + proj₁ (proj₂ (takeVals k vals)) ≡ k
takeVals-spends zero          _        = refl
takeVals-spends (suc k)       []       = refl
takeVals-spends (suc zero)    (v ∷ _)  = refl
takeVals-spends (suc (suc k)) (v ∷ vs) = cong suc (takeVals-spends (suc k) vs)

takeVals-cut : ∀ {n} {Γ : Ctx n} {s} (k : ℕ) (vals : List (Val Γ s)) →
  proj₂ (proj₂ (takeVals k vals)) ≡ true → proj₁ (proj₂ (takeVals k vals)) ≡ zero
takeVals-cut zero          _        ()
takeVals-cut (suc k)       []       ()
takeVals-cut (suc zero)    (v ∷ _)  _  = refl
takeVals-cut (suc (suc k)) (v ∷ vs) eq = takeVals-cut (suc k) vs eq

-- WHAT ONE DISPATCH SPENDS.  The node's budget is an ACCOUNT: whatever
-- the step lets through plus whatever it leaves in the node is what it
-- started with, on both branches.  The cut branch zeroes the node and
-- is exact only because a cut spends the budget entirely; the non-cut
-- branch writes back what `takeVals` reported remaining.
takeDispatch-spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) (b : ℕ) →
  let d = takeDispatch {e = e} nid vals fin sched st (just (take-st b)) in
  length (proj₁ d) + nodeBudget nid (proj₂ (proj₂ (proj₂ (proj₂ d)))) ≡ b
takeDispatch-spends nid vals fin sched st b
  with proj₂ (proj₂ (takeVals b vals)) in ceq
... | true  =
  trans (cong₂ _+_ refl
          (trans (cong budgetIn (lookup-set nid (take-st zero) (EvalSt.nodes st)))
                 (sym (takeVals-cut b vals ceq))))
        (takeVals-spends b vals)
... | false =
  trans (cong₂ _+_ refl
          (cong budgetIn
            (lookup-set nid (take-st (proj₁ (proj₂ (takeVals b vals)))) (EvalSt.nodes st))))
        (takeVals-spends b vals)

-- AND AT THE NODE THE DISPATCH ACTUALLY READS.  The step does not
-- receive the node's state, it LOOKS IT UP, so the account has to be
-- stated against that lookup rather than against a supplied budget --
-- and every state that is not a take's reads as zero on both sides,
-- which is the honest arm rather than a gap: a frame whose node is
-- missing or holds another operator's state emits nothing and spends
-- nothing.
step-take-spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ)
  (st : EvalSt e) →
  let d = takeDispatch {e = e} nid vals fin sched st
            (lookupNode nid (EvalSt.nodes st)) in
  length (proj₁ d) + nodeBudget nid (proj₂ (proj₂ (proj₂ (proj₂ d))))
    ≡ nodeBudget nid st
step-take-spends nid vals fin sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (take-st b) = takeDispatch-spends nid vals fin sched st b
... | just (scan-st _)           = cong budgetIn leq
... | just (mergeAll-st _ _ _ _) = cong budgetIn leq
... | just (switch-st _ _)       = cong budgetIn leq
... | just (exhaust-st _ _)      = cong budgetIn leq
... | nothing                    = cong budgetIn leq

----------------------------------------------------------------------
-- THE FRAME'S WHOLE BURST IS ONE ACCOUNT, and it is stated over the
-- DERIVATION rather than over the walk that produces one.  The walk
-- reaches a take through a transport and two accessors, none of which
-- a statement about the node's budget has any business mentioning;
-- the derivation carries the same three components with its own
-- constructor at the head, so the induction is on a datatype rather
-- than on whatever happens to reduce.
--
-- AND IT IS AN EQUALITY RATHER THAN THE INEQUALITY THE CONSUMER
-- WANTS, because an inequality does not compose along the fold: each
-- instant would lose exactly the slack the next one is denominated
-- in, and the sum would be bounded by nothing.
----------------------------------------------------------------------

step-take-deriv : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  {id now} {nid : NodeId} {κ : Path Γ lo s t} {vals : List (Val Γ s)} {fin}
  {sched sched₁ : Sched Γ} {st st₁ : EvalSt e} {vals′ evs fin′}
  → stepFrame⇓ {e = e} id now (take-f nid) κ vals fin sched st
      (vals′ , evs , fin′ , sched₁ , st₁)
  → length vals′ + nodeBudget nid st₁ ≡ nodeBudget nid st
step-take-deriv {nid = nid} {vals = vals} {fin = fin} {sched = sched} {st = st}
  step-take = step-take-spends nid vals fin sched st

push-take-spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
  {id now} {nid : NodeId} {κ : Path Γ lo s t} {ems : Stream Γ s}
  {sched sched₂ : Sched Γ} {st st₂ : EvalSt e} {rest}
  → pushBurst⇓ {e = e} id now (take-f nid) κ ems sched st (rest , sched₂ , st₂)
  → length (emitValues rest) + nodeBudget nid st₂ ≡ nodeBudget nid st
push-take-spends push-nil = refl
push-take-spends {nid = nid} {st = st} (push-cons {em = em} {vals′ = vals′}
                  {evs = evs} {fin′ = fin′} {st₁ = st₁} {rest = rest}
                  refl d dr) =
  trans
    (cong (_+ _)
      (trans (cong (λ z → length (z ++ emitValues rest))
                   (frame-values (proj₁ (proj₂ (splitEvents (InstEmit.events em))))
                                 evs vals′ fin′
                                 (valuesOf-prot (InstEmit.events em))))
             (length-++ vals′)))
    (trans (+-assoc (length vals′) (length (emitValues rest)) _)
           (trans (cong (length vals′ +_) (push-take-spends dr))
                  (step-take-deriv d)))

----------------------------------------------------------------------
-- AND THE ROOT'S TAKE SPENDS EXACTLY ITS BUDGET.  The frame installs
-- the node at the schedule's own `nextNode` and then subscribes the
-- inner expression ABOVE it, so nothing the inner walk does can reach
-- the node -- which is what makes the budget the push reads back the
-- one the frame wrote.  The zero arm needs the node to be FRESH, and
-- that is a hypothesis rather than a fact about the walk: there the
-- frame installs nothing, so a node already holding a budget would be
-- read as this take's own.
----------------------------------------------------------------------

root-take-spends : ∀ {n} {Γ : Ctx n} {t} {E : Closed Γ t} {u lo}
  {count : Tm Γ [] [] [] natᵗ} {b : Closed Γ u} {κ : Path Γ lo u t} {id now}
  {sched : Sched Γ} {st : EvalSt E} {r}
  → lookupNode (Sched.nextNode sched) (EvalSt.nodes st) ≡ nothing
  → subscribeE⇓ {e = E} (takeᵉ count b) κ id now sched st r
  → length (emitValues (proj₁ r))
      + nodeBudget (Sched.nextNode sched) (proj₂ (proj₂ r))
    ≡ evalTm count
root-take-spends fresh (subs-take-zero ceq refl) =
  trans (cong (0 +_) (cong budgetIn fresh)) (sym ceq)
root-take-spends {st = st} fresh (subs-take-suc {k = k} ceq refl inner push) =
  trans (trans (push-take-spends push)
               (trans (cong budgetIn
                        (PreservedBelow.below
                          (subscribeE-preserves (suc _) ≤-refl inner) _ ≤-refl))
                      (cong budgetIn
                        (lookup-set _ (take-st (suc k)) (EvalSt.nodes st)))))
        (sym ceq)

----------------------------------------------------------------------
-- AND THE RUN IS A DERIVATION, which is the whole of what the frame's
-- half needed.  `reducible` pairs its triple with a derivation about
-- the very expression it was asked for, and the transport at its head
-- is INSIDE that pair rather than in front of it -- so the derivation
-- arrives already stated at `takeᵉ`, and the constructor at its head
-- is the take's own.
----------------------------------------------------------------------

rootDeriv : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  subscribeE⇓ {e = takeᵉ (nat̂ k) e} (takeᵉ (nat̂ k) e) (root {lo = n}) 0 0
    (sched-init (takeᵉ (nat̂ k) e) ins) (st-init (takeᵉ (nat̂ k) e))
    (rootRun k e ins)
rootDeriv {n = n} k e ins =
  proj₁ (proj₂ (reducible (takeᵉ (nat̂ k) e) (root {lo = n}) 0 0
          (sched-init (takeᵉ (nat̂ k) e) ins) (st-init (takeᵉ (nat̂ k) e))))

----------------------------------------------------------------------
-- THE FRAME'S HALF, AND IT IS AN EQUALITY.  What the subscribe frame
-- emits plus what it leaves in the node is EXACTLY the budget it
-- started with -- the node is an account and the frame is the only
-- thing that touches it, so nothing is lost and nothing is invented.
-- The consumer wants only the inequality, and takes it by reflexivity.
----------------------------------------------------------------------

take-burst-spends :
  ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  length (emitValues (rootBurst k e ins)) + takeBudget k e ins ≡ k
take-burst-spends k e ins = root-take-spends refl (rootDeriv k e ins)

take-burst-bound :
  ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  length (emitValues (rootBurst k e ins)) + takeBudget k e ins ≤ k
take-burst-bound k e ins = ≤-reflexive (take-burst-spends k e ins)

----------------------------------------------------------------------
-- THE TWO HALVES OF THE BUDGET, and the split is the whole design.  The
-- frame spends some of `k` and hands the rest on; the drain spends no
-- more than it was handed.  Both leaves are denominated in the SAME
-- `takeBudget`, which is a computed number rather than a witness, so
-- neither can be met by enlarging anything.
----------------------------------------------------------------------

postulate
  -- And the drain spends no more than it was handed.  Stated over the
  -- budget rather than over `k` because the drain never sees `k`: it
  -- reads the node's state, which is the only thing that crosses the
  -- frame boundary.
  -- PROBED: `Probed.Take-Bounds`, at a cut landing ACROSS two arrivals,
  --   which is the one shape that forces the budget to survive the frame
  --   and be spent in the drain.  TIGHT, and pinned beside the same
  --   program with the take removed.  Not reached: every flattening
  --   program, a take nested under another take, and a budget that is
  --   not a literal.
  take-drain-bound :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
      (ins : Slots Γ) →
    length (emitValues (drainRest fuel k e ins)) ≤ takeBudget k e ins

----------------------------------------------------------------------
-- THE BOUND.  Stated over the flat value stream rather than over
-- batches, because `take` counts values: a batch-level statement would
-- be weaker exactly where the node is interesting, since the cut can
-- land mid-batch.
----------------------------------------------------------------------


take-bounds-values :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ)
    (e : Closed Γ t) (ins : Slots Γ) →
  length (emitValues (evaluate↓ fuel (takeᵉ (nat̂ k) e) ins)) ≤ k
take-bounds-values fuel k e ins =
  subst (λ xs → length (emitValues xs) ≤ k) (sym (run-splits fuel k e ins))
    (subst (_≤ k)
      (sym (trans (cong length (emitValues-++ (rootBurst k e ins)
                                              (drainRest fuel k e ins)))
                  (length-++ (emitValues (rootBurst k e ins)))))
      (≤-trans (+-monoʳ-≤ (length (emitValues (rootBurst k e ins)))
                          (take-drain-bound fuel k e ins))
               (take-burst-bound k e ins)))
