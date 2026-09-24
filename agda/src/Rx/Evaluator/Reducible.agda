------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS, AND THE PATH CARRIED AS
-- A PROOF-CARRYING CONTINUATION.
------------------------------------------------------------------

-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- expression to its subscription derivation may not mention that
-- derivation's own type in a negative position, so the candidate
-- cannot be an inductive family over the domain relation.  Defined by
-- recursion on `Ty` it never needs to be: `Red m (obs u)` mentions
-- `Red m u` at a strictly smaller type and `subscribeE⇓` only
-- positively.

-- A SUBSCRIBE TAKES THE REST OF THE PATH IN, AS AN OPAQUE
-- CONTINUATION, AND ANSWERS AT THE ROOT.  `RP m (Red m u) S κ` is the
-- path above the subscribe, packaged as a fold that takes values AT
-- `u` with their candidates and answers at the root; the candidate at
-- `obs u` takes one in and hands its state back.  `Red m u` occurs in
-- the observable arm only as that parameter, so the recursion on `Ty`
-- is structural, and the answer is at `t` because it carries no
-- candidate.  Folding where a value is produced is the only order that
-- agrees with rxjs: a value a share's fan-out delivers during the
-- subscribe would otherwise arrive behind or ahead of the answer, and
-- a counting frame could tell.

-- AND THE CANDIDATE HANDS BACK A TRACE, WHICH IS HOW AN ARM RECOVERS
-- ITS OWN SUCCESSOR.  A stateful frame writes a value into the store
-- that the store cannot vouch for, since a candidate is one universe
-- above the state; the frame's SUCCESSOR continuation closes over the
-- candidate it just computed and stands on the store still holding
-- what it closed over (`Pre`, below).  The arm
-- that pushed the frame needs that successor -- `batchSync` folds its
-- flush through it after its source's subscribe has returned -- and
-- the subscribe it called can only answer at the SOURCE's type, one
-- frame below.  So the answer carries the trace: every call the
-- subscribe made to the continuation it was handed, with the column,
-- the flag and the state each was made in, at the source's type.  The
-- arm translates each call through the frame it pushed and REPLAYS its
-- parent over the result; folds are pure, so the replay computes the
-- successor the run built.  Nothing in the record names a type above
-- its own, and `Red m (obs u)` still mentions `Red m u` alone.
--
-- DEAD ROUTE: typing the peel instead -- a field of the record at the
--   frame's output type, whether named through a field, a frame-stack
--   index or the path's own index.  Any such field instantiates the
--   record's parameter at `Red` of a larger type, and the parameter
--   sits in the fold's domain, so the record occurs NEGATIVELY in
--   itself through the observable arm.  The positivity failure is
--   genuine, not conservative: it is the Girard-Tait descent refusing
--   a candidate that mentions a type above its own.
-- DEAD ROUTE: a candidate quantifying over the parent's predicate
--   abstractly, or over a telescope of predicates along the path.  A
--   predicate is a `Set₁`, so the quantification lands the candidate
--   in `Set₂` and the ceiling of universes climbs with every frame.
-- DEAD ROUTE: re-indexing the candidate by the room WHILE THE ANSWER
--   CARRIES A SATISFACTION COLUMN.  The connect's def comes back
--   proven at the inner ceiling and the arm owes the column at the
--   outer; weakening runs the other way.  The trace does not reopen
--   it: a call is recorded at the ceiling of the continuation it was
--   made to, and a continuation dropped to a lower ceiling forgets its
--   candidates on the way down, so what the lower run recorded is
--   exactly the data-vouched column the higher record received.
-- RECOVERY: git show 3abdafa1:agda/src/Rx/Evaluator/Reducible.agda
--   holds every arm as a real body over the successor design -- the
--   frame continuations, the certification of a cell against its held
--   column, the flattener walks and drains, the share's fan-out under
--   the connect's peel, and the two runtime guards whose dead branches
--   were the postulates `stuck-hop` and `stuck-finish`.  Each arm
--   ports by adding the trace to what it answers and replaying its
--   parent where it used to peel.
-- RECOVERY: git show 3abdafa1:agda/src/Rx/Evaluator/Keeps.agda holds
--   the store-preservation lemmas every arm spends on its room proof.
-- RECOVERY: git show 3abdafa1:agda/src/Rx/Exp/ValEq.agda holds a
--   decidable value equality, which certifying a cell against a held
--   column needed and standing on the store's agreement does not.

-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the scheduler and the evaluator state as plain indices with no
-- precondition, so the candidate can demand subscribability in EVERY
-- state whose room is under the ceiling -- which is what lets a
-- flattener's hop subscribe its inner in whatever state the outer
-- delivery reached, with no invariant threaded.

-- AND THE CEILING IS AN INDEX OF THE CANDIDATE.  A candidate proven at
-- a lower ceiling is only ever APPLIED, to a continuation that has
-- been dropped to that ceiling by forgetting what it was going to be
-- handed; the outer arm sees a state and an answer, and states carry
-- no ceiling.  That is what lets a connect's peel fund the raw fan-out
-- below it.

-- AND THE ENVIRONMENT IS CARRIED RATHER THAN SUBSTITUTED, WHICH IS
-- WHAT MAKES THE WHOLE SUBSTITUTION LAYER UNNECESSARY.  An observable
-- value IS a body paired with the environment it closed over, so the
-- expression face concludes about that pair directly and no lemma
-- relating a peel to a substitution is owed anywhere.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<; n≤1+n; <-≤-trans; <⇒≤; ∸-monoʳ-<; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Prim using (Tick)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; unfoldμ; varᵗ; unit̂; bool̂; nat̂; nilᵗ; consᵗ; foldᵗ;
  pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; FnClo; applyClo)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; pres; below; pres-write; lookup-set; set-above; <→≢ᵇ)
open import Decide using (∧ˡ; ∧ʳ; ≡ᵇ-refl)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f;
  batchSync-f; from-inner; thru-outer; NodeState; lookupNode; frameNodes; register;
  installNode; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; mergeAllᵒ; AllOp; switchᵒ;
  exhaustᵒ; NodeId; cell-st; take-st; switch-st; exhaust-st; batchSync-st; setNode; hasRoom;
  consumeUsable; finishUsable; thruWrap; switchKill; aliveThroughᶠ; RegId; scanDispatch;
  batchDown; shareAdmit; shareDying; shareSpend; drainSt)
open import Rx.Evaluator.Unconn-Arith using (unconn-insert; fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps; switchKill-keeps; thruWrap-keeps; thruWalk-keeps;
  thruConsume-keeps; subscribeE-keeps; shareGo-keeps; shareDying-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; mergeAllDrain⇓; subs-of; subs-empty; subs-mint; subs-defer; subs-floor; subs-μ;
  subs-map; subs-take-zero; subs-take-suc; subs-scan; subs-batchSync; subs-shared; slot-spent;
  slot-join; slot-connect; connect; foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map;
  injectRoot; inner; thruConsume⇓; consume-all-sub; consume-all-enqueue; consume-switch-sub;
  consume-exhaust-sub; thruWalk⇓; walk-nil; walk-cons; drain-spent; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil; react-false;
  react-alive; react-dead; step-from-inner; step-thru-outer; subscribeAll⇓; sub-all;
  subs-merge-all; subs-switch-all; subs-exhaust-all; shareWalk⇓; shareGo⇓; fold-sink; disp;
  walk-end; walk-more; go-nil; go-cut; go-live; drain-nil; drain-no-room; drain-room;
  step-scan; step-take; step-batchSync)

open import Rx.Evaluator.Reducible.Support using (Agree; Ans; Apart; Arm; BatchHeld; Call; Column;
  ConsistentF; Fell; FrameStep; by-bool; FreshF; HeldF; HoldsFs; Kept; NodeOn; Pre; PreFs; PreHolds; QEmpty; RP; Red;
  RedEnv; Room; RoomEmpty; Rule; ScanHeld; Sound; Stage; SubStep; Trace; Wrapped; []ᵗ; _∷ᵗ_; _++ᵗ_; admit-agree; admit-ot;
  ans; apart-fi; apply; batchStep; batch₀; bumpNode; call; cell-inj; colsOf; consumeNil; der;
  distinct; downHeld; drain-waiting; drop-ot; dropS; dying-rule; end-++; endPre; endRP; endS; ends-register;
  ends-sub; f-exhaust; f-merge; f-switch; fallen; fallenStage; fellᵗ; fiHolds→thru; finishing; fold;
  fresh-apart; fresh-inner; fresh-path; fresh-sound; ground; grounded; head-off;
  head-on; headHolds; headKept; headPre; held; holds-step; holdsFs-step; holdsOf;
  inner-back; joinPre; kept; kept-in; kept-shift; kept-step; kill-sub; lower-nodes; mapStep; next; node-eq;
  node-in₁; node-one; node-two; ofColumn; out; push-sound; push-thru; qempty-room; red-scripted;
  redFoldVals; redLookup; register-sound; room-wrap; row-sound; ruled; scanCons; scanCt;
  scanOff; scanRed; scanReg; scanStepped; self-node; sink-sound; sounds; spend-or; ceil-or; stage; stage-map;
  stage-nil; stage-rebase; stage-seq; standing; step; step-cons; step-ct; step-off; step-red;
  step-reg; step-⇓; st″; sub-on; sub-ot; sub-rule; switchKill-ct; switchKill-nodes; takeStep;
  termini; u-exhaust; u-merge; u-switch; unheadHolds; unheadKept; usable; waiting; wrap-facts; wrap-ot;
  wrap-reg; wrapNode; writeStage; ∨-T)
open import Rx.Evaluator.Reducible.Floor using (fold-refill-spends; raw-kept; refill-spends)
open import Rx.Evaluator.Reducible.Rule-Kept using (fold-kept; fold-sound; step-kept; subscribe-kept)
open import Rx.Evaluator.Reducible.Calls using (callStage; fiStep; headCall; inner-after)

baseRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
         (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
       → (op : AllOp) (nid inst : NodeId) (κ : Path Γ ℓ u t)
         (pfs : PreFs (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ))
       → ∀ {b} → Acc _<_ b → waiting (proj₁ pfs) ≤ b
       → RP {e = e} m (Red m u) ⊤ (from-inner op nid inst ↠[ ≤-refl ] κ) (standing pfs)

-- what one fold of the base answers: fallen where it connected, and the
-- base again, over the store's columns, where it did not -- at the
-- accessibility it was built over, the queue read back under the same
-- ceiling by `fold-refill-spends`, decided and not assumed as the
-- drain's bound is
baseAns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
          (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
        → (op : AllOp) (nid inst : NodeId) (κ : Path Γ ℓ u t) {now : Tick} {vals : List (Val Γ u)} {fin : Bool}
          (sched : Sched Γ) (st : EvalSt e) → Room m sched st
        → Sound (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ) sched st
        → ∀ {b} → Acc _<_ b → waiting (lookupNode nid (EvalSt.nodes st)) ≤ b
        → (r : Stream Γ t × Sched Γ × EvalSt e)
        → foldPath⇓ {e = e} now (from-inner op nid inst ↠[ ≤-refl ] κ) vals fin sched st r
        → Ans {e = e} m (Red m u) ⊤ (from-inner op nid inst ↠[ ≤-refl ] κ) now vals fin sched st

-- ONE INNER SUBSCRIBED RAW, under its exit frame pushed on a path the
-- store holds: its own candidate, at the room it was handed, over the
-- base.  Every caller hands it the room exactly at the ceiling -- the
-- fallen fold because its peel lands there, the arrival spine because
-- it seeds there -- so the inner stands on the store's own columns,
-- which the rule vouches for.

-- IT RE-ENTERS THE CANDIDATE, AND THE CANDIDATE REACHES THE RAW FOLD
-- AGAIN THROUGH THE FALLEN CONTINUATION AND THROUGH THE BASE.  The
-- fallen fold peels the room's accessibility.  The base's fold reaches
-- `rawInner` again at its own path only through its drain, whose inner
-- is budgeted at the queue's accessibility, strictly below the one the
-- base was built over, or at the room the refill peeled; everywhere
-- else the base folds the path below it, which is shorter.  The queue's
-- accessibility travels as a CEILING WITH THE WITNESS BESIDE IT, so the
-- base's successor and the drain's next pop keep the very accessibility
-- they were handed, and every pop is a structural child of it.  Under the
-- room every member keeps the order it had: the input bound and the
-- term size at the arms, the value at `red-val`, the path and its floor
-- at the raw fold, and every continuation builder guarded by the `fold`
-- copattern it answers.
-- STRUCTURAL SCC: baseAns baseRP batchFinish consume consumeFallen consumeStanding fallenRP headNext liveRP rawAfter rawConsume rawDrain rawFinish rawFold rawGo rawInner rawReact rawThru rawWalk red-all red-batchSync red-env red-exhaustAll red-input red-input-shared red-map red-mapFn red-mergeAll red-scan red-switchAll red-take red-val redExpAcc redTmAcc redTmsAcc reducible stepStage subNext subRP subStanding thruStep translate translate-go translate-sub translate-sub-end translate-sub-end-go translate-sub-go walk

-- DEAD ROUTE: the inners on `fallen` ground.  At the peeled ceiling the
--   room is not below it; raising the ceiling a step needs an
--   accessibility the peel does not hand out, and a fresh one is not
--   smaller than the fold's.  Handing the fold the UNPEELED
--   accessibility with the fall instead makes the fallen fold its own
--   successor at the same accessibility, through every arm that pushes
--   a frame.
-- DEAD ROUTE: each pushed frame rebuilt raw from the store at the same
--   ceiling.  Every arm pushing a frame re-enters the raw fold at the
--   same accessibility over a longer path, and nothing on that cycle is
--   smaller -- the candidate re-seeds the term and the type.
rawInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
           (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
         → (op : AllOp) (nid : NodeId) (κ : Path Γ ℓ u t) (now : Tick) (o : Val Γ (obs u))
           (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → Sound κ sched st → NodeOn nid κ sched st
         → (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h
         → ∀ {b} → Acc _<_ b → waiting h ≤ b
         → Σ (Stream Γ t × Sched Γ × EvalSt e)
             (subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st)

-- a merge's queue drained raw, one inner a lane, on the fuel the finish
-- found it at: each inner is budgeted at the queue it leaves, and a
-- queue read back longer than that has spent room, so the drain goes on
-- at the ceiling the connect peeled.  The bound is decided, not assumed:
-- the evaluator runs this body, and a budget built from a postulate
-- would be forced by the next pop, so only a queue that overran with
-- nothing spent reaches `refill-spends`, and that is its refutation
rawDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ}
           (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
         → (nid : NodeId) (κ : Path Γ ℓ s t) (now : Tick) (fuel : List (Val Γ (obs s)))
           (lim : Maybe ℕ) (act : ℕ) (od : Bool) (q : List (Val Γ (obs s)))
           (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → Sound κ sched st → NodeOn nid κ sched st → ∀ {b} → Acc _<_ b → length q ≤ b
         → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
             (λ r → mergeAllDrain⇓ {e = e} nid κ now fuel lim act od q sched st r
                  × Sound κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  × NodeOn nid κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))))
rawDrain ac le aM nid κ now [] lim act od q sched st rm so nd aq wq = _ , drain-spent , so , nd
rawDrain ac le aM nid κ now (_ ∷ fs) lim act od [] sched st rm so nd aq wq = _ , drain-nil , so , nd
rawDrain {s = s} ac le (acc rsM) nid κ now (_ ∷ fs) lim act od (o ∷ q) sched st rm so nd (acc rs) wq =
  by-bool (hasRoom lim act) (λ eqr → _ , drain-no-room eqr , so , nd) λ eqr →
  let (r₁ , d₁) = rawInner ac le (acc rsM) mergeAllᵒ nid κ now o sched
                    (record st { nodes = setNode nid (mergeAll-st {t = s} lim (suc act) q od) (EvalSt.nodes st) })
                    rm (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                    (just (mergeAll-st {t = s} lim (suc act) q od)) (lookup-set nid _ (EvalSt.nodes st)) (rs wq) ≤-refl
      (so₁ , nd₁) = inner-after mergeAllᵒ nid κ sched d₁ (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
      ds = drainSt s (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁))))
  in [ (λ sp →
         let (r₂ , d₂ , so₂ , nd₂) = rawDrain ac le (rsM (<-≤-trans sp rm)) nid κ now fs (proj₁ ds) (proj₁ (proj₂ ds))
                                       (proj₂ (proj₂ (proj₂ ds))) (proj₁ (proj₂ (proj₂ ds)))
                                       (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) ≤-refl so₁ nd₁ (<-wellFounded _) ≤-refl
         in _ , drain-room eqr (inner refl d₁) refl d₂ , so₂ , nd₂)
     , (λ nw →
         let w  = proj₂ nw
             bd = ≤-trans (drain-waiting s (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁))))) w
             (r₂ , d₂ , so₂ , nd₂) = rawDrain ac le (acc rsM) nid κ now fs (proj₁ ds) (proj₁ (proj₂ ds))
                                       (proj₂ (proj₂ (proj₂ ds))) (proj₁ (proj₂ (proj₂ ds)))
                                       (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) (room-keeps (subscribeE-keeps d₁) rm) so₁ nd₁
                                       (rs wq) bd
         in _ , drain-room eqr (inner refl d₁) refl d₂ , so₂ , nd₂)
     ]′ (spend-or (refill-spends mergeAllᵒ nid κ d₁ (sub-on (λ r∈ → r∈) ≤-refl nd)
                                 (lookup-set nid _ (EvalSt.nodes st))))

-- one observable consumed raw: the store says which lane it takes
rawConsume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
             (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
           → (op : AllOp) (nid : NodeId) (κ : Path Γ ℓ u t) (now : Tick) (o : Val Γ (obs u))
             (sched : Sched Γ) (st : EvalSt e) → Room m sched st
           → Sound κ sched st → NodeOn nid κ sched st
           → Σ (Stream Γ t × Sched Γ × EvalSt e)
               (λ r → thruConsume⇓ {e = e} op nid κ now o sched st r
                    × Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) × NodeOn nid κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
rawConsume {u = u} ac le aM op nid κ now o sched st rm so nd
  with lookupNode nid (EvalSt.nodes st) in c
... | h with consumeUsable op u h in equ
...   | false = _ , consumeNil op (trans (cong (consumeUsable op u) c) equ) , so , nd
...   | true with usable op u h equ
...     | u-switch cur od =
          let sk  = switchKill cur sched st
              st₁ = record (proj₂ sk) { nodes = setNode nid (switch-st (just (nodeCt (proj₁ sk))) od) (EvalSt.nodes (proj₂ sk)) }
              ct  = subst (nodeCt sched ≤_) (sym (switchKill-ct cur sched st)) ≤-refl
              so′ = sub-ot {κ = κ} {sched = sched} {sched′ = proj₁ sk} {st = st} {st′ = st₁} (kill-sub cur sched st) ct so
              nd′ = sub-on {nid = nid} {κ = κ} {sched = sched} {sched′ = proj₁ sk} {st = st} {st′ = st₁} (kill-sub cur sched st) ct nd
              (r , d) = rawInner ac le aM switchᵒ nid κ now o (proj₁ sk) st₁
                          (room-keeps (switchKill-keeps cur sched st refl) rm) so′ nd′
                          _ (lookup-set nid _ (EvalSt.nodes (proj₂ sk))) (<-wellFounded _) ≤-refl
          in _ , consume-switch-sub c refl refl (inner refl d) , inner-after switchᵒ nid κ (proj₁ sk) d so′ nd′
...     | u-exhaust od =
          let (r , d) = rawInner ac le aM exhaustᵒ nid κ now o sched
                          (record st { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) }) rm
                          (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                          _ (lookup-set nid _ (EvalSt.nodes st)) (<-wellFounded _) ≤-refl
          in _ , consume-exhaust-sub c (inner refl d)
               , inner-after exhaustᵒ nid κ sched d (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
...     | u-merge lim act q od = by-bool (hasRoom lim act)
          (λ eqr → _ , consume-all-enqueue c eqr , sub-ot (λ r∈ → r∈) ≤-refl so , sub-on (λ r∈ → r∈) ≤-refl nd)
          (λ eqr →
          let (r , d) = rawInner ac le aM mergeAllᵒ nid κ now o sched
                          (record st { nodes = setNode nid (mergeAll-st lim (suc act) q od) (EvalSt.nodes st) }) rm
                          (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                          _ (lookup-set nid _ (EvalSt.nodes st)) (<-wellFounded _) ≤-refl
          in _ , consume-all-sub c eqr (inner refl d)
               , inner-after mergeAllᵒ nid κ sched d (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd))

-- the outer's values consumed raw, in walk order
rawThru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
          (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
        → (op : AllOp) (nid : NodeId) (κ : Path Γ ℓ u t) (now : Tick) (vals : List (Val Γ (obs u)))
          (sched : Sched Γ) (st : EvalSt e) → Room m sched st
        → Sound κ sched st → NodeOn nid κ sched st
        → Σ (Stream Γ t × Sched Γ × EvalSt e)
            (λ r → thruWalk⇓ {e = e} op nid κ now vals sched st r
                 × Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) × NodeOn nid κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
rawThru ac le aM op nid κ now [] sched st rm so nd = _ , walk-nil , so , nd
rawThru ac le aM op nid κ now (o ∷ os) sched st rm so nd =
  let (r₁ , d₁ , so₁ , nd₁) = rawConsume ac le aM op nid κ now o sched st rm so nd
      (r₂ , d₂ , so₂ , nd₂) = rawThru ac le aM op nid κ now os (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁))
                                (room-keeps (thruConsume-keeps d₁) rm) so₁ nd₁
  in _ , walk-cons d₁ d₂ , so₂ , nd₂

-- THE RAW FOLD OF A PATH THE STORE HOLDS.  An arrival and a share's
-- fan-out fold down registry paths nd subscribe built, so the frames'
-- held candidates are rebuilt by `red-val` on what the store holds,
-- funded by the room the connect peeled and by the floor: a chain
-- registered on a share sinks STRICTLY above that share, so past a
-- sink the rows fan out at a higher floor.  It is a fold and not a
-- continuation because it holds nothing between calls -- its
-- successor would be itself -- and because the arrival spine and the
-- fallen continuation are its only callers, each of which applies it
-- once.  It descends on the path at a frame and on the floor at a
-- sink; every inner it subscribes is `rawInner`'s.

-- THE FOLD'S STACKED INNERS OWE WHAT STANDING GROUND GETS FREE FROM THE
-- ROOT: the base's fold, connecting nothing, writes nd node of a frame
-- stacked above it.  The invariant carrying it is ONE TERMINUS PER NODE:
-- every registry row through a frame's node ends where that frame's own
-- path ends, at the root or at one sink.  A flattener's frames sit only on
-- its outer's path and its inners', which share its continuation, and a
-- row registered under an inner is that inner's continuation with its
-- floor lowered, so nd row leaves the terminus it was made under.  A
-- base ending at the root reaches nd sink without a connect.  A base
-- ending at `j`'s sink reaches only rows on shares from `j` up, and a
-- row on a share sits above that share's index, so it never ends at
-- `j`'s sink, which is the one place a stacked frame's rows end.  The
-- state records nd terminus, so every ground reaching this fold owes
-- the rule.

-- WITHOUT THE RULE THE FOLD DIVERGES, from a state nd run reaches.  A
-- merge limited to one lane, busy, with an inner queued, is finished
-- under an inner frame whose path ends at a share's sink, and the
-- share's registry holds a row mapping every value to that same inner
-- through the merge's own outer frame to the root.  The finish drains
-- the queued inner; its value fans out through the row and is queued
-- again behind the lane it holds; its end finishes and drains it once
-- more, and nothing on that cycle is smaller.  The merge's node then
-- has a row ending at the root and an inner frame ending at the sink,
-- which is what the rule forbids.  Read off the relation, not
-- machine-checked.

-- The invariant held on a swept corpus of 1.5M programs, run on the
-- side branch's evaluator over this relation: at every frame step whose
-- continuation fanned out or connected (4.4M fan-out, 107k connect), the
-- frame's nodes came through the rest of the fold unchanged in shape and
-- value, and every registry row through them ended at the frame's own
-- terminus.  The same check fed the pre-step state at take's frame
-- flagged 1.4k writes on 20k programs, so it can fire.  Steps with
-- neither a fan-out nor a connect were not checked, and 63 deep
-- recursive programs timed out uncovered.
rawFold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
          (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
        → (κ : Path Γ ℓ u t) (now : Tick) (vals : List (Val Γ u)) (fin : Bool)
          (sched : Sched Γ) (st : EvalSt e) → Room m sched st → Sound κ sched st
        → Σ (Stream Γ t × Sched Γ × EvalSt e) (foldPath⇓ {e = e} now κ vals fin sched st)

-- a frame's step, then the fold of the path below it
rawAfter : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u lo ℓ ℓ′}
           (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
         → (f : Frame Γ s u) (le′ : ℓ ≤ ℓ′) (κ : Path Γ ℓ′ u t) {now : Tick}
           {vals : List (Val Γ s)} {fin : Bool} {sched : Sched Γ} {st : EvalSt e}
           (r : Stream Γ t × List (Val Γ u) × Bool × Sched Γ × EvalSt e)
         → stepFrame⇓ {e = e} now f κ vals fin sched st r
         → Room m (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
         → Sound κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
         → Σ (Stream Γ t × Sched Γ × EvalSt e) (foldPath⇓ {e = e} now (f ↠[ le′ ] κ) vals fin sched st)

-- an inner's exit frame reacting to what the inner sent
rawReact : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ ℓ′}
           (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ′) → Acc _<_ m
         → (op : AllOp) (nid inst : NodeId) (le′ : ℓ ≤ ℓ′) (κ : Path Γ ℓ′ s t) (now : Tick)
           (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → Sound (from-inner op nid inst ↠[ le′ ] κ) sched st
         → (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h
         → ∀ {b} → Acc _<_ b → waiting h ≤ b
         → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
             (λ r → stepFrame⇓ {e = e} now (from-inner op nid inst) κ vals fin sched st r
                  × Sound κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))))

-- and finishing it once nd chain under the instance is registered, at
-- the node the store reads back
rawFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s lo ℓ ℓ′}
            (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ′) → Acc _<_ m
          → (op : AllOp) (nid inst : NodeId) (le′ : ℓ ≤ ℓ′) (κ : Path Γ ℓ′ s t) (now : Tick)
            (vals : List (Val Γ s)) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
          → Sound (from-inner op nid inst ↠[ le′ ] κ) sched st
          → (h : Maybe (NodeState Γ)) → ∀ {b} → Acc _<_ b → waiting h ≤ b
          → Σ (Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e)
              (λ r → innerFinish⇓ {e = e} op nid inst κ now vals sched st h r
                   × Sound κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))))

-- a share's fan-out, one value to every admitted row before the next
rawWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} (i : Fin n)
          (ac : Acc _<_ (n ∸ suc (toℕ i))) → Acc _<_ m
        → (now : Tick) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
          (sched : Sched Γ) (st : EvalSt e) → Room m sched st → Rule sched st
        → Σ (Stream Γ t × Sched Γ × EvalSt e)
            (λ r → shareWalk⇓ {e = e} now i vals fin sched st r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))

-- one delivery to every row admitted at its start
rawGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} (i : Fin n)
        (ac : Acc _<_ (n ∸ suc (toℕ i))) → Acc _<_ m
      → (now : Tick) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
        (ps : List (RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t))
        (sched : Sched Γ) (st : EvalSt e) → Room m sched st → Rule sched st
      → (∀ {a} → a ∈ ps → Sound (proj₂ a) sched st)
      → (∀ {a b} → a ∈ ps → b ∈ ps → Agree (proj₂ a) (proj₂ b))
      → Σ (Stream Γ t × Sched Γ × EvalSt e)
          (λ r → shareGo⇓ {e = e} now i vals fin ps sched st r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))

rawFold ac le aM root now vals fin sched st rm so = _ , fold-root
rawFold {n = n} (acc rs) le aM (share-sink i below) now vals fin sched st rm so =
  let (r , w , _) = rawWalk i (rs (∸-monoʳ-< (s≤s (≤-trans le below)) (toℕ<n i))) aM now vals fin
                      sched (shareDying i fin st) (room-keeps (shareDying-keeps i fin sched st) rm)
                      (dying-rule i fin sched st (ruled so))
  in _ , fold-sink (disp w)
rawFold ac le aM (map-f fn ↠[ le′ ] κ) now vals fin sched st rm so =
  rawAfter ac le aM (map-f fn) le′ κ _ step-map rm (drop-ot (map-f fn) le′ κ so)
rawFold ac le aM (scan-f fn k ↠[ le′ ] κ) now vals fin sched st rm so =
  let sd = step-scan {fn = fn} {nid = k} {κ = κ} {now = now} {vals = vals} {fin = fin} {sched = sched} {st = st}
  in rawAfter ac le aM (scan-f fn k) le′ κ _ sd (room-keeps (stepFrame-keeps sd) rm)
       (drop-ot (scan-f fn k) le′ κ (step-kept le′ sd so))
rawFold ac le aM (take-f k ↠[ le′ ] κ) now vals fin sched st rm so =
  let sd = step-take {nid = k} {κ = κ} {now = now} {vals = vals} {fin = fin} {sched = sched} {st = st}
  in rawAfter ac le aM (take-f k) le′ κ _ sd (room-keeps (stepFrame-keeps sd) rm)
       (drop-ot (take-f k) le′ κ (step-kept le′ sd so))
rawFold ac le aM (batchSync-f k ↠[ le′ ] κ) now vals fin sched st rm so =
  let sd = step-batchSync {nid = k} {κ = κ} {now = now} {vals = vals} {fin = fin} {sched = sched} {st = st}
  in rawAfter ac le aM (batchSync-f k) le′ κ _ sd (room-keeps (stepFrame-keeps sd) rm)
       (drop-ot (batchSync-f k) le′ κ (step-kept le′ sd so))
rawFold ac le aM (from-inner op nid inst ↠[ le′ ] κ) now vals fin sched st rm so =
  let (r , sd , so′) = rawReact ac (≤-trans le le′) aM op nid inst le′ κ now vals fin sched st rm so
                         _ refl (<-wellFounded _) ≤-refl
  in rawAfter ac le aM (from-inner op nid inst) le′ κ r sd (room-keeps (stepFrame-keeps sd) rm) so′
rawFold ac le aM (thru-outer op nid ↠[ le′ ] κ) now vals fin sched st rm so =
  let (r , w , so₁ , _) = rawThru ac (≤-trans le le′) aM op nid κ now vals sched st rm
                            (drop-ot (thru-outer op nid) le′ κ so)
                            (head-on (thru-outer op nid) le′ κ nid (self-node nid []) so)
  in rawAfter ac le aM (thru-outer op nid) le′ κ _ (step-thru-outer w)
       (room-keeps (thruWrap-keeps op nid fin (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) (room-keeps (thruWalk-keeps w) rm))
       (wrap-ot op nid fin (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) so₁)

rawAfter ac le aM f le′ κ {now} (_ , vals′ , fin′ , sched₁ , st₁) sd rm so =
  let (r , d) = rawFold ac (≤-trans le le′) aM κ now vals′ fin′ sched₁ st₁ rm so
  in _ , fold-step sd d

rawReact ac le aM op nid inst le′ κ now vals false sched st rm so h eq aq wq =
  _ , step-from-inner react-false , drop-ot (from-inner op nid inst) le′ κ so
rawReact ac le aM op nid inst le′ κ now vals true sched st rm so h eq aq wq =
  by-bool (any (aliveThroughᶠ inst st) (EvalSt.registry st))
    (λ eqa →
      let (r , fd , so′) = rawFinish ac le aM op nid inst le′ κ now vals sched st rm so h aq wq
      in r , step-from-inner (react-dead eqa (subst (λ x → innerFinish⇓ op nid inst κ now vals sched st x r) (sym eq) fd)) , so′)
    (λ eqa → _ , step-from-inner (react-alive eqa) , drop-ot (from-inner op nid inst) le′ κ so)

rawFinish {s = s} ac le aM op nid inst le′ κ now vals sched st rm so h aq wq
  with finishUsable op s inst h in equ
...   | false = _ , finish-nil equ , drop-ot (from-inner op nid inst) le′ κ so
...   | true with finishing op s inst h equ
...     | f-switch c od eqc = _ , finish-switch-clear eqc , sub-ot (λ r∈ → r∈) ≤-refl (drop-ot (from-inner op nid inst) le′ κ so)
...     | f-exhaust act od  = _ , finish-exhaust-clear , sub-ot (λ r∈ → r∈) ≤-refl (drop-ot (from-inner op nid inst) le′ κ so)
...     | f-merge lim act q od =
          let fi  = from-inner {s = s} op nid inst
              so₀ = drop-ot fi le′ κ so
              (r₁ , d₁) = rawFold ac le aM κ now vals false sched st rm so₀
              so₁ = fold-kept d₁ so₀ (fi ↠[ le′ ] κ) so (λ _ _ _ → refl)
              (r₂ , d₂ , so₂ , _) = rawDrain ac le aM nid κ now q lim (pred act) od q
                                      (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) (room-keeps (foldPath-keeps d₁) rm)
                                      (drop-ot fi le′ κ so₁) (head-on fi le′ κ nid (self-node nid (inst ∷ [])) so₁) aq wq
          in _ , finish-all-drain {act = act} d₁ d₂ , sub-ot (λ r∈ → r∈) ≤-refl so₂

rawWalk i ac aM now [] false sched st rm ru = _ , walk-nil , ru
rawWalk i ac aM now [] true sched st rm ru =
  let (r , g , ru′) = rawGo i ac aM now [] true (shareAdmit i (EvalSt.registry st)) sched (shareSpend i st) rm
                        (sub-rule (λ r∈ → r∈) ≤-refl ru)
                        (λ a∈ → sub-ot (λ r∈ → r∈) ≤-refl (admit-ot i sched st ru a∈)) (admit-agree i st (termini ru))
  in r , walk-end g , ru′
rawWalk i ac aM now (v ∷ vs) fin sched st rm ru =
  let (r₁ , g , ru₁) = rawGo i ac aM now (v ∷ []) false (shareAdmit i (EvalSt.registry st)) sched st rm ru
                         (admit-ot i sched st ru) (admit-agree i st (termini ru))
      (r₂ , w , ru₂) = rawWalk i ac aM now vs fin (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁))
                         (room-keeps (shareGo-keeps g) rm) ru₁
  in _ , walk-more g w , ru₂

rawGo i ac aM now vals fin [] sched st rm ru ok ag = _ , go-nil , ru
rawGo i ac aM now vals fin ((rid , p) ∷ ps) sched st rm ru ok ag =
  by-bool (any (_≡ᵇ rid) (EvalSt.cancelled st)) (λ eqc →
  let so = sub-ot (λ r∈ → r∈) ≤-refl (ok (here refl))
      (r₁ , d) = rawFold ac ≤-refl aM p now vals fin sched
                   (record st { delivered = rid ∷ EvalSt.delivered st }) rm so
      (r₂ , g , ru₂) = rawGo i ac aM now vals fin ps (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁))
                         (room-keeps (foldPath-keeps d) rm)
                         (ruled (fold-kept d so p so (λ _ _ _ → refl)))
                         (λ {a} a∈ → fold-kept d so (proj₂ a) (sub-ot (λ r∈ → r∈) ≤-refl (ok (there a∈)))
                                       (ag (here refl) (there a∈)))
                         (λ a∈ b∈ → ag (there a∈) (there b∈))
  in _ , go-live eqc d g , ru₂)
  (λ eqc →
  let (r , g , ru′) = rawGo i ac aM now vals fin ps sched st rm ru (λ a∈ → ok (there a∈))
                        (λ a∈ b∈ → ag (there a∈) (there b∈))
  in r , go-cut eqc g , ru′)

------------------------------------------------------------------
-- THE ARMS, STATED.
------------------------------------------------------------------

-- THE EXPRESSION FACE DISPATCHES ON THE FORMER.  The formers that push
-- no frame and fold at most once are bodies here; every former that
-- pushes a frame, and the slot arm, is a leaf below, stated at full
-- strength and ported from the recovery pointer above.
redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) → Arm b

-- THE SLOT ARM MIRRORS THE MACHINE'S CASE SPLIT ON THE SLOT: below the
-- floor it folds the end and nothing else; at a scripted slot it folds
-- what the script says with `red-val` beside every value; at a
-- shared slot it joins, or spends the room and connects.
red-input : ∀ {n} {Γ : Ctx n} {Θ} (i : Fin n) (ρ : Env Γ Θ) (k : ℕ)
          → T (toℕ i <ᵇ k) → Acc _<_ k → ∀ {m} → Acc _<_ m
          → Red {Γ = Γ} m (obs (lookup Γ i)) (Θ , input i , ρ)

-- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
-- former hands the recursion back to the expression face.
redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
           (ρ : Env Γ Θ) {m} → RedEnv m ρ
         → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
         → Acc _<_ (gsizeᵗ tm) → Acc _<_ m → Red m u (evalWith tm ρ)

redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u} (ts : List (Tm Γ [] [] Θ u))
            (ρ : Env Γ Θ) {m} → RedEnv m ρ
          → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
          → Acc _<_ (gsizeᵗˢ ts) → Acc _<_ m
          → All (Red m u) (map (λ tm → evalWith tm ρ) ts)

-- THE TOP LINE: every closure whose environment is reducible is
-- itself reducible, which is the face above with both accessibilities
-- seeded at their own subjects and the room's taken as given.
reducible : ∀ {n} {Γ : Ctx n} {Θ t} {m} → Acc _<_ m
          → (b : Exp Γ [] [] Θ t) (ρ : Env Γ Θ)
          → RedEnv m ρ → Red {Γ = Γ} m (obs t) (Θ , b , ρ)

-- AND EVERY RUNTIME VALUE IS REDUCIBLE AT EVERY CEILING IT IS ASKED
-- AT.  A value at observable type IS a body paired with an
-- environment, and an entry of that environment at observable type is
-- another such value -- so nothing could be claimed of the pair that
-- is not already claimed of its entries.  The descent is not on the
-- value and never was; it is on the accessibility this takes, which
-- every caller has either peeled or been handed by something that
-- did.

-- THE PAIR ITSELF DESCENDS ON THE VALUE: an environment is a component
-- of the observable value it is read out of, and an entry a component
-- of the environment.
red-val : ∀ {n} {Γ : Ctx n} {m} → Acc _<_ m → (t : Ty) (v : Val Γ t) → Red m t v

red-env : ∀ {n} {Γ : Ctx n} {m} → Acc _<_ m → {Θ : List Ty} (ρ : Env Γ Θ) → RedEnv m ρ

------------------------------------------------------------------
-- THE LEAVES: EVERY ARM THAT PUSHES A FRAME, AND THE SLOT ARMS.
------------------------------------------------------------------

-- EACH IS THE OLD BODY WITH TWO ADDITIONS: it answers with the trace
-- of the calls it made, and where it used to peel an exit frame it now
-- translates its source's trace through the frame it pushed and
-- replays the continuation it was handed.  The replay is the one new
-- piece of machinery the port owes, and it is shared: a fold applied
-- to each recorded call in order.

-- THE MAP ARM.  It pushes the map frame live over whatever ground its
-- caller stands on, subscribes its source under it, and answers with
-- the source's trace translated through the frame.
red-map : ∀ {n} {Γ : Ctx n} {Θ s t} (f : Tm Γ [] [] (s ∷ Θ) t)
            (b : Exp Γ [] [] Θ s) → Arm (mapᵉ f b)

-- the map frame's transport of candidates: the body's candidate under
-- the extended environment, funded by the term's own size, which the
-- arm peels off its own before handing it over
red-mapFn : ∀ {n} {Γ : Ctx n} {Θ s t} (f : Tm Γ [] [] (s ∷ Θ) t)
              (b : Exp Γ [] [] Θ s) (ρ : Env Γ Θ) {m} → RedEnv m ρ
            → (k : ℕ) → T (inputsBelowᵉ k (mapᵉ f b)) → Acc _<_ k
            → Acc _<_ (gsizeᵗ f) → Acc _<_ m
            → ∀ {v} → Red m s v → Red m t (applyClo (_ , f , ρ) v)

-- THE TAKE ARM.  Its frame holds a count read off the store; the
-- translation truncates the column as the frame's dispatch does.
red-take : ∀ {n} {Γ : Ctx n} {Θ t} (c : Tm Γ [] [] Θ natᵗ)
             (b : Exp Γ [] [] Θ t) → Arm (takeᵉ c b)

-- THE BATCHSYNC ARM, WHICH IS THE ONE THE TRACE EXISTS FOR.  The
-- bracket is opened by the install and closed when the subscribe call
-- returns; the arm lowers the bit and folds its frame's successor once
-- more with nothing arriving, and that successor is the replay of the
-- continuation it built over the trace its source answered with.
red-batchSync : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) → Arm (batchSyncᵉ b)

-- THE SCAN ARM.  Its frame holds the accumulator and its candidate;
-- the translation folds the step's candidate along the column.
red-scan : ∀ {n} {Γ : Ctx n} {Θ s t} (f : Tm Γ [] [] ((t ×ᵗ s) ∷ Θ) t)
             (z : Tm Γ [] [] Θ t) (b : Exp Γ [] [] Θ s) → Arm (scanᵉ f z b)

-- THE FLATTENERS.  Each subscribes its source under the outer frame
-- holding the fresh node, and the outer frame's step is a fold over
-- the from-inner frame's step: an inner subscribed in walk order is
-- vouched by the value's own candidate, and the candidate never
-- re-enters itself, because on standing ground a walk-order inner
-- finishes with nothing queued.  Bodies at the foot of the file, past
-- the fold over a subscribing frame.
red-mergeAll : ∀ {n} {Γ : Ctx n} {Θ t} (lim : Maybe ℕ)
                 (b : Exp Γ [] [] Θ (obs t)) → Arm (mergeAllᵉ lim b)
red-switchAll : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ (obs t)) → Arm (switchAllᵉ b)
red-exhaustAll : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ (obs t)) → Arm (exhaustAllᵉ b)

-- THE SHARED SLOT, AND THE ONE EDGE OF THE CYCLE THAT SPENDS THE ROOM.
-- A share's definition is an arbitrary expression standing in no
-- relation to `input i`, so it cannot be reached by any descent on the
-- TERM; the telescope's side condition charges it against the input
-- ceiling `toℕ i` instead, and that is the descent the connect makes.
-- The def is subscribed at the sink AT THE CALLER'S OWN CEILING, on
-- FALLEN ground: the connect is what drops the count under the
-- ceiling, so the witness is in hand before the def is subscribed, and
-- every fold of the sink's continuation peels the room's
-- accessibility on it and reads the store raw at the lower ceiling.
-- The def's values fan out over the registry, through paths no
-- subscribe built.  The trigger's own continuation is not called at
-- all -- the trigger receives its values through the row it
-- registered -- so its trace records only the fall, and the fall at
-- the state the def's subscribe left is the def's own answer.
red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ S}
      (i : Fin n) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (ρ : Env Γ Θ)
      (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo) (pre : Pre κ)
    → ∀ {m} (rp : RP {e = e} m (Red m (lookup Γ i)) S κ pre) (s : S)
    → (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → ∀ (st : EvalSt e) → Acc _<_ m → Room m sched st → PreHolds m κ pre sched st
    → Σ (Stream Γ t × Sched Γ × EvalSt e)
        (λ r → subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r
             × Σ (Trace {e = e} m (Red m (lookup Γ i)) S κ pre rp s)
                 (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                       × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))

-- THE FALLEN CONTINUATION, WHICH IS THE RAW ONE REBUILT AT THE PEELED
-- CEILING ON EVERY CALL.  It holds no candidates, so nothing it holds
-- can be stale; the store is the only source of truth after a connect,
-- and this is the fold that reads it as such.  The accessibility it
-- peels is the one the arm that built it was funded by, and the peel
-- is exactly the fallen witness the caller supplies -- the same
-- descent the connect's fan-out and the old hop's guard made, at the
-- same place, with the dead branch gone because a caller without the
-- witness cannot call it.  Its successor is itself, and the witness
-- survives the fold because a fold keeps the two fields the room
-- reads.
fallenRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
           (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
         → (κ : Path Γ ℓ u t) → RP {e = e} m (Red m u) ⊤ κ fallen
fold (fallenRP ac le (acc rsM) κ) tt now vals _ fin sched st rm (grounded fell so) =
  let (r , d) = rawFold ac le (rsM fell) κ now vals fin sched st ≤-refl so
  in ans (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) d fallen
         (grounded (fell-keeps (foldPath-keeps d) fell) (fold-sound d so)) tt (fallenRP ac le (acc rsM) κ) tt

-- THE LIVE FOLD OVER A PURE FRAME.  It steps at what it holds, folds
-- the path above at the step's state with the candidates through the
-- step, and hands back its successor at what it now holds -- standing
-- where the path still stands, fallen where the path fell.  It needs
-- the room's accessibility for the fall alone, since the fallen fold
-- is funded by it.

-- THE SUCCESSOR IS GUARDED, NOT SMALLER: it is a field of the answer a
-- `fold` copattern of the coinductive `RP` returns, so each unfolding
-- is one fold and the guardedness check holds the pair.
liveRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
         {f : Frame Γ s u} {Held : HeldF f → Set₁}
         (le : lo ≤ ℓ) → Acc _<_ m → FrameStep {e = e} f (Red m s) (Red m u) Held
       → (h : HeldF f) → Held h → (κ : Path Γ ℓ u t) (pfs : PreFs κ)
       → RP {e = e} m (Red m u) S κ (standing pfs)
       → RP {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs))

-- the frame's successor over the path's, by the path's ground
headNext : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
           {f : Frame Γ s u} {Held : HeldF f → Set₁}
           (le : lo ≤ ℓ) → Acc _<_ m → FrameStep {e = e} f (Red m s) (Red m u) Held
         → (h : HeldF f) → Held h → (κ : Path Γ ℓ u t) (p : Pre κ)
         → RP {e = e} m (Red m u) S κ p
         → RP {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p)

------------------------------------------------------------------
-- THE BODIES.
------------------------------------------------------------------

redExpAcc (input i) ρ rρ k ok aK a aM = red-input i ρ k ok aK aM
redExpAcc (ofᵉ ts) ρ rρ k ok aK (acc rs) aM κ pre rp s now sched st rm h =
  let c  = call now (map (λ tm → evalWith tm ρ) ts)
             (ofColumn κ pre (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl) aM)) true sched st rm h
      an = apply rp s c
  in _ , subs-of (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
redExpAcc emptyᵉ ρ rρ k ok aK a aM κ pre rp s now sched st rm h =
  let c  = call now [] (ofColumn κ pre []) true sched st rm h
      an = apply rp s c
  in _ , subs-empty (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
redExpAcc (mapᵉ f b)        ρ rρ k ok aK a aM = red-map f b ρ rρ k ok aK a aM
redExpAcc (takeᵉ c b)       ρ rρ k ok aK a aM = red-take c b ρ rρ k ok aK a aM
redExpAcc (batchSyncᵉ b)    ρ rρ k ok aK a aM = red-batchSync b ρ rρ k ok aK a aM
redExpAcc (scanᵉ f z b)     ρ rρ k ok aK a aM = red-scan f z b ρ rρ k ok aK a aM
redExpAcc (mergeAllᵉ lim b) ρ rρ k ok aK a aM = red-mergeAll lim b ρ rρ k ok aK a aM
redExpAcc (switchAllᵉ b)    ρ rρ k ok aK a aM = red-switchAll b ρ rρ k ok aK a aM
redExpAcc (exhaustAllᵉ b)   ρ rρ k ok aK a aM = red-exhaustAll b ρ rρ k ok aK a aM
redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
                         (rs (subst (_< suc (gsizeᵉ body))
                                    (sym (gsize-unfoldμ body)) ≤-refl)) aM
                         κ pre rp s₀ now sched st rm h
  in r , subs-μ d , rest
redExpAcc (varᵉ ()) ρ rρ k ok aK a aM
redExpAcc {t = u} (deferᵉ body) ρ {m} rρ k ok aK a aM {lo = lo} κ pre rp s₀ now sched st rm h =
  let nid = freshId nodeᵏ (Sched.mint sched)
      st′ = register (freshId regᵏ (Sched.mint sched)) (atDyn (freshId sourceᵏ (Sched.mint sched)) lo)
                     (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ)
                     (installNode nid (mergeAll-st nothing 0 [] false) st)
  in _ , subs-defer refl refl refl refl , []ᵗ
     , holds-step {m = m} κ pre (λ k′ _ k< → below (pres-write st st′ _ refl ≤-refl) k′ k<) (n≤1+n _)
         (λ (x : Fell m sched st) → x)
         (λ so → register-sound {sched = sched} {st = installNode nid (mergeAll-st nothing 0 [] false) st}
                   (freshId regᵏ (Sched.mint sched)) (atDyn (freshId sourceᵏ (Sched.mint sched)) lo)
                   (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ) (n≤1+n _) refl
                   (λ k′ on → [ (λ a → inj₂ (subst (λ j → nodeCt sched ≤ j × j < suc (nodeCt sched)) (node-eq a) (≤-refl , ≤-refl)))
                              , inj₁ ] (∨-T on))
                   (λ so′ → (λ k′ a onκ → <-irrefl (sym (node-eq a)) (fresh-path so′ k′ onκ)) , distinct so′)
                   (sub-ot {st′ = installNode nid (mergeAll-st nothing 0 [] false) st} (λ r∈ → r∈) ≤-refl so))
         h
     , kept-step κ pre (pres-write st st′ _ refl ≤-refl) (n≤1+n _)
         (ends-register {κ = κ} {sched = sched} {st = installNode nid (mergeAll-st {t = u} nothing 0 [] false) st}
            (freshId regᵏ (Sched.mint sched)) (atDyn (freshId sourceᵏ (Sched.mint sched)) lo)
            (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ)
            (λ k′ on → [ (λ a → inj₂ (subst (nodeCt sched ≤_) (node-eq a) ≤-refl)) , inj₁ ] (∨-T on)))
redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h
  with (let src = freshId sourceᵏ (Sched.mint sched)
        in redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) aM κ pre rp s₀ now
             (record sched
                { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
             st rm (holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x) (sub-ot (λ r∈ → r∈) ≤-refl) h))
... | (r , d , tr , hl , kp) = r , subs-mint refl d , tr , hl , kept-in κ (endPre tr) refl kp

-- the live fold: step, fold above, stand on what came back
fold (liveRP {f = f} le aM fs h rh κ pfs rp) s now vals col fin sched st rm hs =
  let r  = step fs h vals fin sched st
      an = apply rp s (headCall {le = le} fs h rh κ pfs (call now vals col fin sched st rm hs))
      so = step-kept le (step-⇓ fs {κ = κ} {now = now} h vals fin sched st (proj₁ (proj₁ (ground hs)))) (sounds hs)
  in ans (out an) (Ans.sched′ an) (Ans.st′ an)
         (fold-step (step-⇓ fs h vals fin sched st (proj₁ (proj₁ (ground hs)))) (der an))
         (headPre (held r) (Ans.pre′ an))
         (headHolds _ le κ (held r)
           ( step-cons fs h vals fin sched st (proj₁ (proj₁ (ground hs)))
           , subst (λ ct → All (_< ct) _) (sym (step-ct fs h vals fin sched st)) (proj₂ (proj₁ (ground hs))) )
           (proj₁ (proj₂ (ground hs))) so (Ans.pre′ an) (Ans.holds′ an) (kept an)
           (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
         (headKept _ le κ (step-off fs h vals fin sched st) (step-ct fs h vals fin sched st)
           (ends-sub (f ↠[ le ] κ) {sched = sched} {st = st} {st′ = st″ r} (step-reg fs h vals fin sched st))
           (Ans.pre′ an) (kept an) (held r))
         (headNext le aM fs (held r) (proj₂ (step-red fs col rh)) κ (Ans.pre′ an) (next an))
         (Ans.s′ an)

headNext le aM fs h rh κ (standing pfs) rp = liveRP le aM fs h rh κ pfs rp
headNext {n = n} {lo = lo} le aM fs h rh κ fallen rp =
  dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ))

-- THE TRANSLATION OF A SOURCE'S TRACE THROUGH THE LIVE FRAME IT WAS
-- SUBSCRIBED UNDER: each call becomes the call the frame made above
-- it, and the walk stops where the path fell, since past the fall the
-- frame's fold reads the store and calls nothing it was handed.  It
-- descends on the trace: a call-bearing clause peels one call, and the
-- dispatch by ground re-enters at what that peel left.
translate : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
            {f : Frame Γ s u} {Held : HeldF f → Set₁}
            (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
            (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
            (rp : RP {e = e} m (Red m u) S κ (standing pfs)) {s₀ : S}
          → Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs)) (liveRP le aM fs h rh κ pfs rp) s₀
          → Trace {e = e} m (Red m u) S κ (standing pfs) rp s₀
translate-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
               {f : Frame Γ s u} {Held : HeldF f → Set₁}
               (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
               (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (p : Pre κ)
               (rp : RP {e = e} m (Red m u) S κ p) {s₀ : S}
             → Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p) (headNext le aM fs h rh κ p rp) s₀
             → Trace {e = e} m (Red m u) S κ p rp s₀
translate le aM fs h rh κ pfs rp []ᵗ = []ᵗ
translate {n = n} {ℓ = ℓ} le aM fs h rh κ pfs rp (fellᵗ _ s′) =
  fellᵗ (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ)) s′
translate le aM fs h rh κ pfs rp {s₀} (c ∷ᵗ tr) =
  headCall fs h rh κ pfs c
    ∷ᵗ translate-go le aM fs (held (step fs h (Call.vals c) (Call.fin c) (Call.sched c) (Call.st c)))
         (proj₂ (step-red fs (Call.col c) rh)) κ (Ans.pre′ an) (next an) tr
  where an = apply rp s₀ (headCall fs h rh κ pfs c)
translate-go le aM fs h rh κ (standing pfs) rp tr = translate le aM fs h rh κ pfs rp tr
translate-go le aM fs h rh κ fallen         rp tr = []ᵗ

-- a trace on the fallen fold ends fallen
fallen-stays : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ} {S : Set}
               (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) (aM : Acc _<_ m) (κ : Path Γ ℓ u t) {s₀ : S}
             → (tr : Trace {e = e} m (Red m u) S κ fallen (dropS (fallenRP ac le aM κ)) s₀)
             → endPre tr ≡ fallen
fallen-stays ac le (acc rsM) κ []ᵗ         = refl
fallen-stays ac le (acc rsM) κ (fellᵗ _ _) = refl
fallen-stays ac le (acc rsM) κ (c ∷ᵗ tr) = fallen-stays ac le (acc rsM) κ tr

-- and the translation ends where the source's trace did, one frame
-- down, with the frame holding candidates for what it holds there.  It
-- descends on the trace as the translation does.
-- STRUCTURAL SCC: translate-end translate-end-go
translate-end : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
                {f : Frame Γ s u} {Held : HeldF f → Set₁}
                (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
                (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
                (rp : RP {e = e} m (Red m u) S κ (standing pfs)) {s₀ : S}
              → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs)) (liveRP le aM fs h rh κ pfs rp) s₀)
              → Σ (HeldF f) (λ h″ → Held h″ × endPre tr ≡ headPre h″ (endPre (translate le aM fs h rh κ pfs rp tr)))
translate-end-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
                   {f : Frame Γ s u} {Held : HeldF f → Set₁}
                   (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
                   (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (p : Pre κ)
                   (rp : RP {e = e} m (Red m u) S κ p) {s₀ : S}
                 → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p) (headNext le aM fs h rh κ p rp) s₀)
                 → Σ (HeldF f) (λ h″ → Held h″ × endPre tr ≡ headPre h″ (endPre (translate-go le aM fs h rh κ p rp tr)))
translate-end le aM fs h rh κ pfs rp []ᵗ         = h , rh , refl
translate-end le aM fs h rh κ pfs rp (fellᵗ _ _) = h , rh , refl
translate-end le aM fs h rh κ pfs rp {s₀} (c ∷ᵗ tr) =
  translate-end-go le aM fs (held (step fs h (Call.vals c) (Call.fin c) (Call.sched c) (Call.st c)))
    (proj₂ (step-red fs (Call.col c) rh)) κ (Ans.pre′ an) (next an) tr
  where an = apply rp s₀ (headCall fs h rh κ pfs c)
translate-end-go le aM fs h rh κ (standing pfs) rp tr = translate-end le aM fs h rh κ pfs rp tr
translate-end-go {n = n} {lo = lo} le aM fs h rh κ fallen rp tr =
  h , rh , fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ) tr

-- THE MAP ARM'S BODY.  Over a standing path the frame goes on live and
-- the answer is the translation; over a fallen one the frame goes on
-- fallen, the source calls nothing the arm was handed, and the arm's
-- own trace is empty.
red-mapFn f b ρ rρ k ok aK aF aM {v} p =
  redTmAcc f (v ∷ᵉ ρ) (p , rρ) k (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK aF aM

red-map {s = s} f b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK
                                  (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
                                  (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) (standing (tt , pfs))
                                  (liveRP ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp)
                                  s₀ now sched st rm (grounded ((tt , []ᵃ) , (λ _ ()) , ground h) (push-sound (map-f (_ , f , ρ)) ≤-refl κ (sounds h) (λ k ())))
      (h″ , _ , eq) = translate-end ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
      tr′ = translate ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
  in r , subs-map d , tr′
   , unheadHolds (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′)
       (subst (λ p → PreHolds _ (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq hl)
   , unheadKept (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′) {sched} {sched} {st = st} {st₁ = st}
       (λ _ _ ()) ≤-refl (λ _ _ → refl) (λ _ _ _ ea → ea)
       (subst (λ p → Kept (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) p sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq kp)
red-map {n = n} {s = s} f b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK
                                  (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
                                  (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) fallen
                                  (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (map-f (_ , f , ρ) ↠[ ≤-refl ] κ))) s₀ now sched st rm
                                  (grounded (ground fell) (push-sound (map-f (_ , f , ρ)) ≤-refl κ (sounds fell) (λ k ())))
  in r , subs-map d , []ᵗ
    , unheadHolds (map-f (_ , f , ρ)) ≤-refl κ tt fallen
        (subst (λ p → PreHolds _ (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

-- and its ground, over a standing path
fresh-holds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo s u} (f : Frame Γ s u) (κ : Path Γ lo u t)
                (pfs : PreFs κ) (h : HeldF f) (ns : NodeState Γ) {sched : Sched Γ} {st : EvalSt e}
            → (∀ k → T (any (_≡ᵇ k) (frameNodes f)) → nodeCt sched ≡ k)
            → ConsistentF f h (installNode (nodeCt sched) ns st) → FreshF (suc (nodeCt sched)) f
            → PreHolds m κ (standing pfs) sched st
            → PreHolds m (f ↠[ ≤-refl ] κ) (standing (h , pfs)) (bumpNode sched) (installNode (nodeCt sched) ns st)
fresh-holds f κ pfs h ns {sched} {st} one c fr hs =
  grounded
    ( (c , fr)
    , (λ k′ on onκ → fresh-apart κ pfs (ground hs) k′
                       (subst (λ j → T (nodeCt sched ≡ᵇ j)) (one k′ on) (subst T (sym (≡ᵇ-refl (nodeCt sched))) tt₀)) onκ)
    , holdsFs-step κ pfs (λ k′ on k< → set-above (nodeCt sched) k′ ns (EvalSt.nodes st) (<→≢ᵇ k<)) (n≤1+n _) (ground hs) )
    (fresh-sound f κ ns one (sounds hs))

-- THE TAKE ARM'S BODY.  A zero count completes on subscription and
-- never touches the source; otherwise the node goes in at the counter
-- and the arm is the map arm's over the take frame.
red-take c b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h with evalWith c ρ in eq
red-take c b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h | zero =
  let cl = call now [] (ofColumn κ pre []ᵃ) true sched st rm h
      an = apply rp s₀ cl
  in _ , subs-take-zero eq (der an) , cl ∷ᵗ []ᵗ , Ans.holds′ an , kept an
red-take c b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h | suc j =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok) aK
                                  (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c)))) aM
                                  (take-f (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just (take-st (suc j)) , pfs))
                                  (liveRP ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp)
                                  s₀ now (bumpNode sched) (installNode (nodeCt sched) (take-st (suc j)) st) rm
                                  (fresh-holds (take-f (nodeCt sched)) κ pfs (just (take-st (suc j))) (take-st (suc j)) (λ _ → node-eq)
                                     (lookup-set (nodeCt sched) (take-st (suc j)) (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) h)
      (h″ , _ , eq′) = translate-end ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp tr
      tr′ = translate ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp tr
  in r , subs-take-suc eq refl d , tr′
   , unheadHolds (take-f (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       (subst (λ p → PreHolds _ (take-f (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq′ hl)
   , unheadKept (take-f (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       {sched} {bumpNode sched} {st = st} {st₁ = installNode (nodeCt sched) (take-st (suc j)) st}
       (λ k′ k< on → subst T (<→≢ᵇ k<) (node-one {nodeCt sched} {k′} on)) (n≤1+n _)
       (λ k′ k< → set-above (nodeCt sched) k′ (take-st (suc j)) (EvalSt.nodes st) (<→≢ᵇ k<))
       (λ _ _ _ ea → ea)
       (subst (λ p → Kept (take-f (nodeCt sched) ↠[ ≤-refl ] κ) p (bumpNode sched)
                           (installNode (nodeCt sched) (take-st (suc j)) st) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq′ kp)
red-take {n = n} c b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell | suc j =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok) aK
                                  (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c)))) aM
                                  (take-f (nodeCt sched) ↠[ ≤-refl ] κ) fallen
                                  (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (take-f (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
                                  (bumpNode sched) (installNode (nodeCt sched) (take-st (suc j)) st) rm
                                  (grounded (ground fell) (fresh-sound (take-f (nodeCt sched)) κ (take-st (suc j)) (λ _ → node-eq) (sounds fell)))
  in r , subs-take-suc eq refl d , []ᵗ
    , unheadHolds (take-f (nodeCt sched)) ≤-refl κ nothing fallen
        (subst (λ p → PreHolds _ (take-f (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
           (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u} (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
         → (∀ {v} → Red m (u ×ᵗ s) v → Red m u (applyClo fn v))
         → FrameStep {e = e} (scan-f fn nid) (Red m s) (Red m u) (ScanHeld m u)
scanStep fn nid rf = record
  { step      = scanStepped fn nid
  ; step-⇓    = λ {_} {κ} {now} h vals fin sched st c →
                  subst (λ x → stepFrame⇓ now (scan-f fn nid) κ vals fin sched st
                                 (injectRoot (scanDispatch fn nid vals fin sched st x)))
                        c step-scan
  ; step-red  = λ {h} {vals} {fin} {sched} {st} ps rh → scanRed fn rf nid fin sched st h ps rh
  ; step-cons = λ h vals fin sched st c → scanCons fn nid vals fin sched st h c
  ; step-off  = λ h vals fin sched st k ne → scanOff fn nid vals fin sched st h k (head-off nid [] k ne)
  ; step-ct   = λ h vals fin sched st → scanCt fn nid vals fin sched st h
  ; step-reg  = λ h vals fin sched st r∈ → subst (_ ∈_) (scanReg fn nid vals fin sched st h) r∈ }

-- THE SCAN ARM'S BODY: the take arm's, with the cell seeded from the
-- seed's own candidate and the closure's funded by the term's size.
red-scan f z b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                                  (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z)) (m≤n+m _ (gsizeᵗ f))))) aM
                                  (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just (cell-st (evalWith z ρ)) , pfs))
                                  (liveRP ≤-refl aM
                                    (scanStep (_ , f , ρ) (nodeCt sched)
                                      (λ {v} p → redTmAcc f (v ∷ᵉ ρ) (p , rρ) k (∧ˡ (inputsBelowᵗ k f) _ ok) aK
                                                   (rs (s≤s (m≤m+n (gsizeᵗ f) _))) aM))
                                    (just (cell-st (evalWith z ρ)))
                                    (λ eq → subst (Red _ _) (cell-inj eq)
                                              (redTmAcc z ρ rρ k (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                                                 (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b)) (m≤n+m _ (gsizeᵗ f))))) aM))
                                    κ pfs rp)
                                  s₀ now (bumpNode sched) (installNode (nodeCt sched) (cell-st (evalWith z ρ)) st) rm
                                  (fresh-holds (scan-f (_ , f , ρ) (nodeCt sched)) κ pfs (just (cell-st (evalWith z ρ))) (cell-st (evalWith z ρ))
                                     (λ _ → node-eq) (lookup-set (nodeCt sched) (cell-st (evalWith z ρ)) (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) h)
      (h″ , _ , eq′) = translate-end ≤-refl aM
                          (scanStep (_ , f , ρ) (nodeCt sched)
                            (λ {v} p → redTmAcc f (v ∷ᵉ ρ) (p , rρ) k (∧ˡ (inputsBelowᵗ k f) _ ok) aK
                                         (rs (s≤s (m≤m+n (gsizeᵗ f) _))) aM))
                          (just (cell-st (evalWith z ρ)))
                          (λ eq → subst (Red _ _) (cell-inj eq)
                                    (redTmAcc z ρ rρ k (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                                       (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b)) (m≤n+m _ (gsizeᵗ f))))) aM))
                          κ pfs rp tr
      tr′ = translate ≤-refl aM
              (scanStep (_ , f , ρ) (nodeCt sched)
                (λ {v} p → redTmAcc f (v ∷ᵉ ρ) (p , rρ) k (∧ˡ (inputsBelowᵗ k f) _ ok) aK
                             (rs (s≤s (m≤m+n (gsizeᵗ f) _))) aM))
              (just (cell-st (evalWith z ρ)))
              (λ eq → subst (Red _ _) (cell-inj eq)
                        (redTmAcc z ρ rρ k (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                           (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b)) (m≤n+m _ (gsizeᵗ f))))) aM))
              κ pfs rp tr
  in r , subs-scan refl d , tr′
   , unheadHolds (scan-f (_ , f , ρ) (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       (subst (λ p → PreHolds _ (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq′ hl)
   , unheadKept (scan-f (_ , f , ρ) (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       {sched} {bumpNode sched} {st = st} {st₁ = installNode (nodeCt sched) (cell-st (evalWith z ρ)) st}
       (λ k′ k< on → subst T (<→≢ᵇ k<) (node-one {nodeCt sched} {k′} on)) (n≤1+n _)
       (λ k′ k< → set-above (nodeCt sched) k′ (cell-st (evalWith z ρ)) (EvalSt.nodes st) (<→≢ᵇ k<))
       (λ _ _ _ ea → ea)
       (subst (λ p → Kept (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) p (bumpNode sched)
                           (installNode (nodeCt sched) (cell-st (evalWith z ρ)) st) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq′ kp)
red-scan {n = n} f z b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                                  (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z)) (m≤n+m _ (gsizeᵗ f))))) aM
                                  (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) fallen
                                  (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
                                  (bumpNode sched) (installNode (nodeCt sched) (cell-st (evalWith z ρ)) st) rm
                                  (grounded (ground fell) (fresh-sound (scan-f (_ , f , ρ) (nodeCt sched)) κ (cell-st (evalWith z ρ)) (λ _ → node-eq) (sounds fell)))
  in r , subs-scan refl d , []ᵗ
    , unheadHolds (scan-f (_ , f , ρ) (nodeCt sched)) ≤-refl κ nothing fallen
        (subst (λ p → PreHolds _ (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
           (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

-- ONE FOLD THROUGH A PURE FRAME, AS A STAGE: on standing ground the
-- live fold, whose one call above is the head call; on fallen ground
-- the fallen fold, which calls nothing.  The frame's candidate is owed
-- only where the ground stands.
stepStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
              {f : Frame Γ s u} {Held : HeldF f → Set₁}
              (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
              (κ : Path Γ ℓ u t) (h : HeldF f)
              (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
              (now : Tick) (vals : List (Val Γ s)) → Column (f ↠[ le ] κ) (Red m s) (headPre h q) vals
          → (fin : Bool) {sched : Sched Γ} {st : EvalSt e} → Room m sched st
          → PreHolds m (f ↠[ le ] κ) (headPre h q) sched st
          → (∀ {pfs} → q ≡ standing pfs → Held h)
          → Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now (f ↠[ le ] κ) vals fin sched st (o , sc , s′)) q rp s₀ sched st
stepStage {f = f} le aM fs κ h (standing pfs) rp s₀ now vals col fin {sched} {st} rm hs rh =
  let r  = step fs h vals fin sched st
      c  = headCall {le = le} fs h (rh refl) κ pfs (call now vals col fin sched st rm hs)
      an = apply rp s₀ c
      d  = step-⇓ fs {κ = κ} {now = now} h vals fin sched st (proj₁ (proj₁ (ground hs)))
      so = step-kept le d (sounds hs)
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (fold-step d (der an)) (c ∷ᵗ []ᵗ) refl (held r)
       (headHolds f le κ (held r)
         ( step-cons fs h vals fin sched st (proj₁ (proj₁ (ground hs)))
         , subst (λ ct → All (_< ct) _) (sym (step-ct fs h vals fin sched st)) (proj₂ (proj₁ (ground hs))) )
         (proj₁ (proj₂ (ground hs))) so (Ans.pre′ an) (Ans.holds′ an) (kept an)
         (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
       (headKept f le κ (step-off fs h vals fin sched st) (step-ct fs h vals fin sched st)
         (ends-sub (f ↠[ le ] κ) {sched = sched} {st = st} {st′ = st″ r} (step-reg fs h vals fin sched st))
         (Ans.pre′ an) (kept an) (held r))
stepStage {n = n} {lo = lo} {f = f} le aM fs κ h fallen rp s₀ now vals col fin {sched} {st} rm (grounded fell so) rh =
  let an = fold (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (f ↠[ le ] κ)) tt now vals tt fin sched st rm
                (grounded fell so)
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) []ᵗ refl h
       (grounded (fell-keeps (foldPath-keeps (der an)) fell) (fold-sound (der an) so)) tt

-- THE BRACKET CLOSED.  Whatever the source's subscription left, the
-- arm lowers the bit at the frame's node and folds the frame once more
-- with nothing arriving, over the ground the source's trace ended on;
-- the flush's candidates are the buffer's, which the frame held.
batchFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {Θ u lo m} {S : Set}
                (b : Exp Γ [] [] Θ u) (ρ : Env Γ Θ) (aM : Acc _<_ m)
                (κ : Path Γ lo (u ×ᵗ listᵗ u) t) (pre : Pre κ)
                (rp : RP {e = e} m (Red m (u ×ᵗ listᵗ u)) S κ pre) (s₀ : S)
                (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
            → (A : Stage m (batchSync-f {s = u} (nodeCt sched)) ≤-refl κ
                     (λ o sc s′ → subscribeE⇓ {e = e} (Θ , b , ρ) (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) now
                                    (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st)
                                    (o , sc , s′))
                     pre rp s₀ (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st))
            → BatchHeld m u (Stage.hd A)
            → Σ (Stream Γ t × Sched Γ × EvalSt e)
                (λ r → subscribeE⇓ {e = e} (Θ , batchSyncᵉ b , ρ) κ now sched st r
                     × Σ (Trace {e = e} m (Red m (u ×ᵗ listᵗ u)) S κ pre rp s₀)
                         (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                               × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))
batchFinish {e = e} {Θ = Θ} {u = u} {m = m} b ρ aM κ pre rp s₀ now sched st rm A rhA =
  let nid = nodeCt sched
      x   = lookupNode nid (EvalSt.nodes (Stage.st′ A))
      W   = writeStage (batchSync-f {s = u} nid) ≤-refl κ (endPre (Stage.tr A)) (endRP (Stage.tr A)) (endS (Stage.tr A))
              nid (batchDown u x) (λ k ne → head-off nid [] k ne) (just (batchDown u x))
              (lookup-set nid (batchDown u x) (EvalSt.nodes (Stage.st′ A))) (Stage.hd A) (Stage.hl A)
      F   = stepStage ≤-refl aM (batchStep nid) κ (just (batchDown u x))
              (endPre (Stage.tr A)) (endRP (Stage.tr A)) (endS (Stage.tr A)) now []
              (ofColumn (batchSync-f nid ↠[ ≤-refl ] κ) (headPre (just (batchDown u x)) (endPre (Stage.tr A))) []ᵃ)
              false (room-keeps (subscribeE-keeps (Stage.dv A)) rm) (Stage.hl W)
              (λ {pfs} eq → downHeld u x
                 (subst (BatchHeld m u)
                    (sym (proj₁ (proj₁ (ground (subst (λ p → PreHolds m (batchSync-f nid ↠[ ≤-refl ] κ) (headPre (Stage.hd A) p)
                                                                  (Stage.sc A) (Stage.st′ A))
                                                      eq (Stage.hl A))))))
                    rhA))
      S′  = stage-seq {D₃ = λ o sc s′ → subscribeE⇓ {e = e} (Θ , batchSyncᵉ b , ρ) κ now sched st (o , sc , s′)} A
              (stage-rebase (batchSync-f nid) ≤-refl κ ≤-refl
                 (λ k _ ne → set-above nid k (batchDown u x) (EvalSt.nodes (Stage.st′ A)) (head-off nid [] k ne))
                 (λ _ _ _ ea → ea) F)
              (λ d₂ → subs-batchSync refl (Stage.dv A) d₂)
  in (Stage.out S′ , Stage.sc S′ , Stage.st′ S′) , Stage.dv S′ , Stage.tr S′
   , unheadHolds (batchSync-f nid) ≤-refl κ (Stage.hd S′) (endPre (Stage.tr S′)) (Stage.hl S′)
   , unheadKept (batchSync-f nid) ≤-refl κ (Stage.hd S′) (endPre (Stage.tr S′))
       {sched} {bumpNode sched} {st = st} {st₁ = installNode nid (batchSync-st {s = u} true [] false) st}
       (λ k′ k< on → subst T (<→≢ᵇ k<) (node-one {nid} {k′} on)) (n≤1+n _)
       (λ k′ k< → set-above nid k′ (batchSync-st {s = u} true [] false) (EvalSt.nodes st) (<→≢ᵇ k<))
       (λ _ _ _ ea → ea) (Stage.kp S′)

-- THE BATCHSYNC ARM'S BODY: the take arm's source subscription with
-- the bracket opened at the counter, then the bracket closed.
red-batchSync {t = u} b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h =
  let ((o₁ , sc₁ , st₁) , d , tr , hl , kp) = redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
                                                  (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just (batchSync-st {s = u} true [] false) , pfs))
                                                  (liveRP ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp)
                                                  s₀ now (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) rm
                                                  (fresh-holds (batchSync-f (nodeCt sched)) κ pfs (just (batchSync-st {s = u} true [] false))
                                                     (batchSync-st {s = u} true [] false) (λ _ → node-eq)
                                                     (lookup-set (nodeCt sched) (batchSync-st {s = u} true [] false) (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) h)
      (h″ , rh″ , eq′) = translate-end ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp tr
  in batchFinish b ρ aM κ (standing pfs) rp s₀ now sched st rm
       (stage o₁ sc₁ st₁ d
          (translate ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp tr)
          refl h″
          (subst (λ p → PreHolds _ (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) p sc₁ st₁) eq′ hl)
          (subst (λ p → Kept (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) p (bumpNode sched)
                              (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) sc₁ st₁) eq′ kp))
       rh″
red-batchSync {n = n} {t = u} b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell =
  let ((o₁ , sc₁ , st₁) , d , tr , hl , kp) = redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
                                                  (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) fallen
                                                  (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
                                                  (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) rm
                                                  (grounded (ground fell)
                                                     (fresh-sound (batchSync-f (nodeCt sched)) κ (batchSync-st {s = u} true [] false) (λ _ → node-eq) (sounds fell)))
  in batchFinish b ρ aM κ fallen rp s₀ now sched st rm
       (stage o₁ sc₁ st₁ d []ᵗ refl nothing
          (subst (λ p → PreHolds _ (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) p sc₁ st₁)
             (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
          tt)
       (λ ())

red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ pre rp s now sched st rm h
    with toℕ i <? lo
... | no  ¬below =
      let c  = call now [] (ofColumn κ pre []) true sched st rm h
          an = apply rp s c
      in _ , subs-floor (≮⇒≥ ¬below) (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ pre rp s now sched st rm h
    | yes below with Sched.slots sched i in slEq
...   | scripted {ok = oks} sc = red-scripted i ρ k ok (acc rsK) κ below pre rp s now sched sc {oks = oks} slEq st aM rm h
...   | shared d {ok = okd} =
        red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok)) ρ
          κ below pre rp s now sched slEq st aM rm h

-- THE SHARED SLOT'S BODY.  Spent: the end folds once through the
-- continuation.  Joined: one row is registered and nothing is folded,
-- so the ground stands where it stood.  Neither: the connect, which
-- registers the trigger's row, inserts the index, and subscribes the
-- def under the fallen sink; what comes back is the fall at the state
-- the def left, which is all a fallen answer owes.
red-input-shared {n = n} {lo = lo} i d {okd} aI ρ κ below pre rp s now sched slEq st aM rm h =
  by-bool (memberSource (toℕ i) (EvalSt.completedSources st))
    (λ doneEq → by-bool (memberSource (toℕ i) (EvalSt.connectedShares st))
      (λ connEq →
        let rid    = freshId regᵏ (Sched.mint sched)
            sched′ = record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
            st′    = register rid (atSlot i) (lowerFloor below κ)
                       (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
            fell′  = ≤-trans (unconn-insert (Sched.slots sched) (EvalSt.connectedShares st) i slEq connEq) rm
            (r , dv , tr , hl , _) =
              redExpAcc d []ᵉ tt (toℕ i) okd aI (<-wellFounded (gsizeᵉ d)) aM
                (share-sink i ≤-refl) fallen
                (dropS (fallenRP (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl)))
                tt now sched′ st′ (<⇒≤ fell′) (grounded fell′ (sink-sound i ≤-refl (ruled (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h))))))
        in r , subs-shared {κ = κ} {below = below} slEq
                (slot-connect {κ = κ} {below = below} doneEq connEq (connect {κ = κ} {below = below} refl dv))
          , fellᵗ (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM κ)) s
          , grounded
              (ground (subst (λ p → PreHolds _ (share-sink i ≤-refl) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
                        (fallen-stays (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl) tr) hl))
              (subscribe-kept dv (sink-sound i ≤-refl (ruled (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h))))) κ (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h))) (λ k ()))
          , tt)
      (λ connEq →
        _ , subs-shared {κ = κ} {below = below} slEq (slot-join {κ = κ} {below = below} doneEq connEq refl)
        , []ᵗ , holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x) (row-sound i below κ sched st) h
        , kept-step κ pre (pres (λ _ _ → refl)) ≤-refl
            (ends-register {κ = κ} {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
               (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on)))))
    (λ doneEq →
      let c  = call now [] (ofColumn κ pre []) true sched st rm h
          an = apply rp s c
      in _ , subs-shared {κ = κ} {below = below} slEq (slot-spent {κ = κ} {below = below} doneEq (der an))
         , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an)

------------------------------------------------------------------
-- THE TERM FACE.
------------------------------------------------------------------

redTmAcc (varᵗ x) ρ rρ k ok aK a aM = redLookup ρ rρ x
redTmAcc unit̂     ρ rρ k ok aK a aM = tt
redTmAcc (bool̂ b) ρ rρ k ok aK a aM = tt
redTmAcc (nat̂ j)  ρ rρ k ok aK a aM = tt
redTmAcc nilᵗ     ρ rρ k ok aK a aM = []
redTmAcc (consᵗ x xs) ρ rρ k ok aK (acc rs) aM =
    redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
      (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs)))) aM
  ∷ redTmAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
      (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x)))) aM
redTmAcc (foldᵗ l z f) ρ rρ k ok aK (acc rs) aM =
  let zfe  = inputsBelowᵗ k z ∧ inputsBelowᵗ k f
      okl  = ∧ˡ (inputsBelowᵗ k l) zfe ok
      rest = ∧ʳ (inputsBelowᵗ k l) zfe ok
      okz  = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
      okf  = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
  in redFoldVals f ρ
       (λ {x} {ac} rx rac →
          redTmAcc f (x ∷ᵉ ac ∷ᵉ ρ) (rx , rac , rρ) k okf aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))) aM)
       (redTmAcc l ρ rρ k okl aK
         (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))) aM)
       (redTmAcc z ρ rρ k okz aK
         (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                           (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))) aM)
redTmAcc (pairᵗ x y) ρ rρ k ok aK (acc rs) aM =
    redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
      (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y)))) aM
  , redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
      (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x)))) aM
redTmAcc (fstᵗ q) ρ rρ k ok aK (acc rs) aM =
  proj₁ (redTmAcc q ρ rρ k ok aK (rs ≤-refl) aM)
redTmAcc (sndᵗ q) ρ rρ k ok aK (acc rs) aM =
  proj₂ (redTmAcc q ρ rρ k ok aK (rs ≤-refl) aM)
redTmAcc (inlᵗ x) ρ rρ k ok aK (acc rs) aM = redTmAcc x ρ rρ k ok aK (rs ≤-refl) aM
redTmAcc (inrᵗ x) ρ rρ k ok aK (acc rs) aM = redTmAcc x ρ rρ k ok aK (rs ≤-refl) aM
redTmAcc (caseᵗ sc l r) ρ rρ k ok aK (acc rs) aM
  with evalWith sc ρ
     | redTmAcc sc ρ rρ k (∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok) aK
         (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r)))) aM
... | inj₁ x | q =
  redTmAcc l (x ∷ᵉ ρ) (q , rρ) k
    (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) (∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok)) aK
    (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                      (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc))))) aM
... | inj₂ y | q =
  redTmAcc r (y ∷ᵉ ρ) (q , rρ) k
    (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) (∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok)) aK
    (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                      (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc))))) aM
redTmAcc (ifᵗ c x y) ρ rρ k ok aK (acc rs) aM with evalWith c ρ
... | true  =
  redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok)) aK
    (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                      (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c))))) aM
... | false =
  redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok)) aK
    (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                      (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c))))) aM
redTmAcc (primᵗ add x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ sub x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ mul x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ eqᵖ x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ eqᵘ x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ ltᵖ x)  ρ rρ k ok aK a aM = tt
redTmAcc (primᵗ notᵖ x) ρ rρ k ok aK a aM = tt
redTmAcc (strmᵗ e) ρ rρ k ok aK (acc rs) aM = redExpAcc e ρ rρ k ok aK (rs ≤-refl) aM

redTmsAcc []       ρ rρ k ok aK a aM = []
redTmsAcc (x ∷ xs) ρ rρ k ok aK (acc rs) aM =
    redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
      (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs)))) aM
  ∷ redTmsAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
      (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x)))) aM

reducible aM b ρ rρ =
  redExpAcc b ρ rρ _ (ib-topᵉ b) (<-wellFounded _) (<-wellFounded (gsizeᵉ b)) aM

------------------------------------------------------------------
-- THE CANDIDATE AT VALUES.
------------------------------------------------------------------

-- THE RE-ENTRY IS THROUGH THE ACCESSIBILITY AND THROUGH NOTHING ELSE.
-- Every caller of this at an observable holds an `Acc` it did not
-- manufacture in place: the drain's came down the walk from a fold
-- that peeled the room; the guard's is the peel itself; the raw
-- fold's is the connect's.  So the cascade this starts is under a
-- component that has already dropped, or under a budget that has, and
-- the checker reads it off the argument.
red-val aM unitᵗ     v           = tt
red-val aM boolᵗ     v           = tt
red-val aM natᵗ      v           = tt
red-val aM uniqᵗ     v           = tt
red-val aM (s ×ᵗ u)  (a , b)     = red-val aM s a , red-val aM u b
red-val aM (s +ᵗ u)  (inj₁ a)    = red-val aM s a
red-val aM (s +ᵗ u)  (inj₂ b)    = red-val aM u b
red-val aM (listᵗ s) []          = []
red-val aM (listᵗ s) (x ∷ xs)    = red-val aM s x ∷ red-val aM (listᵗ s) xs
red-val aM (obs u)   (Θ , b , ρ) = reducible aM b ρ (red-env aM ρ)

red-env aM []ᵉ                 = tt
red-env aM (_∷ᵉ_ {s = s} v vs) = red-val aM s v , red-env aM vs

rawInner {u = u} ac le aM op nid κ now o sched st rm so nd h eq aq wq =
  let κ′  = from-inner {s = u} op nid (nodeCt sched) ↠[ ≤-refl ] κ
      so′ = fresh-inner op nid κ sched so nd
      (r , d , _) = red-val aM (obs u) o κ′ (standing (h , colsOf κ st))
                      (baseRP ac le aM op nid (nodeCt sched) κ (h , colsOf κ st) aq wq) tt now (bumpNode sched) st rm
                      (grounded (subst (λ x → HoldsFs κ′ (x , colsOf κ st) (bumpNode sched) st) eq
                                   (holdsOf κ′ (fresh-path so′) (distinct so′))) so′)
  in r , d

-- the base: its exit frame reacts at the budget its column pins, and the
-- path below folds raw
fold (baseRP ac le aM op nid inst κ (h , pfs) aq wq) tt now vals _ fin sched st rm (grounded hs so) =
  let wq′ = ceil-or (subst (λ x → waiting x ≤ _) (sym (proj₁ (proj₁ hs))) wq)
      (r₀ , sd , so₀) = rawReact ac le aM op nid inst ≤-refl κ now vals fin sched st rm so _ refl aq wq′
      (r , d) = rawAfter ac le aM (from-inner op nid inst) ≤-refl κ r₀ sd (room-keeps (stepFrame-keeps sd) rm) so₀
  in baseAns ac le aM op nid inst κ sched st rm so aq wq′ r d

-- the successor sits at the head of a `with` branch, where the `fold`
-- copattern guards it; under a lambda handed to an eliminator it is an
-- argument, which the copattern does not guard
baseAns ac le aM op nid inst κ sched st rm so aq wq (out , sched′ , st′) d
  with spend-or (fold-refill-spends op nid inst κ d so)
... | inj₁ sp =
  ans out sched′ st′ d fallen (grounded (<-≤-trans sp rm) (fold-sound d so)) tt
      (fallenRP ac le aM (from-inner op nid inst ↠[ ≤-refl ] κ)) tt
... | inj₂ (nsp , bd) =
  let κ′  = from-inner op nid inst ↠[ ≤-refl ] κ
      so′ = fold-sound d so
  in ans out sched′ st′ d (standing (colsOf κ′ st′))
         (grounded (holdsOf κ′ {sched = sched′} {st = st′} (fresh-path so′) (distinct so′)) so′)
         (raw-kept d nsp {pfs = colsOf κ′ st′})
         (baseRP ac le aM op nid inst κ (colsOf κ′ st′) aq (≤-trans bd wq)) tt

------------------------------------------------------------------
-- THE FOLD OVER A SUBSCRIBING FRAME, AND THE FLATTENER ARMS.
------------------------------------------------------------------

-- THE FOLD IS THE STEP APPLIED ONCE, and its successor is the same
-- fold at what the step left the frame holding -- standing where the
-- step's trace left the path standing, fallen where it fell.  The
-- successor is guarded by the `fold` copattern, as the live fold's is.
subRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
        (le : lo ≤ ℓ) (aM : Acc _<_ m) → SubStep {e = e} f G m
      → (h : HeldF f) → G h → (κ : Path Γ ℓ u t) (pfs : PreFs κ)
      → RP {e = e} m (Red m u) S κ (standing pfs)
      → RP {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs))
subNext : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
          (le : lo ≤ ℓ) (aM : Acc _<_ m) → SubStep {e = e} f G m
        → (h : HeldF f) → G h → (κ : Path Γ ℓ u t) (p : Pre κ)
        → RP {e = e} m (Red m u) S κ p
        → RP {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p)
fold (subRP le aM ss h g κ pfs rp) s₀ now vals col fin sched st rm hs =
  let r = proj₁ (ss le κ pfs rp s₀ h g now vals col fin sched st rm hs)
      g′ = proj₂ (ss le κ pfs rp s₀ h g now vals col fin sched st rm hs)
  in ans (Stage.out r) (Stage.sc r) (Stage.st′ r) (Stage.dv r)
         (headPre (Stage.hd r) (endPre (Stage.tr r))) (Stage.hl r) (Stage.kp r)
         (subNext le aM ss (Stage.hd r) g′ κ (endPre (Stage.tr r)) (endRP (Stage.tr r)))
         (endS (Stage.tr r))
subNext le aM ss h g κ (standing pfs) rp = subRP le aM ss h g κ pfs rp
subNext {n = n} {lo = lo} le aM ss h g κ fallen rp =
  dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ))

-- THE TRANSLATION OF A SOURCE'S TRACE THROUGH A SUBSCRIBING FRAME:
-- each call becomes the calls the step made above it, appended, and
-- the walk stops where the path fell.  It descends on the trace, one
-- call per call-bearing clause.
translate-sub : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
                (le : lo ≤ ℓ) (aM : Acc _<_ m) (ss : SubStep {e = e} f G m)
                (h : HeldF f) (g : G h) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
                (rp : RP {e = e} m (Red m u) S κ (standing pfs)) {s₀ : S}
              → Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs)) (subRP le aM ss h g κ pfs rp) s₀
              → Trace {e = e} m (Red m u) S κ (standing pfs) rp s₀
translate-sub-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
                   (le : lo ≤ ℓ) (aM : Acc _<_ m) (ss : SubStep {e = e} f G m)
                   (h : HeldF f) (g : G h) (κ : Path Γ ℓ u t) (p : Pre κ)
                   (rp : RP {e = e} m (Red m u) S κ p) {s₀ : S}
                 → Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p) (subNext le aM ss h g κ p rp) s₀
                 → Trace {e = e} m (Red m u) S κ p rp s₀
translate-sub le aM ss h g κ pfs rp []ᵗ = []ᵗ
translate-sub {n = n} {ℓ = ℓ} le aM ss h g κ pfs rp (fellᵗ _ s′) =
  fellᵗ (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ)) s′
translate-sub le aM ss h g κ pfs rp {s₀} (c ∷ᵗ tr) =
  let rg = ss le κ pfs rp s₀ h g (Call.now c) (Call.vals c) (Call.col c) (Call.fin c)
              (Call.sched c) (Call.st c) (Call.room c) (Call.holds c)
      r  = proj₁ rg
  in Stage.tr r ++ᵗ translate-sub-go le aM ss (Stage.hd r) (proj₂ rg) κ (endPre (Stage.tr r)) (endRP (Stage.tr r)) tr
translate-sub-go le aM ss h g κ (standing pfs) rp tr = translate-sub le aM ss h g κ pfs rp tr
translate-sub-go le aM ss h g κ fallen         rp tr = []ᵗ

-- and it ends where the source's trace did, one frame down, on a
-- ground that never stands where the ground it started from fell, at
-- a column the guard still holds of.  It descends on the trace.
translate-sub-end : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
                    (le : lo ≤ ℓ) (aM : Acc _<_ m) (ss : SubStep {e = e} f G m)
                    (h : HeldF f) (g : G h) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
                    (rp : RP {e = e} m (Red m u) S κ (standing pfs)) {s₀ : S}
                  → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs)) (subRP le aM ss h g κ pfs rp) s₀)
                  → Σ (HeldF f) (λ h″ → G h″ × endPre tr ≡ headPre h″ (endPre (translate-sub le aM ss h g κ pfs rp tr)))
translate-sub-end-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set} {f : Frame Γ s u} {G : HeldF f → Set}
                       (le : lo ≤ ℓ) (aM : Acc _<_ m) (ss : SubStep {e = e} f G m)
                       (h : HeldF f) (g : G h) (κ : Path Γ ℓ u t) (p : Pre κ)
                       (rp : RP {e = e} m (Red m u) S κ p) {s₀ : S}
                     → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p) (subNext le aM ss h g κ p rp) s₀)
                     → Σ (HeldF f) (λ h″ → G h″ × endPre tr ≡ headPre h″ (endPre (translate-sub-go le aM ss h g κ p rp tr)))
                       × joinPre p (endPre (translate-sub-go le aM ss h g κ p rp tr)) ≡ endPre (translate-sub-go le aM ss h g κ p rp tr)
translate-sub-end le aM ss h g κ pfs rp []ᵗ         = h , g , refl
translate-sub-end le aM ss h g κ pfs rp (fellᵗ _ _) = h , g , refl
translate-sub-end le aM ss h g κ pfs rp {s₀} (c ∷ᵗ tr) =
  let rg = ss le κ pfs rp s₀ h g (Call.now c) (Call.vals c) (Call.col c) (Call.fin c)
              (Call.sched c) (Call.st c) (Call.room c) (Call.holds c)
      r  = proj₁ rg
      go = translate-sub-go le aM ss (Stage.hd r) (proj₂ rg) κ (endPre (Stage.tr r)) (endRP (Stage.tr r)) tr
      ((h″ , g″ , eq) , jn) = translate-sub-end-go le aM ss (Stage.hd r) (proj₂ rg) κ (endPre (Stage.tr r)) (endRP (Stage.tr r)) tr
      e₂ = trans (end-++ (Stage.tr r) go) jn
  in h″ , g″ , trans eq (cong (headPre h″) (sym e₂))
translate-sub-end-go le aM ss h g κ (standing pfs) rp tr = translate-sub-end le aM ss h g κ pfs rp tr , refl
translate-sub-end-go {n = n} {lo = lo} le aM ss h g κ fallen rp tr =
  (h , g , fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ) tr) , refl

-- THE OUTER'S STEP: walk the observables that arrived, subscribing
-- each under a fresh inner frame, then wrap the end at the node.
thruStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
           (aM : Acc _<_ m) → SubStep {e = e} (thru-outer {u = u} op nid) RoomEmpty m

-- one inner subscribed by the walk, on standing ground, after the
-- flattener's own node has been written: the inner frame goes on live
-- over the path and the outer reads its ground back
subStanding : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
              (aM : Acc _<_ m) {S : Set} {lo ℓ}
              (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
              (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S)
              (ns′ : NodeState Γ) → QEmpty (just ns′) → (o : Val Γ (obs u)) → Red m (obs u) o → (now : Tick)
              {sched : Sched Γ} {st : EvalSt e} → Room m sched st → HoldsFs κ pfs sched st
            → nid < nodeCt sched → Apart κ (thru-outer {u = u} op nid)
            → Sound (thru-outer {u = u} op nid ↠[ le ] κ) sched st
            → Σ (Stage m (thru-outer op nid) le κ
                  (λ o′ sc s′ → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now
                                  (bumpNode sched) (record st { nodes = setNode nid ns′ (EvalSt.nodes st) }) (o′ , sc , s′))
                  (standing pfs) rp s₀ sched st)
                (λ r → RoomEmpty (Stage.hd r))
subStanding {m = m} {u = u} op nid aM le κ pfs rp s₀ ns′ gq o ro now {sched} {st} rm hsκ lt ap so =
  let inst = nodeCt sched
      κ′   = from-inner {s = u} op nid inst ↠[ ≤-refl ] κ
      ss   = fiStep op nid inst
      st″  = record st { nodes = setNode nid ns′ (EvalSt.nodes st) }
      hs′ : HoldsFs κ′ (just ns′ , pfs) (bumpNode sched) st″
      hs′ = ( (lookup-set nid ns′ (EvalSt.nodes st) , (<-≤-trans lt (n≤1+n _) ∷ᵃ ≤-refl ∷ᵃ []ᵃ))
            , apart-fi op nid κ pfs hsκ (λ k a → ap k (node-in₁ {nid} {k} [] a))
            , holdsFs-step κ pfs
                (λ k on _ → set-above nid k ns′ (EvalSt.nodes st) (head-off nid [] k (λ onN → ap k onN on)))
                (n≤1+n _) hsκ )
      (r , d , tr , hl , kp) = ro κ′ (standing (just ns′ , pfs)) (subRP ≤-refl aM ss (just ns′) gq κ pfs rp) s₀
                                  now (bumpNode sched) st″ rm
                                  (grounded hs′ (fresh-inner op nid κ sched {st″}
                                     (sub-ot (λ r∈ → r∈) ≤-refl (drop-ot (thru-outer op nid) le κ so))
                                     (sub-on (λ r∈ → r∈) ≤-refl (head-on (thru-outer op nid) le κ nid (self-node nid []) so))))
      (h″ , g″ , eq) = translate-sub-end ≤-refl aM ss (just ns′) gq κ pfs rp tr
      tr′ = translate-sub ≤-refl aM ss (just ns′) gq κ pfs rp tr
      sc  = proj₁ (proj₂ r)
      st′ = proj₂ (proj₂ r)
  in stage (proj₁ r) sc st′ d tr′ refl h″
       (fiHolds→thru op nid inst le κ h″ (endPre tr′) (subst (λ p → PreHolds m κ′ p sc st′) eq hl))
       (kept-shift (from-inner op nid inst) (thru-outer op nid) ≤-refl le κ h″ h″ (endPre tr′)
          {sched} {bumpNode sched} {sc} {st} {st″} {st′} (n≤1+n (nodeCt sched))
          (λ k k< ne on → [ (λ a → ne (node-in₁ {nid} {k} [] a)) , (λ c → subst T (<→≢ᵇ k<) c) ] (node-two {nid} {inst} {k} on))
          (λ k _ ne → set-above nid k ns′ (EvalSt.nodes st) (head-off nid [] k ne))
          (λ _ _ _ ea → ea)
          (subst (λ p → Kept κ′ p (bumpNode sched) st″ sc st′) eq kp))
     , qempty-room h″ g″

-- one inner subscribed on fallen ground: the store is read raw
consumeFallen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
                (aM : Acc _<_ m) {ℓ} (κ : Path Γ ℓ u t) (now : Tick)
                (o : Val Γ (obs u)) → Red m (obs u) o
                → {sched : Sched Γ} {st : EvalSt e} → Room m sched st → Fell m sched st
                → Sound κ sched st → NodeOn nid κ sched st
              → Σ (Stream Γ t × Sched Γ × EvalSt e)
                  (λ r → thruConsume⇓ {e = e} op nid κ now o sched st r
                       × Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) × NodeOn nid κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
consumeFallen {n = n} {u = u} op nid aM {ℓ} κ now o ro {sched} {st} rm fell so nd
  with lookupNode nid (EvalSt.nodes st) in c
... | h with consumeUsable op u h in equ
...   | false = _ , consumeNil op (trans (cong (consumeUsable op u) c) equ) , so , nd
...   | true with usable op u h equ
...     | u-switch cur od =
            let sk  = switchKill cur sched st
                ks  = switchKill-keeps cur sched st refl
                st₁ = record (proj₂ sk) { nodes = setNode nid (switch-st (just (nodeCt (proj₁ sk))) od) (EvalSt.nodes (proj₂ sk)) }
                ct  = subst (nodeCt sched ≤_) (sym (switchKill-ct cur sched st)) ≤-refl
                so′ = sub-ot {κ = κ} {sched = sched} {sched′ = proj₁ sk} {st = st} {st′ = st₁} (kill-sub cur sched st) ct so
                nd′ = sub-on {nid = nid} {κ = κ} {sched = sched} {sched′ = proj₁ sk} {st = st} {st′ = st₁} (kill-sub cur sched st) ct nd
                κ′  = from-inner {s = u} switchᵒ nid (nodeCt (proj₁ sk)) ↠[ ≤-refl ] κ
                (r , d , _ , hl , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                         (bumpNode (proj₁ sk)) st₁ (room-keeps ks rm)
                                         (grounded (fell-keeps ks fell) (fresh-inner switchᵒ nid κ (proj₁ sk) {st₁} so′ nd′))
            in _ , consume-switch-sub c refl refl (inner refl d) , inner-back switchᵒ nid (nodeCt (proj₁ sk)) κ (sounds hl)
...     | u-exhaust od =
            let st₁ = record st { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) }
                κ′  = from-inner {s = u} exhaustᵒ nid (nodeCt sched) ↠[ ≤-refl ] κ
                (r , d , _ , hl , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                         (bumpNode sched) st₁ rm
                                         (grounded fell (fresh-inner exhaustᵒ nid κ sched {st₁}
                                            (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)))
            in _ , consume-exhaust-sub c (inner refl d) , inner-back exhaustᵒ nid (nodeCt sched) κ (sounds hl)
...     | u-merge lim act q od with hasRoom lim act in eqr
...       | false = _ , consume-all-enqueue c eqr , sub-ot (λ r∈ → r∈) ≤-refl so , sub-on (λ r∈ → r∈) ≤-refl nd
...       | true  =
            let st₁ = record st { nodes = setNode nid (mergeAll-st lim (suc act) q od) (EvalSt.nodes st) }
                κ′  = from-inner {s = u} mergeAllᵒ nid (nodeCt sched) ↠[ ≤-refl ] κ
                (r , d , _ , hl , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                         (bumpNode sched) st₁ rm
                                         (grounded fell (fresh-inner mergeAllᵒ nid κ sched {st₁}
                                            (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)))
            in _ , consume-all-sub c eqr (inner refl d) , inner-back mergeAllᵒ nid (nodeCt sched) κ (sounds hl)

-- one observable consumed by the walk, on standing ground
consumeStanding : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
                  (aM : Acc _<_ m) {S : Set} {lo ℓ}
                  (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (now : Tick) (pfs : PreFs κ)
                  (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S)
                  (h : Maybe (NodeState Γ)) → RoomEmpty h → (o : Val Γ (obs u)) → Red m (obs u) o
                → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
                → PreHolds m (thru-outer {u = u} op nid ↠[ le ] κ) (standing (h , pfs)) sched st
                → Σ (Stage m (thru-outer op nid) le κ
                      (λ o′ sc s′ → thruConsume⇓ {e = e} op nid κ now o sched st (o′ , sc , s′))
                      (standing pfs) rp s₀ sched st)
                    (λ r → RoomEmpty (Stage.hd r))
consumeStanding {u = u} op nid aM le κ now pfs rp s₀ h g o ro {sched} {st} rm hs@(grounded ((c , lt ∷ᵃ []ᵃ) , ap , hsκ) so)
  with consumeUsable op u h in equ
... | false = stage-nil _ le κ (standing pfs) rp s₀ [] (consumeNil op (trans (cong (consumeUsable op u) c) equ)) h hs , g
... | true with usable op u h equ
...   | u-switch cur od =
        let sk  = switchKill cur sched st
            ks  = switchKill-keeps cur sched st refl
            ctE = switchKill-ct cur sched st
            ndE = switchKill-nodes cur sched st
            hsκ′ : HoldsFs κ pfs (proj₁ sk) (proj₂ sk)
            hsκ′ = holdsFs-step κ pfs (λ k _ _ → cong (lookupNode k) ndE) (subst (nodeCt sched ≤_) (sym ctE) ≤-refl) hsκ
            (sb , gsb) = subStanding switchᵒ nid aM le κ pfs rp s₀ (switch-st (just (nodeCt (proj₁ sk))) od) tt o ro now
                           (room-keeps ks rm) hsκ′ (subst (nid <_) (sym ctE) lt) ap
                           (sub-ot (kill-sub cur sched st) (subst (nodeCt sched ≤_) (sym ctE) ≤-refl) so)
        in stage-map (λ d → consume-switch-sub c refl refl (inner refl d))
             (stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl) (λ k _ _ → cong (lookupNode k) ndE)
                (ends-sub (thru-outer op nid ↠[ le ] κ) {sched = sched} {st = st} {st′ = proj₂ sk} (kill-sub cur sched st)) sb)
           , gsb
...   | u-exhaust od =
        let (sb , gsb) = subStanding exhaustᵒ nid aM le κ pfs rp s₀ (exhaust-st true od) tt o ro now rm hsκ lt ap so
        in stage-map (λ d → consume-exhaust-sub c (inner refl d)) sb , gsb
...   | u-merge lim act q od with hasRoom lim act in eqr
...     | false = stage-map (λ { (refl , refl , refl) → consume-all-enqueue c eqr })
                    (writeStage _ le κ (standing pfs) rp s₀ nid (mergeAll-st lim act (q ++ o ∷ []) od)
                       (λ k ne → head-off nid [] k ne) (just (mergeAll-st lim act (q ++ o ∷ []) od))
                       (lookup-set nid (mergeAll-st lim act (q ++ o ∷ []) od) (EvalSt.nodes st)) h hs)
                , (λ tr → ⊥-elim (subst T eqr tr))
...     | true  =
        let (sb , gsb) = subStanding mergeAllᵒ nid aM le κ pfs rp s₀ (mergeAll-st lim (suc act) q od)
                           (g tt₀) o ro now rm hsκ lt ap so
        in stage-map (λ d → consume-all-sub c eqr (inner refl d)) sb , gsb

consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
          (aM : Acc _<_ m) {S : Set} {lo ℓ}
          (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (now : Tick) (q : Pre κ)
          (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
          (h : Maybe (NodeState Γ)) → RoomEmpty h → (o : Val Γ (obs u)) → Red m (obs u) o
        → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
        → PreHolds m (thru-outer {u = u} op nid ↠[ le ] κ) (headPre h q) sched st
        → Σ (Stage m (thru-outer op nid) le κ
              (λ o′ sc s′ → thruConsume⇓ {e = e} op nid κ now o sched st (o′ , sc , s′)) q rp s₀ sched st)
            (λ r → RoomEmpty (Stage.hd r))
consume op nid aM le κ now (standing pfs) rp s₀ h g o ro rm hs =
  consumeStanding op nid aM le κ now pfs rp s₀ h g o ro rm hs
consume op nid aM le κ now fallen rp s₀ h g o ro rm (grounded fell so) =
  let (r , d , so′ , nd′) = consumeFallen op nid aM κ now o ro rm fell
                              (drop-ot (thru-outer op nid) le κ so) (head-on (thru-outer op nid) le κ nid (self-node nid []) so)
  in fallenStage _ le κ rp s₀ (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) d (thruConsume-keeps d) fell
       (push-thru op nid le κ so′ nd′) h , g

walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
       (aM : Acc _<_ m) {S : Set} {lo ℓ}
       (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (now : Tick) (q : Pre κ)
       (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
       (h : Maybe (NodeState Γ)) → RoomEmpty h → (vals : List (Val Γ (obs u))) → All (Red m (obs u)) vals
     → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
     → PreHolds m (thru-outer {u = u} op nid ↠[ le ] κ) (headPre h q) sched st
     → Σ (Stage m (thru-outer op nid) le κ
           (λ o sc s′ → thruWalk⇓ {e = e} op nid κ now vals sched st (o , sc , s′)) q rp s₀ sched st)
         (λ r → RoomEmpty (Stage.hd r))
walk op nid aM le κ now q rp s₀ h g [] []ᵃ rm hs = stage-nil _ le κ q rp s₀ [] walk-nil h hs , g
walk op nid aM le κ now q rp s₀ h g (o ∷ os) (ro ∷ᵃ ros) rm hs =
  let (c , gc) = consume op nid aM le κ now q rp s₀ h g o ro rm hs
      (w , gw) = walk op nid aM le κ now (endPre (Stage.tr c)) (endRP (Stage.tr c)) (endS (Stage.tr c)) (Stage.hd c) gc os ros
                   (room-keeps (thruConsume-keeps (Stage.dv c)) rm) (Stage.hl c)
  in stage-seq c w (λ d₂ → walk-cons (Stage.dv c) d₂) , gw

-- the wrap at the end of the walk, and the one call above it
thruTail : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId) {S : Set} {lo ℓ}
           (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (now : Tick) (fin : Bool) (q : Pre κ)
           (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S) (h : Maybe (NodeState Γ)) → RoomEmpty h
         → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
         → PreHolds m (thru-outer {u = u} op nid ↠[ le ] κ) (headPre h q) sched st
         → Σ (Stage m (thru-outer op nid) le κ
               (λ o sc s′ → foldPath⇓ {e = e} now κ []
                              (proj₁ (thruWrap {e = e} op nid fin (sched , st)))
                              (proj₁ (proj₂ (thruWrap {e = e} op nid fin (sched , st))))
                              (proj₂ (proj₂ (thruWrap {e = e} op nid fin (sched , st)))) (o , sc , s′))
               q rp s₀ sched st)
             (λ r → RoomEmpty (Stage.hd r))
thruTail op nid le κ now fin (standing pfs) rp s₀ h g {sched} {st} rm (grounded ((c , lt ∷ᵃ []ᵃ) , ap , hs) so) =
  let wf  = wrap-facts op nid fin sched st
      W   = thruWrap op nid fin (sched , st)
      h′  = wrapNode op fin h
      node : lookupNode nid (EvalSt.nodes (proj₂ (proj₂ W))) ≡ h′
      node = subst (λ x → lookupNode nid (EvalSt.nodes (proj₂ (proj₂ W))) ≡ wrapNode op fin x) c (Wrapped.node wf)
      ctE = cong nodeCt (Wrapped.sch wf)
      hs₂ : HoldsFs (thru-outer op nid ↠[ le ] κ) (h′ , pfs) (proj₁ (proj₂ W)) (proj₂ (proj₂ W))
      hs₂ = ( (node , subst (nid <_) (sym ctE) lt ∷ᵃ []ᵃ) , ap
            , holdsFs-step κ pfs (λ k on _ → Wrapped.off wf k (head-off nid [] k (λ onN → ap k onN on)))
                (subst (nodeCt sched ≤_) (sym ctE) ≤-refl) hs )
      cs = callStage (thru-outer op nid) le κ h′ (standing pfs) rp s₀ now [] (ofColumn κ (standing pfs) []ᵃ) (proj₁ W)
             (room-keeps (thruWrap-keeps op nid fin sched st) rm) (grounded hs₂ (wrap-ot op nid fin sched st so))
  in stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl)
       (λ k _ ne → Wrapped.off wf k (head-off nid [] k ne))
       (ends-sub (thru-outer op nid ↠[ le ] κ) {sched = sched} {st = st} {st′ = proj₂ (proj₂ W)} (wrap-reg op nid fin sched st)) cs
     , room-wrap op fin h g
thruTail op nid le κ now fin fallen rp s₀ h g {sched} {st} rm (grounded fell so) =
  let wf  = wrap-facts op nid fin sched st
      W   = thruWrap op nid fin (sched , st)
      ctE = cong nodeCt (Wrapped.sch wf)
      cs  = callStage (thru-outer op nid) le κ (wrapNode op fin h) fallen rp s₀ now [] (ofColumn κ fallen []ᵃ) (proj₁ W)
              (room-keeps (thruWrap-keeps op nid fin sched st) rm)
              (grounded (fell-keeps (thruWrap-keeps op nid fin sched st) fell) (wrap-ot op nid fin sched st so))
  in stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl)
       (λ k _ ne → Wrapped.off wf k (head-off nid [] k ne))
       (ends-sub (thru-outer op nid ↠[ le ] κ) {sched = sched} {st = st} {st′ = proj₂ (proj₂ W)} (wrap-reg op nid fin sched st)) cs
     , room-wrap op fin h g

thruStep op nid aM le κ pfs rp s₀ h g now vals col fin sched st rm hs =
  let (w , gw) = walk op nid aM le κ now (standing pfs) rp s₀ h g vals col rm hs
      (t , gt) = thruTail op nid le κ now fin (endPre (Stage.tr w)) (endRP (Stage.tr w)) (endS (Stage.tr w)) (Stage.hd w) gw
                   (room-keeps (thruWalk-keeps (Stage.dv w)) rm) (Stage.hl w)
  in stage-seq w t (λ dt → fold-step (step-thru-outer (Stage.dv w)) dt) , gt

-- THE FLATTENER ARMS' SHARED BODY: install the node at the counter,
-- subscribe the outer under the outer frame live over whatever ground
-- the caller stands on, and read the path's ground back out.
red-all : ∀ {n} {Γ : Ctx n} {Θ u} (op : AllOp) (ns : NodeState Γ) → RoomEmpty (just ns) → ∀ (b : Exp Γ [] [] Θ (obs u))
          (ρ : Env Γ Θ) {m} → RedEnv m ρ → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
        → Acc _<_ (gsizeᵉ b) → (aM : Acc _<_ m)
        → ∀ {S : Set} {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (pre : Pre κ)
          (rp : RP {e = e} m (Red m u) S κ pre) (s₀ : S)
          (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Room m sched st → PreHolds m κ pre sched st
        → Σ (Stream Γ t × Sched Γ × EvalSt e)
            (λ r → subscribeAll⇓ {e = e} op ns (Θ , b , ρ) κ now sched st r
                 × Σ (Trace {e = e} m (Red m u) S κ pre rp s₀)
                     (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                           × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))
red-all op ns gns b ρ rρ k ok aK aB aM κ (standing pfs) rp s₀ now sched st rm hs =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k ok aK aB aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just ns , pfs))
                                  (subRP ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp) s₀ now
                                  (bumpNode sched) (installNode (nodeCt sched) ns st) rm
                                  (fresh-holds (thru-outer op (nodeCt sched)) κ pfs (just ns) ns (λ _ → node-eq)
                                     (lookup-set (nodeCt sched) ns (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) hs)
      (h″ , _ , eq) = translate-sub-end ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
      tr′ = translate-sub ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
  in r , sub-all refl d , tr′
   , unheadHolds (thru-outer op (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       (subst (λ p → PreHolds _ (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq hl)
   , unheadKept (thru-outer op (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
       {sched} {bumpNode sched} {st = st} {st₁ = installNode (nodeCt sched) ns st}
       (λ k′ k< on → subst T (<→≢ᵇ k<) (node-one {nodeCt sched} {k′} on)) (n≤1+n _)
       (λ k′ k< → set-above (nodeCt sched) k′ ns (EvalSt.nodes st) (<→≢ᵇ k<))
       (λ _ _ _ ea → ea)
       (subst (λ p → Kept (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) p (bumpNode sched) (installNode (nodeCt sched) ns st)
                           (proj₁ (proj₂ r)) (proj₂ (proj₂ r))) eq kp)
red-all {n = n} op ns gns b ρ rρ k ok aK aB aM {lo = lo} κ fallen rp s₀ now sched st rm fell =
  let (r , d , tr , hl , kp) = redExpAcc b ρ rρ k ok aK aB aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) fallen
                                  (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
                                  (bumpNode sched) (installNode (nodeCt sched) ns st) rm (grounded (ground fell) (fresh-sound (thru-outer op (nodeCt sched)) κ ns (λ _ → node-eq) (sounds fell)))
  in r , sub-all refl d , []ᵗ
    , unheadHolds (thru-outer op (nodeCt sched)) ≤-refl κ nothing fallen
        (subst (λ p → PreHolds _ (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
           (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

red-mergeAll lim b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all mergeAllᵒ (mergeAll-st lim 0 [] false) (λ _ → refl) b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-merge-all d , rest
red-switchAll b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all switchᵒ (switch-st nothing false) tt b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-switch-all d , rest
red-exhaustAll b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all exhaustᵒ (exhaust-st false false) tt b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-exhaust-all d , rest
