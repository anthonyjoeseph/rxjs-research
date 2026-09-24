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

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; map; _++_; null; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; _∸_; s≤s; z≤n; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; _≤?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<; n≤1+n; <-≤-trans; <⇒≤; ∸-monoʳ-<; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Prim using (Tick; ObservableInput; hot; cold)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; isData; unfoldμ; varᵗ; unit̂;
  bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; FnClo; applyClo; _≟ᵗ_)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (sourceᵏ; nodeᵏ; regᵏ; ordinalᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; PreservedBelow; pres; below; pres-write; lookup-set; set-above; <→≢ᵇ)
open import Decide using (∧ˡ; ∧ʳ; ≡ᵇ→≡; ≡ᵇ-refl)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f;
  batchSync-f; from-inner; thru-outer; NodeState; lookupNode; frameNodes; pathHasNode;
  register; installNode; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; mergeAllᵒ;
  AllOp; switchᵒ; exhaustᵒ; NodeId; RegRow; cell-st; take-st; switch-st; exhaust-st; batchSync-st;
  setNode; hasRoom; consumeUsable; finishUsable; thruWrap; switchKill; aliveThroughᶠ;
  RegId; RegSrc; regFloor; cutThrough; takeVals; takeDispatch; scanVals; scanDispatch; batchVals; batchDispatch; batchDown; resolve; shareAdmit; shareDying; shareSpend; drainSt)
open import Rx.Evaluator.Unconn-Arith using (unconn; unconn-insert; fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps; Keeps; switchKill-keeps; thruWrap-keeps; thruWalk-keeps;
  thruConsume-keeps; innerFinish-keeps; subscribeE-keeps; shareGo-keeps; shareDying-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; mergeAllDrain⇓; subs-of; subs-empty; subs-mint; subs-defer; subs-floor; subs-μ; subs-map; subs-take-zero; subs-take-suc; subs-scan; subs-batchSync; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async;
  subs-shared; slot-spent; slot-join; slot-connect; connect; foldPath⇓; fold-root; fold-step;
  stepFrame⇓; step-map; injectRoot; inner; thruConsume⇓; consume-all-sub; consume-all-enqueue;
  consume-all-nil; consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil; thruWalk⇓; walk-nil; walk-cons; drain-spent; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil; innerReact⇓;
  react-false; react-alive; react-dead; step-from-inner; step-thru-outer; subscribeAll⇓;
  sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all; shareWalk⇓; shareGo⇓; fold-sink; disp;
  walk-end; walk-more; go-nil; go-cut; go-live; drain-nil; drain-no-room; drain-room; step-scan; step-take;
  step-batchSync)

------------------------------------------------------------------
-- THE CEILING, THE CONTINUATION, THE CANDIDATE.
------------------------------------------------------------------

-- THE ROOM LEFT FOR CONNECTS, WHICH IS WHAT EVERY SUBSCRIPTION SPENDS
-- AND ONLY A CONNECT SPENDS ANY OF.  A shared slot connects once ever,
-- so the slots the table holds and the connected set does not is a
-- quantity the whole run only ever takes down -- and it is the one
-- quantity that does, since a subscribe re-entered from inside a
-- share's own emission is subscribing a slot the set already holds.
--
-- IT TRAVELS AS A CEILING WITH THE WITNESS BESIDE IT, NOT AS AN
-- ACCESSIBILITY AT THE COUNT.  A step that leaves the count alone then
-- hands the SAME witness on, as a variable, and re-proves the bound
-- instead -- which is what the termination checker can read.  An
-- accessibility carried at the count itself would have to be
-- transported at every such step, and a transported accessibility is a
-- function call where a structural child is owed.
--
-- THE ACCESSIBILITY IS SUPPLIED WHERE A CANDIDATE IS BUILT, THE ROOM
-- WHERE IT IS APPLIED.  `redExpAcc`, `reducible` and `red-val` each
-- take `Acc _<_ m` and produce a candidate at ceiling `m`; a
-- candidate's observable arm takes only the witness that the state it
-- is being applied in sits under `m`.  So the three places that
-- DESCEND on the room -- the connect, and the two runtime guards below
-- -- are each a `with` on a comparison followed by an application of
-- the accessibility's own field, which is the one form the checker
-- reads as smaller.
Room : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → ℕ → Sched Γ → EvalSt e → Set
Room m sched st = unconn (Sched.slots sched) (EvalSt.connectedShares st) ≤ m

-- THE ROOM HAS FALLEN: a connect happened since this ceiling was set.
-- It is the one fact a frame may spend where the store and its own
-- closure disagree, because it is the one thing that peels the
-- accessibility a candidate at the store's contents is funded by.
Fell : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → ℕ → Sched Γ → EvalSt e → Set
Fell m sched st = unconn (Sched.slots sched) (EvalSt.connectedShares st) < m

-- WHAT A FRAME HOLDS, AS VALUES AND NOTHING ELSE.  A frame's
-- continuation closes over candidates for what its node holds, and a
-- candidate is one universe above the state -- so the store cannot
-- carry the candidates and the candidate cannot be indexed by them
-- (that is the positivity failure above).  What the candidate CAN be
-- indexed by is the values: the node state the closure was built over,
-- at `Set`.  `Maybe`, because a node can be absent, and a column that
-- can say so is one every state agrees with.
HeldF : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
HeldF           (map-f _)            = ⊤
HeldF {Γ = Γ}   (scan-f _ _)         = Maybe (NodeState Γ)
HeldF {Γ = Γ}   (take-f _)           = Maybe (NodeState Γ)
HeldF {Γ = Γ}   (batchSync-f _)      = Maybe (NodeState Γ)
HeldF {Γ = Γ}   (from-inner _ _ _)   = Maybe (NodeState Γ)
HeldF {Γ = Γ}   (thru-outer _ _)     = Maybe (NodeState Γ)

-- WHAT A STANDING PATH'S FRAMES STAND ON: each frame's own column,
-- which the store agrees with, so there is no value the frame cannot
-- vouch for.  A STANDING PATH MAY END AT A SHARE'S SINK, which holds
-- nothing: an inner subscribed from the raw fold stands on the store's
-- own columns over a path the fan-out reached, and what a standing
-- fold past the sink writes is accounted for by the terminus `Kept`
-- guards on, not by the path.
PreFs : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → Set
PreFs root             = ⊤
PreFs (share-sink _ _) = ⊤
PreFs (f ↠[ _ ] κ)     = HeldF f × PreFs κ

-- AND WHAT THE PATH STANDS ON: EITHER EVERY FRAME'S OWN GROUND, OR THE
-- ROOM HAVING FALLEN SINCE THE CEILING WAS SET.  A fallen path holds
-- no candidates at all -- the accessibility peels and the whole path
-- is rebuilt raw from the store at the lower ceiling on every call --
-- and the fall is PATH-WIDE BY TYPE, because a live frame's parent
-- expects a full column and a peeled candidate cannot supply one.  It
-- is permanent because the room never rises.  The branch the old
-- guards could not close is the one no constructor names: a
-- disagreeing store with the room still at the ceiling.
--
-- IT IS AN INDEX OF THE CONTINUATION, NOT A HYPOTHESIS ON ONE FOLD,
-- because it is what the SUCCESSOR was built over too: a fold hands
-- back the successor together with the ground it stands on in the
-- state it left, and the next caller supplies that ground back.
data Pre {n} {Γ : Ctx n} {lo u t} (κ : Path Γ lo u t) : Set where
  standing : PreFs κ → Pre κ
  fallen   : Pre κ

-- THE STORE AGREES WITH THE COLUMN: the frame's node reads back as
-- what the column says.
ConsistentF : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
              (f : Frame Γ s u) → HeldF f → EvalSt e → Set
ConsistentF (map-f _)               _ st = ⊤
ConsistentF (scan-f _ nid)          h st = lookupNode nid (EvalSt.nodes st) ≡ h
ConsistentF (take-f nid)            h st = lookupNode nid (EvalSt.nodes st) ≡ h
ConsistentF (batchSync-f nid)       h st = lookupNode nid (EvalSt.nodes st) ≡ h
ConsistentF (from-inner _ nid _)    h st = lookupNode nid (EvalSt.nodes st) ≡ h
ConsistentF (thru-outer _ nid)      h st = lookupNode nid (EvalSt.nodes st) ≡ h

-- AND THE FRAME'S NODE IS BELOW THE COUNTER, which is what makes a
-- write at the counter leave it alone.  Agreement alone is not
-- preserved by anything: an arm installing its own node has to know
-- the node it installs is not one of the path's, and that is a fact
-- about allocation, carried here beside the agreement it protects.
FreshF : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Set
FreshF ct f = All (_< ct) (frameNodes f)

HoldsF : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
         (f : Frame Γ s u) → HeldF f → Sched Γ → EvalSt e → Set
HoldsF f h sched st = ConsistentF f h st × FreshF (nodeCt sched) f

-- AND A FRAME'S NODES ARE NONE OF THE PATH'S ABOVE IT.  Its own write
-- then touches no frame above it, and the fold above touches no node
-- of its own -- the two directions consistency has to survive.  A
-- fact about the path alone.
Apart : ∀ {n} {Γ : Ctx n} {lo u t s} (κ : Path Γ lo u t) (f : Frame Γ s u) → Set
Apart κ f = ∀ k → T (any (_≡ᵇ k) (frameNodes f)) → T (pathHasNode k κ) → ⊥

HoldsFs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
          (κ : Path Γ lo u t) → PreFs κ → Sched Γ → EvalSt e → Set
HoldsFs root             _         sched st = ⊤
HoldsFs (share-sink _ _) _         sched st = ⊤
HoldsFs (f ↠[ _ ] κ)     (h , pfs) sched st =
  HoldsF f h sched st × Apart κ f × HoldsFs κ pfs sched st

-- AND NO FRAME'S NODES RECUR ON THE PATH BELOW IT, on either ground.
-- Every path a run builds is nested one frame at a time at nodes the
-- counter hands out, so it is distinct by construction; carried here
-- because the store's rows and the raw fold's paths are read back from
-- the registry, where nothing else says so.
Distinct : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → Set
Distinct root             = ⊤
Distinct (share-sink _ _) = ⊤
Distinct (f ↠[ _ ] κ)     = Apart κ f × Distinct κ

-- WHERE A PATH ENDS: at the root, or at one share's sink.
endOf : ∀ {n} {Γ : Ctx n} {lo s t} → Path Γ lo s t → Maybe (Fin n)
endOf root             = nothing
endOf (share-sink i _) = just i
endOf (_ ↠[ _ ] p)     = endOf p

rowThrough : ∀ {n} {Γ : Ctx n} {t} → NodeId → RegRow Γ t → Bool
rowThrough k (_ , _ , (_ , p)) = pathHasNode k p

rowEnd : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → Maybe (Fin n)
rowEnd (_ , _ , (_ , p)) = endOf p

rowDistinct : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → Set
rowDistinct (_ , _ , (_ , p)) = Distinct p

-- ONE TERMINUS PER NODE: two rows through one node end at the same
-- place.
Termini : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → Set
Termini st = ∀ k {r r′} → r ∈ EvalSt.registry st → r′ ∈ EvalSt.registry st
               → T (rowThrough k r) → T (rowThrough k r′) → rowEnd r ≡ rowEnd r′

EndsAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → NodeId → Maybe (Fin n) → EvalSt e → Set
EndsAt k x st = ∀ {r} → r ∈ EvalSt.registry st → T (rowThrough k r) → rowEnd r ≡ x

-- A NODE BELOW THE COUNTER, OFF THE PATH, WHOSE ROWS END WHERE THE
-- PATH DOES, STILL HAS ITS ROWS END THERE: a run's new rows run through
-- the path's nodes and the ones it minted, and a cut only removes rows.
EndsKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
           (κ : Path Γ lo u t) → Sched Γ → EvalSt e → EvalSt e → Set
EndsKept κ sched st st′ =
  ∀ k → k < nodeCt sched → (T (pathHasNode k κ) → ⊥) → EndsAt k (endOf κ) st → EndsAt k (endOf κ) st′

-- AND EVERY NODE A ROW RUNS THROUGH IS BELOW THE COUNTER, which is what
-- lets a node the counter hands out carry no row yet.
FreshRows : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → Set
FreshRows sched st = ∀ {r} → r ∈ EvalSt.registry st → ∀ k → T (rowThrough k r) → k < nodeCt sched

FreshPath : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → Sched Γ → Set
FreshPath κ sched = ∀ k → T (pathHasNode k κ) → k < nodeCt sched

-- THE RULE, AS A FACT ABOUT THE STORE ALONE.
record Rule {n} {Γ : Ctx n} {t} {e : Closed Γ t} (sched : Sched Γ) (st : EvalSt e) : Set where
  constructor rule
  field
    termini       : Termini st
    fresh-rows    : FreshRows sched st
    distinct-rows : ∀ {r} → r ∈ EvalSt.registry st → rowDistinct r
open Rule public

-- AND THE RULE FOR A CONTINUATION, which the store does not hold: every
-- row through one of its nodes ends where it does, and its nodes are
-- below the counter.  This is what ties a path folded down to the rows
-- the store holds, and it is carried on both grounds because every fold
-- whose state the raw fold later reads owes it.
record Sound {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s}
             (κ : Path Γ lo s t) (sched : Sched Γ) (st : EvalSt e) : Set where
  constructor sound
  field
    ruled      : Rule sched st
    ends       : ∀ k → T (pathHasNode k κ) → EndsAt k (endOf κ) st
    fresh-path : FreshPath κ sched
    distinct   : Distinct κ
open Sound public

-- A FLATTENER'S OWN NODE, below the path it sits on: its rows end where
-- that path does, it is below the counter, and it is not on that path.
-- Without the last, a path passing the flattener's own outer frame is
-- admitted, and there an inner subscribed raw queues onto the merge
-- whose finish drains it, one level down each time, so `rawInner` has
-- no finite derivation: `git show 966e2e99:agda/evidence/refuted/Refuted/Raw-Inner-Feedback.agda`.
record NodeOn {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s}
              (nid : NodeId) (κ : Path Γ lo s t) (sched : Sched Γ) (st : EvalSt e) : Set where
  constructor node-on
  field
    at-end     : EndsAt nid (endOf κ) st
    node-below : nid < nodeCt sched
    off-path   : T (pathHasNode nid κ) → ⊥
open NodeOn public

Ground : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
         (m : ℕ) (κ : Path Γ lo u t) → Pre κ → Sched Γ → EvalSt e → Set
Ground m κ (standing pfs) sched st = HoldsFs κ pfs sched st
Ground m κ fallen         sched st = Fell m sched st

-- AND ON EITHER GROUND, THE RULE: a fold's state is one the raw fold may
-- later read, whichever ground the fold stood on.
record PreHolds {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
                (m : ℕ) (κ : Path Γ lo u t) (pre : Pre κ) (sched : Sched Γ) (st : EvalSt e) : Set where
  constructor grounded
  field
    ground : Ground m κ pre sched st
    sounds : Sound κ sched st
open PreHolds public

-- THE CANDIDATE COLUMN IS TOTAL WHERE THE PATH STANDS ON A FRAME, and
-- absent otherwise: a standing frame holds candidates for everything
-- its node holds and receives one beside every value that arrives; a
-- fallen path re-vouches everything from the store and needs none;
-- the root and a share's sink vouch for nothing.
Column : ∀ {n} {Γ : Ctx n} {lo u t} (κ : Path Γ lo u t)
         (P : Val Γ u → Set₁) → Pre κ → List (Val Γ u) → Set₁
Column (f ↠[ _ ] κ) P (standing _) vals = All P vals
Column _            P _            vals = ⊤

-- a full column is a column on any ground
ofColumn : ∀ {n} {Γ : Ctx n} {lo u t} (κ : Path Γ lo u t)
           {P : Val Γ u → Set₁} (pre : Pre κ) {vals : List (Val Γ u)}
         → All P vals → Column κ P pre vals
ofColumn root             _            ps = tt
ofColumn (share-sink _ _) _            ps = tt
ofColumn (f ↠[ _ ] κ)     (standing _) ps = ps
ofColumn (f ↠[ _ ] κ)     fallen       ps = tt

-- the two halves of a disjunction under `T`, in and out
∨-Tˡ : ∀ {a b : Bool} → T a → T (a ∨ b)
∨-Tˡ {true} _ = tt₀

∨-Tʳ : ∀ {a b : Bool} → T b → T (a ∨ b)
∨-Tʳ {true}  _ = tt₀
∨-Tʳ {false} p = p

∨-T : ∀ {a b : Bool} → T (a ∨ b) → T a ⊎ T b
∨-T {true}  _ = inj₁ tt₀
∨-T {false} p = inj₂ p

-- membership in a one- or two-node frame, read off and put back
node-one : ∀ {x k : ℕ} → T (any (_≡ᵇ k) (x ∷ [])) → T (x ≡ᵇ k)
node-one {x} {k} p with x ≡ᵇ k
... | true  = tt₀
... | false = p

node-two : ∀ {x y k : ℕ} → T (any (_≡ᵇ k) (x ∷ y ∷ [])) → T (x ≡ᵇ k) ⊎ T (y ≡ᵇ k)
node-two {x} {y} {k} p with x ≡ᵇ k
... | true  = inj₁ tt₀
... | false = inj₂ (node-one {y} {k} p)

node-in₁ : ∀ {x k : ℕ} (ns : List ℕ) → T (x ≡ᵇ k) → T (any (_≡ᵇ k) (x ∷ ns))
node-in₁ {x} {k} ns p with x ≡ᵇ k
... | true  = tt₀
... | false = ⊥-elim p

-- a node found among a list of nodes below a bound is below it
nodes-below : ∀ (ns : List ℕ) {ct} → All (_< ct) ns
            → ∀ k → T (any (_≡ᵇ k) ns) → k < ct
nodes-below (j ∷ ns) (lt ∷ᵃ lts) k on with j ≡ᵇ k in eq
... | true  = subst (_< _) (≡ᵇ→≡ j k eq) lt
... | false = nodes-below ns lts k on

-- a node is found among its own
self-node : ∀ (nid : ℕ) (ns : List ℕ) → T (any (_≡ᵇ nid) (nid ∷ ns))
self-node nid ns rewrite ≡ᵇ-refl nid = tt₀

-- two paths agree where they meet: a node on both ends them in one place
Agree : ∀ {n} {Γ : Ctx n} {t lo lo′ s s′} → Path Γ lo s t → Path Γ lo′ s′ t → Set
Agree κ κ₂ = ∀ k → T (pathHasNode k κ) → T (pathHasNode k κ₂) → endOf κ ≡ endOf κ₂

-- the rule for a path is the rule for the path below its head frame
drop-ot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} (f : Frame Γ s u) (le : lo ≤ ℓ)
            (κ : Path Γ ℓ u t) {sched : Sched Γ} {st : EvalSt e}
        → Sound (f ↠[ le ] κ) sched st → Sound κ sched st
drop-ot f le κ (sound ru ea fp (_ , ds)) = sound ru (λ k h → ea k (∨-Tʳ h)) (λ k h → fp k (∨-Tʳ h)) ds

-- and a head frame's own node sits on the path below it
head-on : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} (f : Frame Γ s u) (le : lo ≤ ℓ)
            (κ : Path Γ ℓ u t) {sched : Sched Γ} {st : EvalSt e} (k : NodeId)
        → T (any (_≡ᵇ k) (frameNodes f)) → Sound (f ↠[ le ] κ) sched st → NodeOn k κ sched st
head-on f le κ k h (sound _ ea fp (ap , _)) = node-on (ea k (∨-Tˡ h)) (fp k (∨-Tˡ h)) (ap k h)

-- a registry that only lost rows, under a counter that did not fall,
-- keeps every rule it had
sub-rule : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {sched sched′ : Sched Γ} {st st′ : EvalSt e}
         → (∀ {r} → r ∈ EvalSt.registry st′ → r ∈ EvalSt.registry st) → nodeCt sched ≤ nodeCt sched′
         → Rule sched st → Rule sched′ st′
sub-rule sb ct (rule tm fr dr) = rule (λ k a b → tm k (sb a) (sb b)) (λ a k h → <-≤-trans (fr (sb a) k h) ct) (λ a → dr (sb a))

sub-ot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t}
           {sched sched′ : Sched Γ} {st st′ : EvalSt e}
       → (∀ {r} → r ∈ EvalSt.registry st′ → r ∈ EvalSt.registry st) → nodeCt sched ≤ nodeCt sched′
       → Sound κ sched st → Sound κ sched′ st′
sub-ot sb ct (sound ru ea fp ds) = sound (sub-rule sb ct ru) (λ k h a → ea k h (sb a)) (λ k h → <-≤-trans (fp k h) ct) ds

sub-on : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {nid : NodeId} {κ : Path Γ lo s t}
           {sched sched′ : Sched Γ} {st st′ : EvalSt e}
       → (∀ {r} → r ∈ EvalSt.registry st′ → r ∈ EvalSt.registry st) → nodeCt sched ≤ nodeCt sched′
       → NodeOn nid κ sched st → NodeOn nid κ sched′ st′
sub-on sb ct (node-on ea lt op) = node-on (λ a → ea (sb a)) (<-≤-trans lt ct) op

-- EVERY RUN KEEPS THE RULE.  A run's new rows are its continuation with
-- frames pushed at nodes the counter hands out, and a row registered
-- under an inner ends where the inner's continuation does; a fan-out
-- folds each admitted row down its own path, whose nodes the rule
-- already ties to its end; a cut only removes rows.  Stated at any state
-- the rule holds in, which nothing has instantiated.  The route is one
-- structural induction over the evaluator's relations, in the shape of
-- the one that proves the room is kept.
postulate
  -- PROBED: `Probed.Rule-Kept` -- the merge's head step over a literal of
  --   deferred inners, at a store of rows sharing the merge's node and at
  --   one also holding a row through a node ending at a share's sink.
  step-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo ℓ} {f : Frame Γ s u}
                (le : lo ≤ ℓ) {κ : Path Γ ℓ u t} {now vals fin sched st r}
            → stepFrame⇓ {e = e} now f κ vals fin sched st r
            → Sound (f ↠[ le ] κ) sched st
            → Sound (f ↠[ le ] κ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
  -- PROBED: `Probed.Rule-Kept` -- the root subscribe of a merge of
  --   deferred inners, and of one reading a share whose def is deferred,
  --   asked at the root and, in the second, at the sink.  Not a κ₂
  --   carrying a node, nor a share whose def flattens.
  subscribe-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {o : Val Γ (obs u)}
                     {κ : Path Γ lo u t} {now sched st r}
                 → subscribeE⇓ {e = e} o κ now sched st r → Sound κ sched st
                 → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree κ κ₂
                 → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  -- PROBED: `Probed.Rule-Kept` -- the merge's outer fold in both
  --   programs, asked at its own path, the root and the sink.  Not a κ₂
  --   carrying a node other than the fold's own path.
  fold-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
                {now vals fin sched st r}
            → foldPath⇓ {e = e} now κ vals fin sched st r → Sound κ sched st
            → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree κ κ₂
            → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- a fold keeps the rule for its own path
fold-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
               {now vals fin sched st r}
           → foldPath⇓ {e = e} now κ vals fin sched st r → Sound κ sched st
           → Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
fold-sound {κ = κ} d so = fold-kept d so κ so (λ _ _ _ → refl)

-- a one-node frame's node is the one it names
node-eq : ∀ {x k : ℕ} → T (any (_≡ᵇ k) (x ∷ [])) → x ≡ k
node-eq {x} {k} p with x ≡ᵇ k in eq
... | true  = ≡ᵇ→≡ x k eq
... | false = ⊥-elim p

-- a frame pushed on a path the rule holds for, whose nodes sit on that
-- path, keeps it
push-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u} (f : Frame Γ s u) (le : lo ≤ ℓ)
               (κ : Path Γ ℓ u t) {sched : Sched Γ} {st : EvalSt e}
           → Sound κ sched st → (∀ k → T (any (_≡ᵇ k) (frameNodes f)) → NodeOn k κ sched st)
           → Sound (f ↠[ le ] κ) sched st
push-sound f le κ (sound ru ea fp ds) nd =
  sound ru (λ k h {r} → [ (λ a → at-end (nd k a) {r}) , (λ on → ea k on {r}) ] (∨-T h))
           (λ k h → [ (λ a → node-below (nd k a)) , fp k ] (∨-T h))
           ((λ k a → off-path (nd k a)) , ds)

-- and the outer frame, at a node on the path
push-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ u} (op : AllOp) (nid : NodeId) (le : lo ≤ ℓ)
              (κ : Path Γ ℓ u t) {sched : Sched Γ} {st : EvalSt e}
          → Sound κ sched st → NodeOn nid κ sched st → Sound (thru-outer {u = u} op nid ↠[ le ] κ) sched st
push-thru op nid le κ {sched} {st} so nd =
  push-sound (thru-outer op nid) le κ so (λ k a → subst (λ j → NodeOn j κ sched st) (node-eq a) nd)

-- a sink names no node, so the rule for it is the rule for the store
sink-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} (i : Fin n) (le : lo ≤ toℕ i)
               {sched : Sched Γ} {st : EvalSt e}
           → Rule sched st → Sound {e = e} (share-sink {Γ = Γ} {t = t} i le) sched st
sink-sound i le ru = sound ru (λ k ()) (λ k ()) tt

-- a lowered floor moves neither the nodes nor the end
lower-nodes : ∀ {n} {Γ : Ctx n} {s t lo lo′} (le : lo′ ≤ lo) (κ : Path Γ lo s t) (k : NodeId)
            → pathHasNode k (lowerFloor le κ) ≡ pathHasNode k κ
lower-nodes le root             k = refl
lower-nodes le (share-sink i p) k = refl
lower-nodes le (f ↠[ h ] p)     k = refl

lower-end : ∀ {n} {Γ : Ctx n} {s t lo lo′} (le : lo′ ≤ lo) (κ : Path Γ lo s t)
          → endOf (lowerFloor le κ) ≡ endOf κ
lower-end le root             = refl
lower-end le (share-sink i p) = refl
lower-end le (f ↠[ h ] p)     = refl

lower-distinct : ∀ {n} {Γ : Ctx n} {s t lo lo′} (le : lo′ ≤ lo) (κ : Path Γ lo s t)
               → Distinct κ → Distinct (lowerFloor le κ)
lower-distinct le root             d = d
lower-distinct le (share-sink i p) d = d
lower-distinct le (f ↠[ h ] p)     d = d

-- A ROW REGISTERED FOR A PATH THE RULE HOLDS FOR KEEPS IT, when the row
-- ends where the path does, every node it runs through is either one of
-- the path's or one the counter has just handed out, and the rule for
-- the path makes the row's own path distinct.
register-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s u} {κ : Path Γ lo s t}
                   {sched sched′ : Sched Γ} {st : EvalSt e}
                   (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
               → nodeCt sched ≤ nodeCt sched′ → endOf p ≡ endOf κ
               → (∀ k → T (pathHasNode k p) → T (pathHasNode k κ) ⊎ (nodeCt sched ≤ k × k < nodeCt sched′))
               → (Sound κ sched st → Distinct p)
               → Sound κ sched st → Sound κ sched′ (register rid rs p st)
register-sound {κ = κ} {sched} {sched′} {st} rid rs p ct ee cls dp so@(sound (rule tm fr dr) ea fp ds) =
  sound (rule tm′ fr′ dr′) ea′ (λ k h → <-≤-trans (fp k h) ct) ds
  where
  old-new : ∀ k {r} → r ∈ EvalSt.registry st → T (rowThrough k r) → T (pathHasNode k p)
          → rowEnd r ≡ endOf p
  old-new k r∈ th hp with cls k hp
  ... | inj₁ onκ      = trans (ea k onκ r∈ th) (sym ee)
  ... | inj₂ (le , _) = ⊥-elim (<-irrefl refl (<-≤-trans (fr r∈ k th) le))
  tm′ : Termini (register rid rs p st)
  tm′ k a b th th′ with ∈-++⁻ (EvalSt.registry st) a | ∈-++⁻ (EvalSt.registry st) b
  ... | inj₁ a′          | inj₁ b′          = tm k a′ b′ th th′
  ... | inj₁ a′          | inj₂ (here refl) = old-new k a′ th th′
  ... | inj₂ (here refl) | inj₁ b′          = sym (old-new k b′ th′ th)
  ... | inj₂ (here refl) | inj₂ (here refl) = refl
  fr′ : FreshRows sched′ (register rid rs p st)
  fr′ a k th with ∈-++⁻ (EvalSt.registry st) a
  ... | inj₁ a′ = <-≤-trans (fr a′ k th) ct
  ... | inj₂ (here refl) with cls k th
  ...   | inj₁ onκ      = <-≤-trans (fp k onκ) ct
  ...   | inj₂ (_ , lt) = lt
  ea′ : ∀ k → T (pathHasNode k κ) → EndsAt k (endOf κ) (register rid rs p st)
  ea′ k onκ a th with ∈-++⁻ (EvalSt.registry st) a
  ... | inj₁ a′          = ea k onκ a′ th
  ... | inj₂ (here refl) = ee
  dr′ : ∀ {r} → r ∈ EvalSt.registry (register rid rs p st) → rowDistinct r
  dr′ a with ∈-++⁻ (EvalSt.registry st) a
  ... | inj₁ a′          = dr a′
  ... | inj₂ (here refl) = dp so

-- AND IT KEEPS EVERY TERMINUS OFF THE PATH, when every node the row
-- runs through is the path's or one at or above the counter.
ends-register : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s u} {κ : Path Γ lo s t}
                  {sched : Sched Γ} {st : EvalSt e}
                  (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
              → (∀ k → T (pathHasNode k p) → T (pathHasNode k κ) ⊎ nodeCt sched ≤ k)
              → EndsKept κ sched st (register rid rs p st)
ends-register {st = st} rid rs p cls k k< ne ea a th with ∈-++⁻ (EvalSt.registry st) a
... | inj₁ a′          = ea a′ th
... | inj₂ (here refl) with cls k th
...   | inj₁ on = ⊥-elim (ne on)
...   | inj₂ le = ⊥-elim (<-irrefl refl (<-≤-trans k< le))

-- so a slot's row, the trigger's path with its floor lowered to the
-- share's, keeps it
row-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} (i : Fin n) (below : toℕ i < lo)
              (κ : Path Γ lo (lookup Γ i) t) (sched : Sched Γ) (st : EvalSt e)
          → Sound κ sched st
          → Sound κ (record sched { mint = setAt regᵏ (suc (freshId regᵏ (Sched.mint sched))) (Sched.mint sched) })
              (register (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ) st)
row-sound i below κ sched st so =
  register-sound {sched = sched} {st = st}
    (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ) ≤-refl (lower-end below κ)
    (λ k on → inj₁ (subst T (lower-nodes below κ k) on)) (λ so′ → lower-distinct below κ (distinct so′)) so

-- CONSISTENCY MOVES ACROSS A STATE THAT READS THE FRAME'S NODES BACK
-- THE SAME.
consistentF-move : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                   (f : Frame Γ s u) (h : HeldF f) {st st′ : EvalSt e}
                 → (∀ k → T (any (_≡ᵇ k) (frameNodes f))
                        → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
                 → ConsistentF f h st → ConsistentF f h st′
consistentF-move (map-f _)              h mv c = tt
consistentF-move (scan-f _ nid)         h mv c = trans (mv nid (self-node nid [])) c
consistentF-move (take-f nid)           h mv c = trans (mv nid (self-node nid [])) c
consistentF-move (batchSync-f nid)      h mv c = trans (mv nid (self-node nid [])) c
consistentF-move (from-inner _ nid j)   h mv c = trans (mv nid (self-node nid (j ∷ []))) c
consistentF-move (thru-outer _ nid)     h mv c = trans (mv nid (self-node nid [])) c

-- THE GROUND SURVIVES A STEP THAT READS THE PATH'S OWN NODES BACK THE
-- SAME AND DOES NOT LOWER THE COUNTER.  The two hypotheses are what a
-- frame's agreement and its freshness each stand on; every arm that
-- writes its own node spends exactly this, and so does every frame's
-- step.
holdsF-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
              (f : Frame Γ s u) (h : HeldF f) {sched sched′ : Sched Γ} {st st′ : EvalSt e}
            → (∀ k → T (any (_≡ᵇ k) (frameNodes f)) → k < nodeCt sched
                   → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
            → nodeCt sched ≤ nodeCt sched′
            → HoldsF f h sched st → HoldsF f h sched′ st′
holdsF-step f h mv ct (c , fr) =
  consistentF-move f h (λ k on → mv k on (nodes-below _ fr k on)) c , mapᵃ (λ lt → <-≤-trans lt ct) fr

holdsFs-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
               (κ : Path Γ lo u t) (pfs : PreFs κ) {sched sched′ : Sched Γ} {st st′ : EvalSt e}
             → (∀ k → T (pathHasNode k κ) → k < nodeCt sched
                    → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
             → nodeCt sched ≤ nodeCt sched′
             → HoldsFs κ pfs sched st → HoldsFs κ pfs sched′ st′
holdsFs-step root             _         mv ct h = tt
holdsFs-step (share-sink _ _) _         mv ct h = tt
holdsFs-step (f ↠[ _ ] κ)     (h , pfs) {sched} {sched′} {st} {st′} mv ct (hf , ap , hs) =
    holdsF-step f h {sched} {sched′} {st} {st′} (λ k on → mv k (∨-Tˡ on)) ct hf
  , ap
  , holdsFs-step κ pfs (λ k on → mv k (∨-Tʳ on)) ct hs

holds-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} {m}
             (κ : Path Γ lo u t) (pre : Pre κ) {sched sched′ : Sched Γ} {st st′ : EvalSt e}
           → (∀ k → T (pathHasNode k κ) → k < nodeCt sched
                  → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
           → nodeCt sched ≤ nodeCt sched′
           → (Fell m sched st → Fell m sched′ st′)
           → (Sound κ sched st → Sound κ sched′ st′)
           → PreHolds m κ pre sched st → PreHolds m κ pre sched′ st′
holds-step κ (standing pfs) mv ct fl sd (grounded h so) = grounded (holdsFs-step κ pfs mv ct h) (sd so)
holds-step κ fallen         mv ct fl sd (grounded h so) = grounded (fl h) (sd so)

-- WHAT A FOLD KEEPS FOR THE FRAME BENEATH IT.  A frame that hands a
-- burst up the path and gets the path's successor back has its own
-- node between the two, and the path above has no business with it: a
-- standing answer says the counter did not fall, and that every node
-- below it that is none of the path's own, and whose rows end where
-- the path does, reads back as it did and still has its rows end
-- there, so the frame beneath stands on its own in the state handed
-- back.  A fallen answer keeps nothing, because nothing beneath a
-- fallen path holds candidates to keep.
--
-- THE TERMINUS IS WHAT A STANDING PATH ENDING AT A SINK OWES.  Its
-- fold fans out at the sink without connecting, and the fan-out writes
-- the nodes of the rows it folds; a row on a share sits above that
-- share's index, so it never ends at the sink, and a node whose rows
-- all end there is none of theirs.  Every frame beneath has its nodes'
-- rows ending where its path does, which is where the path above it
-- ends.
Kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
       (κ : Path Γ lo u t) → Pre κ → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Kept κ (standing _) sched st sched′ st′ =
  nodeCt sched ≤ nodeCt sched′
  × (∀ k → k < nodeCt sched → (T (pathHasNode k κ) → ⊥) → EndsAt k (endOf κ) st
       → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
  × EndsKept κ sched st st′
Kept κ fallen sched st sched′ st′ = ⊤

-- a step that writes only at or above the counter, advances it, and
-- keeps the path's terminus keeps everything
kept-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
            (κ : Path Γ lo u t) (pre : Pre κ) {sched sched′ : Sched Γ} {st st′ : EvalSt e}
          → PreservedBelow (nodeCt sched) st st′ → nodeCt sched ≤ nodeCt sched′
          → EndsKept κ sched st st′
          → Kept κ pre sched st sched′ st′
kept-step κ (standing _) pr ct ek = ct , (λ k k< _ _ → below pr k k<) , ek
kept-step κ fallen       pr ct ek = tt

-- a step that only lost rows keeps every terminus
ends-sub : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (κ : Path Γ lo u t) {sched : Sched Γ} {st st′ : EvalSt e}
         → (∀ {r} → r ∈ EvalSt.registry st′ → r ∈ EvalSt.registry st) → EndsKept κ sched st st′
ends-sub κ sb k _ _ ea a∈ = ea (sb a∈)

-- and what was kept from a counter is kept from an equal one
kept-in : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
          (κ : Path Γ lo u t) (pre : Pre κ) {sched sched₁ sched′ : Sched Γ} {st st′ : EvalSt e}
        → nodeCt sched₁ ≡ nodeCt sched
        → Kept κ pre sched₁ st sched′ st′ → Kept κ pre sched st sched′ st′
kept-in κ (standing _) eq (ct , kp , ek) =
  subst (_≤ _) eq ct , (λ k k< → kp k (subst (k <_) (sym eq) k<)) , λ k k< → ek k (subst (k <_) (sym eq) k<)
kept-in κ fallen       eq kp        = tt

-- ONE CALL MADE TO A CONTINUATION, AS THE CALLER MADE IT.  The trace
-- a subscribe answers with is a list of these, oldest first, and a
-- fold applied to the fields in order is the call itself -- which is
-- what makes the replay compute the successor rather than approximate
-- it.  The room proof travels with the call because the fold demands
-- it and the replayer holds no other.
record Call {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
            (P : Val Γ u → Set₁) (κ : Path Γ lo u t) (pre : Pre κ) : Set₁ where
  constructor call
  field
    now   : Tick
    vals  : List (Val Γ u)
    col   : Column κ P pre vals
    fin   : Bool
    sched : Sched Γ
    st    : EvalSt e
    room  : Room m sched st
    holds : PreHolds m κ pre sched st

-- THE CONTINUATION: THE REST OF THE PATH, AS A FOLD THAT TAKES
-- CANDIDATES AND ANSWERS AT THE ROOT.  A subscribe never sees the
-- frames above it; it sees one function that takes a burst at its own
-- element type, a candidate column over that burst, the completion
-- flag, and a state under the ceiling, and hands back the root-typed
-- stream the fold produced, the state after it, the derivation, the
-- continuation's own updated state, and its SUCCESSOR -- the same
-- closure with the candidates it just computed closed over in place
-- of the ones it was built with, which is where a stateful frame's
-- held candidates live.  The record is coinductive because the root's
-- successor is the root.
--
-- THE STATE TYPE IS EXPLICIT AND STAYS IN `Set`, which is exactly why
-- it cannot carry a candidate; it is threaded unchanged and every
-- caller instantiates it at the unit.
--
-- THE FOLD STANDS ON ITS GROUND AND HANDS BACK ITS SUCCESSOR'S.  The
-- premise is `PreHolds` at the state folded in; the answer carries the
-- successor's own `Pre` and its `PreHolds` at the state folded out, so
-- a caller that threads states through folds alone never has to prove
-- consistency of anything -- it is handed it.  A caller that writes
-- the store itself between two folds owes the re-establishment, and
-- that is exactly the arm writing its OWN node, which touches no other
-- frame's node by freshness.
record RP {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
          (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t) (pre : Pre κ) : Set₁

-- WHAT ONE FOLD ANSWERS: the root stream and the state after it, the
-- derivation, the successor with the ground it stands on in that
-- state, what it kept for the frame beneath, and the state it was
-- threaded.
record Ans {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
           (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t)
           (now : Tick) (vals : List (Val Γ u)) (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e) : Set₁ where
  inductive
  constructor ans
  field
    out    : Stream Γ t
    sched′ : Sched Γ
    st′    : EvalSt e
    der    : foldPath⇓ {e = e} now κ vals fin sched st (out , sched′ , st′)
    pre′   : Pre κ
    holds′ : PreHolds m κ pre′ sched′ st′
    kept   : Kept κ pre′ sched st sched′ st′
    next   : RP {e = e} m P S κ pre′
    s′     : S
open Ans public using (out; der; kept; next)

record RP {n} {Γ} {t} {e} m {u} {lo} P S κ pre where
  coinductive
  field
    fold : S → (now : Tick) (vals : List (Val Γ u)) → Column κ P pre vals
         → (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → PreHolds m κ pre sched st
         → Ans {e = e} m P S κ now vals fin sched st
open RP public

-- one call applied: the fold at the call's own fields
apply : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ}
      → RP {e = e} m P S κ pre → S → (c : Call {e = e} m P κ pre)
      → Ans {e = e} m P S κ (Call.now c) (Call.vals c) (Call.fin c) (Call.sched c) (Call.st c)
apply rp s c = fold rp s (Call.now c) (Call.vals c) (Call.col c) (Call.fin c)
                    (Call.sched c) (Call.st c) (Call.room c) (Call.holds c)

-- THE TRACE: THE CALLS A SUBSCRIBE MADE TO ITS CONTINUATION, IN ORDER,
-- EACH TYPED AGAINST THE SUCCESSOR THE ONE BEFORE IT ANSWERED WITH.
-- Replaying it is applying the fold to each call in turn, and that is
-- not a second computation of the successor to be proven equal to the
-- first: it IS the successor, by the type, so a subscribe answers with
-- the trace and nothing else about its continuation.  A frame arm
-- translates its source's trace through the frame it pushed, call by
-- call, and the translation's end is the successor of the continuation
-- it was handed -- which is what the exit frame's peel used to do.
--
-- AND THE TRACE STOPS WHERE THE PATH FELL.  A connect never calls the
-- continuation it was handed -- the trigger receives the definition's
-- values through the row it registered, folded raw -- and every fold
-- above a fall reads the store and calls nothing it closed over, so
-- there is no successor to compute past that point.  `fellᵗ` records
-- the fallen continuation the fall left and the state it was threaded,
-- so a frame that goes on calling after its source fell has a fold to
-- call and a trace to append; the arm above still owes the fall
-- itself, as the ground its answer ends on.
data Trace {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
           (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t)
         : (pre : Pre κ) → RP {e = e} m P S κ pre → S → Set₁ where
  []ᵗ   : ∀ {pre rp s} → Trace m P S κ pre rp s
  fellᵗ : ∀ {pre rp s} → RP {e = e} m P S κ fallen → S → Trace m P S κ pre rp s
  _∷ᵗ_  : ∀ {pre rp s} (c : Call {e = e} m P κ pre)
        → Trace m P S κ (Ans.pre′ (apply rp s c)) (next (apply rp s c)) (Ans.s′ (apply rp s c))
        → Trace m P S κ pre rp s

-- where a trace ends: the ground it left the path on
endPre : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
         {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
       → Trace {e = e} m P S κ pre rp s → Pre κ
endPre {pre = pre} []ᵗ = pre
endPre (fellᵗ _ _)     = fallen
endPre (c ∷ᵗ tr)       = endPre tr

-- the continuation it left standing there, and the state
endRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
      → (tr : Trace {e = e} m P S κ pre rp s) → RP {e = e} m P S κ (endPre tr)
endRP {rp = rp} []ᵗ = rp
endRP (fellᵗ rp′ _) = rp′
endRP (c ∷ᵗ tr)     = endRP tr

endS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
       {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
     → Trace {e = e} m P S κ pre rp s → S
endS {s = s} []ᵗ  = s
endS (fellᵗ _ s′) = s′
endS (c ∷ᵗ tr)    = endS tr

-- ONE TRACE AFTER ANOTHER: the second picks up where the first ended,
-- and nothing is recorded past a fall -- whether the first fell, or
-- began on fallen ground and made no call.  A call made to a fallen
-- continuation is a fold of the store and computes no successor, so
-- the record has nothing to say about it.
_++ᵗ_ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
      → (tr : Trace {e = e} m P S κ pre rp s)
      → Trace {e = e} m P S κ (endPre tr) (endRP tr) (endS tr)
      → Trace {e = e} m P S κ pre rp s
fellᵗ rp′ s′ ++ᵗ _   = fellᵗ rp′ s′
(c ∷ᵗ tr)    ++ᵗ tr′ = c ∷ᵗ (tr ++ᵗ tr′)
_++ᵗ_ {pre = standing _} []ᵗ tr′ = tr′
_++ᵗ_ {pre = fallen}     []ᵗ tr′ = []ᵗ

-- where a walk continued from one ground ends: where the second half
-- ended if the first stood, fallen if it fell
joinPre : ∀ {n} {Γ : Ctx n} {lo u t} {κ : Path Γ lo u t} → Pre κ → Pre κ → Pre κ
joinPre (standing _) q = q
joinPre fallen       q = fallen

end-++ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
         {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
       → (tr : Trace {e = e} m P S κ pre rp s)
       → (tr′ : Trace {e = e} m P S κ (endPre tr) (endRP tr) (endS tr))
       → endPre (tr ++ᵗ tr′) ≡ joinPre (endPre tr) (endPre tr′)
end-++ (fellᵗ _ _)  tr′ = refl
end-++ (c ∷ᵗ tr)    tr′ = end-++ tr tr′
end-++ {pre = standing _} []ᵗ tr′ = refl
end-++ {pre = fallen}     []ᵗ tr′ = refl

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the
-- statement the whole argument turns on -- given any continuation
-- above and any state under the ceiling, a subscription derivation
-- exists whose answer is at the root, and the calls made to the
-- continuation come back as a trace whose end stands on the ground it
-- claims and kept what a frame beneath needs kept.
--
-- IT LIVES IN `Set₁` BECAUSE THE OBSERVABLE ARM QUANTIFIES OVER THE
-- CONTINUATION'S STATE TYPE, and nothing else about it moved: the
-- data arms are the polymorphic unit, the product and sum arms are
-- products and sums of candidates, and the list arm is `All`.
--
-- THE RECURSIVE OCCURRENCE IS THE CONTINUATION'S PARAMETER.  `Red m u`
-- appears once in the observable arm, as the predicate `RP` is
-- indexed by, at a strictly smaller type.  That is the Girard-Tait
-- descent, unchanged; what changed is that the answer no longer
-- carries it, so the answer can be at `t`.
--
-- THE CEILING IS AN INDEX AND THE PREDICATE GROWS WITH IT -- a larger
-- ceiling admits more states, so it quantifies over more -- while a
-- connect descends to a SMALLER one.  It is met here by never asking
-- the lower ceiling's candidates to come back UP: they go down the raw
-- continuation at the ceiling the connect peeled to, and a
-- continuation built at the higher ceiling that has to cross to the
-- lower one is dropped to it, its candidates forgotten.  What comes
-- back up is not a candidate but a `fallen` successor, which is what
-- the caller's own ceiling can hold: it stands on the room having
-- fallen, and re-vouches from the store at the peeled accessibility
-- on every later call.  Weakening only ever runs from the higher
-- ceiling to the lower, which is the direction it is sound in.
--
-- DEAD ROUTE: re-indexing the candidate by the room WHILE THE ANSWER
--   STILL CARRIES A SATISFACTION COLUMN.  The connect's def comes back
--   proven at the inner ceiling and the arm owes the column at the
--   outer; weakening runs the other way and no instance of it closes
--   the gap.  Bypassed rather than reopened: nothing here comes back
--   proven, because nothing comes back at the element type at all.
Red : ∀ {n} {Γ : Ctx n} (m : ℕ) (t : Ty) → Val Γ t → Set₁
Red m unitᵗ     _        = ⊤
Red m boolᵗ     _        = ⊤
Red m natᵗ      _        = ⊤
Red m uniqᵗ     _        = ⊤
Red m (s ×ᵗ t)  (a , b)  = Red m s a × Red m t b
Red m (s +ᵗ t)  (inj₁ a) = Red m s a
Red m (s +ᵗ t)  (inj₂ b) = Red m t b
Red m (listᵗ t) vs       = All (Red m t) vs
Red {Γ = Γ} m (obs u) b =
  ∀ {S : Set} {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (pre : Pre κ)
  → (rp : RP {e = e} m (Red m u) S κ pre) (s : S)
  → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
  → PreHolds m κ pre sched st
  → Σ (Stream Γ t × Sched Γ × EvalSt e)
      (λ r → subscribeE⇓ {e = e} b κ now sched st r
           × Σ (Trace {e = e} m (Red m u) S κ pre rp s)
               (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                     × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's closure pairs a term with one
-- such environment, so the fundamental theorem at terms has to be
-- stated under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} (m : ℕ) {Θ : List Ty} → Env Γ Θ → Set₁
RedEnv m []ᵉ                  = ⊤
RedEnv m (_∷ᵉ_ {s = t} v vs)  = Red m t v × RedEnv m vs

-- an entry of a reducible environment is reducible
redLookup : ∀ {n} {Γ : Ctx n} {m Θ t} (ρ : Env Γ Θ) → RedEnv m ρ
          → (x : t ∈ Θ) → Red m t (lookupEnv ρ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- THE LIST FOLD'S ACCUMULATOR LOOP, WITH THE STEP TAKEN AS A
-- HYPOTHESIS.  The step is one instance of the term face at an
-- environment two entries longer, and it does not vary along the list,
-- so the walk over the list is an ordinary recursion outside the
-- theorem's own cycle.
redFoldVals : ∀ {n} {Γ : Ctx n} {m Θ s u} (f : Tm Γ [] [] (s ∷ u ∷ Θ) u)
              (ρ : Env Γ Θ)
            → (∀ {x : Val Γ s} {ac : Val Γ u} → Red m s x → Red m u ac
                 → Red m u (evalWith f (x ∷ᵉ ac ∷ᵉ ρ)))
            → {vs : List (Val Γ s)} → All (Red m s) vs
            → {ac : Val Γ u} → Red m u ac
            → Red m u (foldVals f ρ vs ac)
redFoldVals f ρ step []       rac = rac
redFoldVals f ρ step (p ∷ ps) rac = redFoldVals f ρ step ps (step p rac)

-- A chain registered on a share sinks STRICTLY above that share, so
-- the room left above the floor is what shrinks at every fan-out and
-- the path itself never has to.

------------------------------------------------------------------
-- A PURE FRAME AS ONE STEP, AND WHAT THE LIVE FOLD OVER IT SPENDS.
------------------------------------------------------------------

-- what a step hands on: the group, the flag, the state, and what the
-- frame holds now
record Stepped {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u) : Set where
  constructor stepped
  field
    outs   : List (Val Γ u)
    fin″   : Bool
    sched″ : Sched Γ
    st″    : EvalSt e
    held   : HeldF f
open Stepped public

-- WHAT A PURE FRAME IS, TO THE FOLD: a function of what it holds and
-- what arrives, with the facts the generic fold spends.  The step is
-- the evaluator's own dispatch read at the held state, and the
-- derivation says so under agreement; the candidates go through it
-- beside the values; it stays in agreement with what it now holds; it
-- writes only its own nodes and moves the counter not at all.  The
-- flatteners are not of this shape -- they subscribe -- and have folds
-- of their own.
record FrameStep {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u)
                 (P : Val Γ s → Set₁) (P′ : Val Γ u → Set₁)
                 (Held : HeldF f → Set₁) : Set₁ where
  field
    step      : HeldF f → List (Val Γ s) → Bool → Sched Γ → EvalSt e → Stepped {e = e} f
    step-⇓    : ∀ {lo} {κ : Path Γ lo u t} {now} (h : HeldF f) vals fin sched st
              → ConsistentF f h st
              → let r = step h vals fin sched st
                in stepFrame⇓ {e = e} now f κ vals fin sched st
                     (injectRoot (outs r , fin″ r , sched″ r , st″ r))
    step-red  : ∀ {h vals fin sched st} → All P vals → Held h
              → let r = step h vals fin sched st
                in All P′ (outs r) × Held (held r)
    step-cons : ∀ h vals fin sched st → ConsistentF f h st
              → let r = step h vals fin sched st
                in ConsistentF f (held r) (st″ r)
    step-off  : ∀ h vals fin sched st k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
              → lookupNode k (EvalSt.nodes (st″ (step h vals fin sched st)))
              ≡ lookupNode k (EvalSt.nodes st)
    step-ct   : ∀ h vals fin sched st → nodeCt (sched″ (step h vals fin sched st)) ≡ nodeCt sched
    step-reg  : ∀ h vals fin sched st {r} → r ∈ EvalSt.registry (st″ (step h vals fin sched st))
              → r ∈ EvalSt.registry st
open FrameStep public

-- THE FRAME'S GROUND OVER THE PATH'S: live at what it now holds where
-- the path stands, fallen where the path fell.
headPre : ∀ {n} {Γ : Ctx n} {lo ℓ s u t} {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
        → HeldF f → Pre κ → Pre (f ↠[ le ] κ)
headPre h (standing pfs) = standing (h , pfs)
headPre h fallen         = fallen

-- and it holds where the frame's own ground held before the fold and
-- the fold kept the frame's nodes
headHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
            {sched₁ sched₂ : Sched Γ} {st₁ st₂ : EvalSt e}
          → HoldsF f h sched₁ st₁ → Apart κ f → Sound (f ↠[ le ] κ) sched₁ st₁
          → (p : Pre κ) → PreHolds m κ p sched₂ st₂ → Kept κ p sched₁ st₁ sched₂ st₂
          → Sound (f ↠[ le ] κ) sched₂ st₂
          → PreHolds m (f ↠[ le ] κ) (headPre h p) sched₂ st₂
headHolds f le κ h (c , fr) ap so₁ (standing pfs) (grounded hs _) (ct , kp , _) so =
  grounded
    ( ( consistentF-move f h (λ k on → kp k (nodes-below _ fr k on) (ap k on) (ends so₁ k (∨-Tˡ on))) c
      , mapᵃ (λ lt → <-≤-trans lt ct) fr )
    , ap
    , hs )
    so
headHolds f le κ h hf ap so₁ fallen (grounded fell _) kp so = grounded fell so

-- what the frame keeps for the frame beneath it: what the path kept,
-- through its own step
headKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u}
           (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
           {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
         → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
                → lookupNode k (EvalSt.nodes st₁) ≡ lookupNode k (EvalSt.nodes st))
         → nodeCt sched₁ ≡ nodeCt sched → EndsKept (f ↠[ le ] κ) sched st st₁
         → (p : Pre κ) → Kept κ p sched₁ st₁ sched₂ st₂ → (h : HeldF f)
         → Kept (f ↠[ le ] κ) (headPre h p) sched st sched₂ st₂
headKept f le κ off ct eks (standing pfs) (ct₂ , kp , ek) h =
    subst (_≤ _) ct ct₂
  , (λ k k< ne ea → trans (kp k (subst (k <_) (sym ct) k<) (λ on → ne (∨-Tʳ on)) (eks k k< ne ea))
                          (off k (λ on → ne (∨-Tˡ on))))
  , λ k k< ne ea → ek k (subst (k <_) (sym ct) k<) (λ on → ne (∨-Tʳ on)) (eks k k< ne ea)
headKept f le κ off ct eks fallen kp h = tt

-- THE ARM READS THE PATH'S GROUND BACK OUT OF THE FRAME'S, which is
-- where a frame arm's answer comes from once its source has answered
-- about the path with the frame pushed.
unheadHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
              (p : Pre κ) {sched : Sched Γ} {st : EvalSt e}
            → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st → PreHolds m κ p sched st
unheadHolds f le κ h (standing pfs) (grounded (_ , _ , hs) so) = grounded hs (drop-ot f le κ so)
unheadHolds f le κ h fallen         (grounded fell so)         = grounded fell (drop-ot f le κ so)

-- and what the frame kept for the arm's caller, given that the arm's
-- own install sat at or above the counter it began at and wrote
-- nothing below it
unheadKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f) (p : Pre κ)
             {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
           → (∀ k → k < nodeCt sched → T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
           → nodeCt sched ≤ nodeCt sched₁
           → (∀ k → k < nodeCt sched → lookupNode k (EvalSt.nodes st₁) ≡ lookupNode k (EvalSt.nodes st))
           → EndsKept κ sched st st₁
           → Kept (f ↠[ le ] κ) (headPre h p) sched₁ st₁ sched₂ st₂
           → Kept κ p sched st sched₂ st₂
unheadKept f le κ h (standing pfs) above ct pr eks (ct₂ , kp , ek) =
    ≤-trans ct ct₂
  , (λ k k< ne ea → trans (kp k (<-≤-trans k< ct) (λ on → [ above k k< , ne ] (∨-T on)) (eks k k< ne ea)) (pr k k<))
  , λ k k< ne ea → ek k (<-≤-trans k< ct) (λ on → [ above k k< , ne ] (∨-T on)) (eks k k< ne ea)
unheadKept f le κ h fallen above ct pr eks kp = tt

-- THE CALL A LIVE FRAME MAKES ABOVE IT, FOR THE CALL MADE TO IT: the
-- step's group with the candidates through the step, at the step's
-- state, on the ground the step carried up.  One function, because
-- the fold makes this call and the arm's translation re-makes it, and
-- the two have to be the same term.
headCall : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {f : Frame Γ s u}
           {P : Val Γ s → Set₁} {P′ : Val Γ u → Set₁} {Held : HeldF f → Set₁} {le : lo ≤ ℓ}
           (fs : FrameStep {e = e} f P P′ Held) (h : HeldF f) → Held h
         → (κ : Path Γ ℓ u t) (pfs : PreFs κ)
         → Call {e = e} m P (f ↠[ le ] κ) (standing (h , pfs))
         → Call {e = e} m P′ κ (standing pfs)
headCall {f = f} {le = le} fs h rh κ pfs (call now vals col fin sched st rm (grounded ((c , fr) , ap , hs) so)) =
  let r = step fs h vals fin sched st
  in call now (outs r) (ofColumn κ (standing pfs) (proj₁ (step-red fs col rh))) (fin″ r) (sched″ r) (st″ r)
       (room-keeps (stepFrame-keeps (step-⇓ fs {κ = κ} {now = now} h vals fin sched st c)) rm)
       (grounded
         (holdsFs-step κ pfs
           (λ k on k< → step-off fs h vals fin sched st k (λ onF → ap k onF on))
           (subst (nodeCt sched ≤_) (sym (step-ct fs h vals fin sched st)) ≤-refl) hs)
         (drop-ot f le κ (step-kept le (step-⇓ fs {κ = κ} {now = now} h vals fin sched st c) so)))

-- candidates through a function, pointwise
mapAll : ∀ {n} {Γ : Ctx n} {s u} {P : Val Γ s → Set₁} {P′ : Val Γ u → Set₁} {g : Val Γ s → Val Γ u}
       → (∀ {v} → P v → P′ (g v)) → {vs : List (Val Γ s)} → All P vs → All P′ (map g vs)
mapAll gp []ᵃ       = []ᵃ
mapAll gp (p ∷ᵃ ps) = gp p ∷ᵃ mapAll gp ps

-- THE MAP FRAME'S STEP.  Stateless: it maps the values and their
-- candidates through the closure and touches nothing.
mapStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ s u)
          {P : Val Γ s → Set₁} {P′ : Val Γ u → Set₁}
        → (∀ {v} → P v → P′ (applyClo fn v))
        → FrameStep {e = e} (map-f fn) P P′ (λ _ → ⊤)
mapStep fn g = record
  { step      = λ _ vals fin sched st → stepped (map (applyClo fn) vals) fin sched st tt
  ; step-⇓    = λ _ _ _ _ _ _ → step-map
  ; step-red  = λ ps _ → mapAll g ps , tt
  ; step-cons = λ _ _ _ _ _ _ → tt
  ; step-off  = λ _ _ _ _ _ _ _ → refl
  ; step-ct   = λ _ _ _ _ _ → refl
  ; step-reg  = λ _ _ _ _ _ r∈ → r∈ }

------------------------------------------------------------------
-- THE FRAME CONTINUATION THAT REACHES NO CYCLE.
------------------------------------------------------------------

-- THE ROOT MINTS THE BURST FROM NOTHING, and its state is the unit.
rootRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo} {P : Val Γ t → Set₁} {pre : Pre {Γ = Γ} (root {lo = lo} {t = t})}
       → RP {e = e} m {lo = lo} P ⊤ root pre
fold (rootRP {pre = pre}) tt now vals _ fin sched st rm h =
  ans _ sched st fold-root pre h (kept-step root pre (pres (λ _ _ → refl)) ≤-refl (λ _ _ _ ea → ea)) rootRP tt

-- A CONTINUATION THAT THREADS NO STATE THREADS ANY: the fallen fold is
-- built at the unit and a live frame over it carries its caller's.
dropS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
        {κ : Path Γ lo u t} {pre : Pre κ}
      → RP {e = e} m P ⊤ κ pre → RP {e = e} m P S κ pre
fold (dropS rp) s now vals col fin sched st rm h =
  let an = fold rp tt now vals col fin sched st rm h
  in ans (out an) (Ans.sched′ an) (Ans.st′ an) (der an) (Ans.pre′ an) (Ans.holds′ an) (kept an)
         (dropS (next an)) s

------------------------------------------------------------------
-- A FRAME THAT SUBSCRIBES, AND WHAT ITS FOLD HANDS BACK.
------------------------------------------------------------------

-- THE FLATTENER FRAMES ARE NOT STEPS.  A pure frame's step is a
-- function of what it holds and what arrives; the outer's step
-- subscribes every observable that arrives and the inner's finish
-- drains a queue of them, so each step is itself a run of the
-- candidate above -- calls made to the continuation, a trace of them,
-- and ground the frame stands on afterwards.  What such a step hands
-- back is a STAGE: the fold's answer beside the trace it made above,
-- with the frame's own ground and what it kept read off the trace's
-- end.  The stages of one step are joined like traces, and the join
-- is where the frame's ground and the path's are re-established once
-- rather than at every arm.

-- a node the frame does not name is not its head node
head-off : ∀ (j : ℕ) (ns : List ℕ) (k : ℕ)
         → (T (any (_≡ᵇ k) (j ∷ ns)) → ⊥) → (j ≡ᵇ k) ≡ false
head-off j ns k ne with j ≡ᵇ k
... | true  = ⊥-elim (ne tt₀)
... | false = refl

-- every node a standing path names sits below the counter
path-below : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
             (κ : Path Γ lo u t) (pfs : PreFs κ) {sched : Sched Γ} {st : EvalSt e}
           → HoldsFs κ pfs sched st → ∀ k → T (pathHasNode k κ) → k < nodeCt sched
path-below root             _         hs k ()
path-below (share-sink _ _) _         hs k ()
path-below (f ↠[ _ ] κ) (h , pfs) ((_ , fr) , _ , hs) k on =
  [ nodes-below _ fr k , path-below κ pfs hs k ] (∨-T on)

-- so the node the counter names is on no standing path
fresh-apart : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
              (κ : Path Γ lo u t) (pfs : PreFs κ) {sched : Sched Γ} {st : EvalSt e}
            → HoldsFs κ pfs sched st
            → ∀ k → T (nodeCt sched ≡ᵇ k) → T (pathHasNode k κ) → ⊥
fresh-apart κ pfs hs k on onκ = subst T (<→≢ᵇ (path-below κ pfs hs k onκ)) on

-- an inner frame minted at the counter is apart from a path its
-- flattener's node is apart from
apart-fi : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (op : AllOp) (nid : NodeId)
           (κ : Path Γ lo u t) (pfs : PreFs κ) {sched : Sched Γ} {st : EvalSt e}
         → HoldsFs κ pfs sched st
         → (∀ k → T (nid ≡ᵇ k) → T (pathHasNode k κ) → ⊥)
         → Apart κ (from-inner {s = u} op nid (nodeCt sched))
apart-fi op nid κ pfs hs apN k on onκ =
  [ (λ a → apN k a onκ)
  , (λ b → [ (λ c → fresh-apart κ pfs hs k c onκ) , (λ ()) ] (∨-T b)) ] (∨-T on)

-- nothing moved, nothing to keep
kept-refl : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
            (κ : Path Γ lo u t) (p : Pre κ) {sched : Sched Γ} {st : EvalSt e}
          → Kept κ p sched st sched st
kept-refl κ (standing _) = ≤-refl , (λ _ _ _ _ → refl) , λ _ _ _ ea → ea
kept-refl κ fallen       = tt

-- the join of grounds is idempotent, and a ground that absorbs the
-- next absorbs what the next absorbs
join-idem : ∀ {n} {Γ : Ctx n} {lo u t} {κ : Path Γ lo u t} (p : Pre κ) → joinPre p p ≡ p
join-idem (standing _) = refl
join-idem fallen       = refl

join-chain : ∀ {n} {Γ : Ctx n} {lo u t} {κ : Path Γ lo u t} (p q r : Pre κ)
           → joinPre p q ≡ q → joinPre q r ≡ r → joinPre p r ≡ r
join-chain (standing _) q r _    _  = refl
join-chain fallen       _ r refl e₂ = e₂

-- what was kept across two runs was kept across both
kept-trans : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
             (κ : Path Γ lo u t) (pfs : PreFs κ) (p′ : Pre κ)
             {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
           → Kept κ (standing pfs) sched st sched₁ st₁ → Kept κ p′ sched₁ st₁ sched₂ st₂
           → Kept κ p′ sched st sched₂ st₂
kept-trans κ pfs (standing _) (ct₁ , k₁ , e₁) (ct₂ , k₂ , e₂) =
    ≤-trans ct₁ ct₂
  , (λ k k< ne ea → trans (k₂ k (<-≤-trans k< ct₁) ne (e₁ k k< ne ea)) (k₁ k k< ne ea))
  , λ k k< ne ea → e₂ k (<-≤-trans k< ct₁) ne (e₁ k k< ne ea)
kept-trans κ pfs fallen _ _ = tt

-- and through a frame, on grounds that join
kept-join : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
            (h₁ h₂ : HeldF f) (q₁ q₂ : Pre κ) → joinPre q₁ q₂ ≡ q₂
          → {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
          → Kept (f ↠[ le ] κ) (headPre h₁ q₁) sched st sched₁ st₁
          → Kept (f ↠[ le ] κ) (headPre h₂ q₂) sched₁ st₁ sched₂ st₂
          → Kept (f ↠[ le ] κ) (headPre h₂ q₂) sched st sched₂ st₂
kept-join f le κ h₁ h₂ (standing pfs) q₂ eq k₁ k₂ =
  kept-trans (f ↠[ le ] κ) (h₁ , pfs) (headPre h₂ q₂) k₁ k₂
kept-join f le κ h₁ h₂ fallen _ refl k₁ k₂ = tt

-- WHAT A FRAME KEPT, READ FROM ANOTHER FRAME OVER THE SAME PATH AND
-- AN EARLIER STATE: the run kept everything off the first frame and
-- the path; the earlier state differs from the run's start only at
-- nodes the second frame names, and every node below the earlier
-- counter that the first frame names, the second names too.  The
-- one shape covers a frame rebased over its own node's write, the
-- inner frame read back as the outer, and a new inner instance read
-- back as the one the finish was made for.
kept-shift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo₁ lo₂ ℓ s s′ u}
             (f : Frame Γ s u) (g : Frame Γ s′ u) (le₁ : lo₁ ≤ ℓ) (le₂ : lo₂ ≤ ℓ)
             (κ : Path Γ ℓ u t) (h₁ : HeldF f) (h₂ : HeldF g) (p : Pre κ)
             {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
           → nodeCt sched ≤ nodeCt sched₁
           → (∀ k → k < nodeCt sched → (T (any (_≡ᵇ k) (frameNodes g)) → ⊥)
                  → T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
           → (∀ k → k < nodeCt sched → (T (any (_≡ᵇ k) (frameNodes g)) → ⊥)
                  → lookupNode k (EvalSt.nodes st₁) ≡ lookupNode k (EvalSt.nodes st))
           → EndsKept (g ↠[ le₂ ] κ) sched st st₁
           → Kept (f ↠[ le₁ ] κ) (headPre h₁ p) sched₁ st₁ sched₂ st₂
           → Kept (g ↠[ le₂ ] κ) (headPre h₂ p) sched st sched₂ st₂
kept-shift f g le₁ le₂ κ h₁ h₂ (standing pfs) ct under off eks (ct₂ , kp , ek) =
    ≤-trans ct ct₂
  , (λ k k< ne ea → trans (kp k (<-≤-trans k< ct)
                             (λ on → [ under k k< (λ b → ne (∨-Tˡ b)) , (λ c → ne (∨-Tʳ c)) ] (∨-T on))
                             (eks k k< ne ea))
                         (off k k< (λ b → ne (∨-Tˡ b))))
  , λ k k< ne ea → ek k (<-≤-trans k< ct)
                      (λ on → [ under k k< (λ b → ne (∨-Tˡ b)) , (λ c → ne (∨-Tʳ c)) ] (∨-T on))
                      (eks k k< ne ea)
kept-shift f g le₁ le₂ κ h₁ h₂ fallen ct under off eks kp = tt

-- the switch's cut touches neither the node table nor the counter
switchKill-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                   (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                 → EvalSt.nodes (proj₂ (switchKill {e = e} cur sched st)) ≡ EvalSt.nodes st
switchKill-nodes nothing  sched st = refl
switchKill-nodes (just _) sched st = refl

switchKill-ct : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
              → nodeCt (proj₁ (switchKill {e = e} cur sched st)) ≡ nodeCt sched
switchKill-ct nothing  sched st = refl
switchKill-ct (just _) sched st = refl

-- the schedule with the node counter advanced past the node it names
bumpNode : ∀ {n} {Γ : Ctx n} → Sched Γ → Sched Γ
bumpNode sched = record sched { mint = setAt nodeᵏ (suc (nodeCt sched)) (Sched.mint sched) }

-- WHAT THE OUTER'S WRAP LEAVES AT ITS NODE, as a function of what was
-- there, and the facts about the wrap the fold spends: its node reads
-- back as that function says, every other node reads back as it did,
-- and the schedule is untouched.
wrapNode : ∀ {n} {Γ : Ctx n} → AllOp → Bool → Maybe (NodeState Γ) → Maybe (NodeState Γ)
wrapNode _         false h                            = h
wrapNode mergeAllᵒ true  (just (mergeAll-st lim act q _)) = just (mergeAll-st lim act q true)
wrapNode switchᵒ   true  (just (switch-st cur _))         = just (switch-st cur true)
wrapNode exhaustᵒ  true  (just (exhaust-st act _))        = just (exhaust-st act true)
wrapNode _         true  h                            = h

record Wrapped {n} {Γ : Ctx n} {t} {e : Closed Γ t} (nid : NodeId) (h′ : Maybe (NodeState Γ))
               (sched′ : Sched Γ) (st′ : EvalSt e) (w : Bool × Sched Γ × EvalSt e) : Set where
  constructor wrapped
  field
    node : lookupNode nid (EvalSt.nodes (proj₂ (proj₂ w))) ≡ h′
    off  : ∀ k → (nid ≡ᵇ k) ≡ false
         → lookupNode k (EvalSt.nodes (proj₂ (proj₂ w))) ≡ lookupNode k (EvalSt.nodes st′)
    sch  : proj₁ (proj₂ w) ≡ sched′

wrap-facts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (op : AllOp) (nid : NodeId) (fin : Bool)
             (sched′ : Sched Γ) (st′ : EvalSt e)
           → Wrapped nid (wrapNode op fin (lookupNode nid (EvalSt.nodes st′))) sched′ st′
                     (thruWrap {e = e} op nid fin (sched′ , st′))
wrap-facts op nid false sched′ st′ = wrapped refl (λ _ _ → refl) refl
wrap-facts mergeAllᵒ nid true sched′ st′ with lookupNode nid (EvalSt.nodes st′) in eq
... | just (mergeAll-st lim act q _) =
      wrapped (lookup-set nid (mergeAll-st lim act q true) (EvalSt.nodes st′))
              (λ k ne → set-above nid k (mergeAll-st lim act q true) (EvalSt.nodes st′) ne) refl
... | just (cell-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (take-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (batchSync-st _ _ _)  = wrapped eq (λ _ _ → refl) refl
... | just (switch-st _ _)       = wrapped eq (λ _ _ → refl) refl
... | just (exhaust-st _ _)      = wrapped eq (λ _ _ → refl) refl
... | nothing                    = wrapped eq (λ _ _ → refl) refl
wrap-facts switchᵒ nid true sched′ st′ with lookupNode nid (EvalSt.nodes st′) in eq
... | just (switch-st cur _) =
      wrapped (lookup-set nid (switch-st cur true) (EvalSt.nodes st′))
              (λ k ne → set-above nid k (switch-st cur true) (EvalSt.nodes st′) ne) refl
... | just (cell-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (take-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (batchSync-st _ _ _)  = wrapped eq (λ _ _ → refl) refl
... | just (mergeAll-st _ _ _ _) = wrapped eq (λ _ _ → refl) refl
... | just (exhaust-st _ _)      = wrapped eq (λ _ _ → refl) refl
... | nothing                    = wrapped eq (λ _ _ → refl) refl
wrap-facts exhaustᵒ nid true sched′ st′ with lookupNode nid (EvalSt.nodes st′) in eq
... | just (exhaust-st act _) =
      wrapped (lookup-set nid (exhaust-st act true) (EvalSt.nodes st′))
              (λ k ne → set-above nid k (exhaust-st act true) (EvalSt.nodes st′) ne) refl
... | just (cell-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (take-st _)           = wrapped eq (λ _ _ → refl) refl
... | just (batchSync-st _ _ _)  = wrapped eq (λ _ _ → refl) refl
... | just (mergeAll-st _ _ _ _) = wrapped eq (λ _ _ → refl) refl
... | just (switch-st _ _)       = wrapped eq (λ _ _ → refl) refl
... | nothing                    = wrapped eq (λ _ _ → refl) refl

-- WHICH STORED SHAPE A CONSUME CAN USE, AS A VIEW ON THE READING: the
-- evaluator's own test, inverted once, so that every consumer of the
-- test dispatches on three shapes instead of on the whole table.
data Usable {n} {Γ : Ctx n} (u : Ty) : AllOp → Maybe (NodeState Γ) → Set where
  u-merge   : ∀ lim act (q : List (Val Γ (obs u))) od
            → Usable u mergeAllᵒ (just (mergeAll-st lim act q od))
  u-switch  : ∀ cur od → Usable u switchᵒ (just (switch-st cur od))
  u-exhaust : ∀ od → Usable u exhaustᵒ (just (exhaust-st false od))

usable : ∀ {n} {Γ : Ctx n} (op : AllOp) (u : Ty) (h : Maybe (NodeState Γ))
       → consumeUsable op u h ≡ true → Usable u op h
usable mergeAllᵒ u (just (mergeAll-st {w} lim act q od)) eq with w ≟ᵗ u | eq
... | yes refl | _  = u-merge lim act q od
... | no _     | ()
usable mergeAllᵒ u nothing                    ()
usable mergeAllᵒ u (just (cell-st _))         ()
usable mergeAllᵒ u (just (take-st _))         ()
usable mergeAllᵒ u (just (batchSync-st _ _ _)) ()
usable mergeAllᵒ u (just (switch-st _ _))     ()
usable mergeAllᵒ u (just (exhaust-st _ _))    ()
usable switchᵒ   u (just (switch-st cur od))  eq = u-switch cur od
usable switchᵒ   u nothing                    ()
usable switchᵒ   u (just (cell-st _))         ()
usable switchᵒ   u (just (take-st _))         ()
usable switchᵒ   u (just (batchSync-st _ _ _)) ()
usable switchᵒ   u (just (mergeAll-st _ _ _ _)) ()
usable switchᵒ   u (just (exhaust-st _ _))    ()
usable exhaustᵒ  u (just (exhaust-st false od)) eq = u-exhaust od
usable exhaustᵒ  u (just (exhaust-st true _)) ()
usable exhaustᵒ  u nothing                    ()
usable exhaustᵒ  u (just (cell-st _))         ()
usable exhaustᵒ  u (just (take-st _))         ()
usable exhaustᵒ  u (just (batchSync-st _ _ _)) ()
usable exhaustᵒ  u (just (mergeAll-st _ _ _ _)) ()
usable exhaustᵒ  u (just (switch-st _ _))     ()

-- and the same for the finish
data Finishing {n} {Γ : Ctx n} (s : Ty) (inst : NodeId) : AllOp → Maybe (NodeState Γ) → Set where
  f-merge   : ∀ lim act (q : List (Val Γ (obs s))) od
            → Finishing s inst mergeAllᵒ (just (mergeAll-st lim act q od))
  f-switch  : ∀ c od → (c ≡ᵇ inst) ≡ true → Finishing s inst switchᵒ (just (switch-st (just c) od))
  f-exhaust : ∀ act od → Finishing s inst exhaustᵒ (just (exhaust-st act od))

finishing : ∀ {n} {Γ : Ctx n} (op : AllOp) (s : Ty) (inst : NodeId) (h : Maybe (NodeState Γ))
          → finishUsable op s inst h ≡ true → Finishing s inst op h
finishing mergeAllᵒ s inst (just (mergeAll-st {w} lim act q od)) eq with w ≟ᵗ s | eq
... | yes refl | _  = f-merge lim act q od
... | no _     | ()
finishing mergeAllᵒ s inst nothing                    ()
finishing mergeAllᵒ s inst (just (cell-st _))         ()
finishing mergeAllᵒ s inst (just (take-st _))         ()
finishing mergeAllᵒ s inst (just (batchSync-st _ _ _)) ()
finishing mergeAllᵒ s inst (just (switch-st _ _))     ()
finishing mergeAllᵒ s inst (just (exhaust-st _ _))    ()
finishing switchᵒ   s inst (just (switch-st (just c) od)) eq = f-switch c od eq
finishing switchᵒ   s inst (just (switch-st nothing _)) ()
finishing switchᵒ   s inst nothing                    ()
finishing switchᵒ   s inst (just (cell-st _))         ()
finishing switchᵒ   s inst (just (take-st _))         ()
finishing switchᵒ   s inst (just (batchSync-st _ _ _)) ()
finishing switchᵒ   s inst (just (mergeAll-st _ _ _ _)) ()
finishing switchᵒ   s inst (just (exhaust-st _ _))    ()
finishing exhaustᵒ  s inst (just (exhaust-st act od)) eq = f-exhaust act od
finishing exhaustᵒ  s inst nothing                    ()
finishing exhaustᵒ  s inst (just (cell-st _))         ()
finishing exhaustᵒ  s inst (just (take-st _))         ()
finishing exhaustᵒ  s inst (just (batchSync-st _ _ _)) ()
finishing exhaustᵒ  s inst (just (mergeAll-st _ _ _ _)) ()
finishing exhaustᵒ  s inst (just (switch-st _ _))     ()

-- the consume that uses nothing, by operator
consumeNil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} (op : AllOp) {nid : NodeId}
             {κ : Path Γ lo u t} {now : Tick} {o : Val Γ (obs u)} {sched : Sched Γ} {st : EvalSt e}
           → consumeUsable op u (lookupNode nid (EvalSt.nodes st)) ≡ false
           → thruConsume⇓ {e = e} op nid κ now o sched st ([] , sched , st)
consumeNil mergeAllᵒ e = consume-all-nil e
consumeNil switchᵒ   e = consume-switch-nil e
consumeNil exhaustᵒ  e = consume-exhaust-nil e

-- a finish at the node the state holds is a reaction to a dead inner
deadBy : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {op : AllOp} {allNid inst : NodeId}
         {κ : Path Γ lo s t} {now : Tick} {vals : List (Val Γ s)} {sched : Sched Γ} {st : EvalSt e}
         {h : Maybe (NodeState Γ)} {r}
       → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
       → lookupNode allNid (EvalSt.nodes st) ≡ h
       → innerFinish⇓ {e = e} op allNid inst κ now vals sched st h r
       → innerReact⇓ {e = e} op allNid inst κ now vals sched st true r
deadBy eqa refl d = react-dead eqa d

-- THE STAGE.  One run of the frame's step, or a piece of one: what
-- it sent to the root and the state it left, with the derivation the
-- caller wants of it; the calls it made above, as a trace whose end
-- never stands where the stage began fallen; and the frame's ground
-- over the trace's end at the state it left, with what the frame kept
-- for the frame beneath.
record Stage {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {S : Set} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
             (D : Stream Γ t → Sched Γ → EvalSt e → Set)
             (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
             (sched : Sched Γ) (st : EvalSt e) : Set₁ where
  constructor stage
  field
    out   : Stream Γ t
    sc    : Sched Γ
    st′   : EvalSt e
    dv    : D out sc st′
    tr    : Trace {e = e} m (Red m u) S κ q rp s₀
    endOk : joinPre q (endPre tr) ≡ endPre tr
    hd    : HeldF f
    hl    : PreHolds m (f ↠[ le ] κ) (headPre hd (endPre tr)) sc st′
    kp    : Kept (f ↠[ le ] κ) (headPre hd (endPre tr)) sched st sc st′

-- a stage that calls nothing and moves nothing
stage-nil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
            {D : Stream Γ t → Sched Γ → EvalSt e → Set}
            (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
            {sched : Sched Γ} {st : EvalSt e}
            (out : Stream Γ t) → D out sched st
          → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h q) sched st
          → Stage m f le κ D q rp s₀ sched st
stage-nil f le κ q rp s₀ out d h hs = stage out _ _ d []ᵗ (join-idem q) h hs (kept-refl _ _)

-- a stage on fallen ground: whatever ran kept the two fields the room
-- reads, so the fall stands
fallenStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
              {D : Stream Γ t → Sched Γ → EvalSt e → Set}
              (rp : RP {e = e} m (Red m u) S κ fallen) (s₀ : S)
              {sched : Sched Γ} {st : EvalSt e}
              (out : Stream Γ t) (sc : Sched Γ) (st′ : EvalSt e) → D out sc st′
            → Keeps {e = e} sched st sc st′ → Fell m sched st → Sound (f ↠[ le ] κ) sc st′ → (h : HeldF f)
            → Stage m f le κ D fallen rp s₀ sched st
fallenStage f le κ rp s₀ out sc st′ d ks fell so h =
  stage out sc st′ d []ᵗ refl h (grounded (fell-keeps ks fell) so) tt

-- the derivation re-read
stage-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
            {D₁ D₂ : Stream Γ t → Sched Γ → EvalSt e → Set}
            {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
            {sched : Sched Γ} {st : EvalSt e}
          → (∀ {o sc s′} → D₁ o sc s′ → D₂ o sc s′)
          → Stage m f le κ D₁ q rp s₀ sched st → Stage m f le κ D₂ q rp s₀ sched st
stage-map g (stage out sc st′ d tr e h hl kp) = stage out sc st′ (g d) tr e h hl kp

-- the stage read from an earlier state that differs only at the
-- frame's own nodes
stage-rebase : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
               {D : Stream Γ t → Sched Γ → EvalSt e → Set}
               {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
               {sched₀ sched : Sched Γ} {st₀ st : EvalSt e}
             → nodeCt sched₀ ≤ nodeCt sched
             → (∀ k → k < nodeCt sched₀ → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
                    → lookupNode k (EvalSt.nodes st) ≡ lookupNode k (EvalSt.nodes st₀))
             → EndsKept (f ↠[ le ] κ) sched₀ st₀ st
             → Stage m f le κ D q rp s₀ sched st → Stage m f le κ D q rp s₀ sched₀ st₀
stage-rebase f le κ ct off eks (stage out sc st′ d tr e h hl kp) =
  stage out sc st′ d tr e h hl (kept-shift f f le le κ h h (endPre tr) ct (λ _ _ ne → ne) off eks kp)

-- ONE STAGE AFTER ANOTHER.  The second begins where the first's trace
-- ended, on the first's ground; the traces append, the ground is the
-- second's, and what was kept composes.
stage-seq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            {f : Frame Γ s u} {le : lo ≤ ℓ} {κ : Path Γ ℓ u t}
            {D₁ D₂ D₃ : Stream Γ t → Sched Γ → EvalSt e → Set}
            {q : Pre κ} {rp : RP {e = e} m (Red m u) S κ q} {s₀ : S}
            {sched : Sched Γ} {st : EvalSt e}
            (a : Stage m f le κ D₁ q rp s₀ sched st)
          → Stage m f le κ D₂ (endPre (Stage.tr a)) (endRP (Stage.tr a)) (endS (Stage.tr a))
                  (Stage.sc a) (Stage.st′ a)
          → (∀ {o sc s′} → D₂ o sc s′ → D₃ (Stage.out a ++ o) sc s′)
          → Stage m f le κ D₃ q rp s₀ sched st
stage-seq {f = f} {le} {κ} {q = q} a b glue =
  let eqE = trans (end-++ (Stage.tr a) (Stage.tr b)) (Stage.endOk b)
  in stage (Stage.out a ++ Stage.out b) (Stage.sc b) (Stage.st′ b) (glue (Stage.dv b))
       (Stage.tr a ++ᵗ Stage.tr b)
       (subst (λ p → joinPre q p ≡ p) (sym eqE) (join-chain q _ _ (Stage.endOk a) (Stage.endOk b)))
       (Stage.hd b)
       (subst (λ p → PreHolds _ (f ↠[ le ] κ) (headPre (Stage.hd b) p) _ _) (sym eqE) (Stage.hl b))
       (subst (λ p → Kept (f ↠[ le ] κ) (headPre (Stage.hd b) p) _ _ _ _) (sym eqE)
              (kept-join f le κ (Stage.hd a) (Stage.hd b) _ _ (Stage.endOk b) (Stage.kp a) (Stage.kp b)))

-- ONE CALL ABOVE THE FRAME, AS A STAGE: on standing ground it is the
-- fold applied once and the frame's ground carried over it; on fallen
-- ground the fold reads the store and the fall stands.
callStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
            (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
            (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
            (now : Tick) (vals : List (Val Γ u)) → Column κ (Red m u) q vals → (fin : Bool)
          → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
          → PreHolds m (f ↠[ le ] κ) (headPre h q) sched st
          → Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now κ vals fin sched st (o , sc , s′)) q rp s₀ sched st
callStage f le κ h (standing pfs) rp s₀ now vals col fin {sched} {st} rm (grounded (hf , ap , hs) so) =
  let c  = call now vals col fin sched st rm (grounded hs (drop-ot f le κ so))
      an = apply rp s₀ c
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) (c ∷ᵗ []ᵗ) refl h
       (headHolds f le κ h hf ap so (Ans.pre′ an) (Ans.holds′ an) (kept an)
          (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
       (headKept f le κ (λ _ _ → refl) refl (λ _ _ _ ea → ea) (Ans.pre′ an) (kept an) h)
callStage f le κ h fallen rp s₀ now vals col fin {sched} {st} rm (grounded fell so) =
  let an = fold rp s₀ now vals col fin sched st rm (grounded fell (drop-ot f le κ so))
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) []ᵗ refl h
       (grounded (fell-keeps (foldPath-keeps (der an)) fell)
          (fold-kept (der an) (drop-ot f le κ so) (f ↠[ le ] κ) so (λ _ _ _ → refl)))
       tt

-- and the frame holds what it held
callStage-hd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
               (q : Pre κ) (rp : RP {e = e} m (Red m u) S κ q) (s₀ : S)
               (now : Tick) (vals : List (Val Γ u)) (col : Column κ (Red m u) q vals) (fin : Bool)
               {sched : Sched Γ} {st : EvalSt e} (rm : Room m sched st)
               (hs : PreHolds m (f ↠[ le ] κ) (headPre h q) sched st)
             → Stage.hd (callStage f le κ h q rp s₀ now vals col fin rm hs) ≡ h
callStage-hd f le κ h (standing pfs) rp s₀ now vals col fin rm hs = refl
callStage-hd f le κ h fallen         rp s₀ now vals col fin rm hs = refl

-- THE FRAME'S OWN WRITE, AS A STAGE: no call, no output, and the
-- frame's ground re-established at what it now holds, given that the
-- node written is one of the frame's own.
writeStage : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {S : Set} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
             (p : Pre κ) (rp : RP {e = e} m (Red m u) S κ p) (s₀ : S)
             (nid : NodeId) (ns : NodeState Γ)
           → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
           → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
           → ConsistentF f h′ (record st { nodes = setNode nid ns (EvalSt.nodes st) })
           → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
           → Stage m f le κ (λ o sc s′ → (o ≡ []) × (sc ≡ sched)
                                       × (s′ ≡ record st { nodes = setNode nid ns (EvalSt.nodes st) }))
                   p rp s₀ sched st
writeStage f le κ p rp s₀ nid ns ownOff h′ {sched} {st} con h hs =
  stage [] sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) (refl , refl , refl) []ᵗ (join-idem p) h′
    (writeHolds f le κ p nid ns ownOff h′ con h hs) (writeKept f le κ p nid ns ownOff h′ h hs)
  where
  writeHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {lo ℓ s u}
               (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (p : Pre κ)
               (nid : NodeId) (ns : NodeState Γ)
             → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
             → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
             → ConsistentF f h′ (record st { nodes = setNode nid ns (EvalSt.nodes st) })
             → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
             → PreHolds m (f ↠[ le ] κ) (headPre h′ p) sched (record st { nodes = setNode nid ns (EvalSt.nodes st) })
  writeHolds f le κ (standing pfs) nid ns ownOff h′ {sched} {st} con h (grounded ((_ , fr) , ap , hs) so) =
    grounded
      ( (con , fr) , ap
      , holdsFs-step κ pfs (λ k on _ → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ap k onF on))) ≤-refl hs )
      (sub-ot (λ r∈ → r∈) ≤-refl so)
  writeHolds f le κ fallen nid ns ownOff h′ con h (grounded fell so) = grounded fell (sub-ot (λ r∈ → r∈) ≤-refl so)
  writeKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (p : Pre κ)
              (nid : NodeId) (ns : NodeState Γ)
            → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
            → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
            → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
            → Kept (f ↠[ le ] κ) (headPre h′ p) sched st sched (record st { nodes = setNode nid ns (EvalSt.nodes st) })
  writeKept f le κ (standing pfs) nid ns ownOff h′ {sched} {st} h (grounded (_ , ap , _) _) =
    ≤-refl , (λ k _ ne _ → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ne (∨-Tˡ onF)))) , λ _ _ _ ea → ea
  writeKept f le κ fallen nid ns ownOff h′ h fell = tt

-- WHAT A SUBSCRIBING FRAME'S STEP IS: given the frame's ground over a
-- standing path, a call, and a state under the ceiling, a stage whose
-- derivation is the fold of the frame's own path at that call.
--
-- AND A GUARD ON THE COLUMN, WHICH THE STEP IS HANDED AND HANDS BACK.
-- On standing ground the store agrees with the column, so a fact about
-- the column that every step of the frame re-establishes is a fact
-- about the store at every call -- carried by the continuation, with
-- nothing global to thread.
SubStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u) → (HeldF f → Set) → ℕ → Set₁
SubStep {Γ = Γ} {t} {e} {s} {u} f G m =
  ∀ {S : Set} {lo ℓ} (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
    (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : HeldF f) → G h
  → (now : Tick) (vals : List (Val Γ s)) → All (Red m s) vals → (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Room m sched st
  → PreHolds m (f ↠[ le ] κ) (standing (h , pfs)) sched st
  → Σ (Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now (f ↠[ le ] κ) vals fin sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
      (λ r → G (Stage.hd r))

------------------------------------------------------------------
-- THE RAW FOLD.
------------------------------------------------------------------

cut-sub : ∀ {n} {Γ : Ctx n} {t} (v : NodeId) (reg : List (RegRow Γ t)) (r : RegRow Γ t)
        → r ∈ proj₁ (cutThrough v reg) → r ∈ reg
cut-sub v [] r ()
cut-sub v ((rid , rs , c) ∷ reg) r r∈ with pathHasNode v (proj₂ c) | cutThrough v reg | cut-sub v reg
... | true  | kept , rids | ih = there (ih r r∈)
... | false | kept , rids | ih with r∈
...   | here eq   = here eq
...   | there r∈′ = there (ih r r∈′)

kill-sub : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
         → ∀ {r} → r ∈ EvalSt.registry (proj₂ (switchKill cur sched st)) → r ∈ EvalSt.registry st
kill-sub nothing  sched st r∈ = r∈
kill-sub (just v) sched st r∈ = cut-sub v (EvalSt.registry st) _ r∈

-- the outer's wrap writes one node and no row
wrap-ot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s} {κ : Path Γ lo s t}
          (op : AllOp) (nid : NodeId) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
        → Sound κ sched st
        → Sound κ (proj₁ (proj₂ (thruWrap op nid fin (sched , st)))) (proj₂ (proj₂ (thruWrap op nid fin (sched , st))))
wrap-ot op nid false sched st so = so
wrap-ot mergeAllᵒ nid true sched st so with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st _ _ _ _)  = sub-ot (λ r∈ → r∈) ≤-refl so
... | just (cell-st _)            = so
... | just (take-st _)            = so
... | just (batchSync-st _ _ _)   = so
... | just (switch-st _ _)        = so
... | just (exhaust-st _ _)       = so
... | nothing                     = so
wrap-ot switchᵒ nid true sched st so with lookupNode nid (EvalSt.nodes st)
... | just (switch-st _ _)        = sub-ot (λ r∈ → r∈) ≤-refl so
... | just (cell-st _)            = so
... | just (take-st _)            = so
... | just (batchSync-st _ _ _)   = so
... | just (mergeAll-st _ _ _ _)  = so
... | just (exhaust-st _ _)       = so
... | nothing                     = so
wrap-ot exhaustᵒ nid true sched st so with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st _ _)       = sub-ot (λ r∈ → r∈) ≤-refl so
... | just (cell-st _)            = so
... | just (take-st _)            = so
... | just (batchSync-st _ _ _)   = so
... | just (mergeAll-st _ _ _ _)  = so
... | just (switch-st _ _)        = so
... | nothing                     = so

wrap-reg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (op : AllOp) (nid : NodeId) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
         → ∀ {r} → r ∈ EvalSt.registry (proj₂ (proj₂ (thruWrap op nid fin (sched , st)))) → r ∈ EvalSt.registry st
wrap-reg op nid false sched st r∈ = r∈
wrap-reg mergeAllᵒ nid true sched st r∈ with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st _ _ _ _)  = r∈
... | just (cell-st _)            = r∈
... | just (take-st _)            = r∈
... | just (batchSync-st _ _ _)   = r∈
... | just (switch-st _ _)        = r∈
... | just (exhaust-st _ _)       = r∈
... | nothing                     = r∈
wrap-reg switchᵒ nid true sched st r∈ with lookupNode nid (EvalSt.nodes st)
... | just (switch-st _ _)        = r∈
... | just (cell-st _)            = r∈
... | just (take-st _)            = r∈
... | just (batchSync-st _ _ _)   = r∈
... | just (mergeAll-st _ _ _ _)  = r∈
... | just (exhaust-st _ _)       = r∈
... | nothing                     = r∈
wrap-reg exhaustᵒ nid true sched st r∈ with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st _ _)       = r∈
... | just (cell-st _)            = r∈
... | just (take-st _)            = r∈
... | just (batchSync-st _ _ _)   = r∈
... | just (mergeAll-st _ _ _ _)  = r∈
... | just (switch-st _ _)        = r∈
... | nothing                     = r∈

dying-rule : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
           → Rule sched st → Rule sched (shareDying i fin st)
dying-rule i false sched st ru = ru
dying-rule i true  sched st ru = sub-rule (λ r∈ → r∈) ≤-refl ru

-- an admitted path is the path of a row the registry holds
admit-row : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) (reg : List (RegRow Γ t))
              {x : RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t}
          → x ∈ shareAdmit i reg
          → Σ (RegRow Γ t) (λ r₀ → r₀ ∈ reg × (∀ k → rowThrough k r₀ ≡ pathHasNode k (proj₂ x))
                                  × rowEnd r₀ ≡ endOf (proj₂ x))
admit-row i [] ()
admit-row i ((rid , atDyn _ _ , _) ∷ reg) x∈ =
  let (r₀ , m , ek , ee) = admit-row i reg x∈ in r₀ , there m , ek , ee
admit-row {Γ = Γ} i ((rid , atSlot j , (u , p)) ∷ reg) x∈ with i ≟ᶠ j | u ≟ᵗ lookup Γ i
... | no _     | _        = let (r₀ , m , ek , ee) = admit-row i reg x∈ in r₀ , there m , ek , ee
... | yes _    | no _     = let (r₀ , m , ek , ee) = admit-row i reg x∈ in r₀ , there m , ek , ee
... | yes refl | yes refl with x∈
...   | here refl = _ , here refl , (λ k → refl) , refl
...   | there x∈′ = let (r₀ , m , ek , ee) = admit-row i reg x∈′ in r₀ , there m , ek , ee

-- and its path is distinct if every row's is
admit-distinct : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) (reg : List (RegRow Γ t))
                   {x : RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t}
               → (∀ {r} → r ∈ reg → rowDistinct r) → x ∈ shareAdmit i reg → Distinct (proj₂ x)
admit-distinct i [] dr ()
admit-distinct i ((rid , atDyn _ _ , _) ∷ reg) dr x∈ = admit-distinct i reg (λ m → dr (there m)) x∈
admit-distinct {Γ = Γ} i ((rid , atSlot j , (u , p)) ∷ reg) dr x∈ with i ≟ᶠ j | u ≟ᵗ lookup Γ i
... | no _     | _        = admit-distinct i reg (λ m → dr (there m)) x∈
... | yes _    | no _     = admit-distinct i reg (λ m → dr (there m)) x∈
... | yes refl | yes refl with x∈
...   | here refl = dr (here refl)
...   | there x∈′ = admit-distinct i reg (λ m → dr (there m)) x∈′

admit-ot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (i : Fin n) (sched : Sched Γ) (st : EvalSt e) → Rule sched st
         → ∀ {a} → a ∈ shareAdmit i (EvalSt.registry st) → Sound (proj₂ a) sched st
admit-ot i sched st ru a∈ =
  let (r₀ , m , ek , ee) = admit-row i (EvalSt.registry st) a∈
  in sound ru (λ k h r∈ th → trans (termini ru k r∈ m th (subst T (sym (ek k)) h)) ee)
              (λ k h → fresh-rows ru m k (subst T (sym (ek k)) h))
              (admit-distinct i (EvalSt.registry st) (distinct-rows ru) a∈)

admit-agree : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (i : Fin n) (st : EvalSt e) → Termini st
            → ∀ {a b} → a ∈ shareAdmit i (EvalSt.registry st) → b ∈ shareAdmit i (EvalSt.registry st)
            → Agree (proj₂ a) (proj₂ b)
admit-agree i st tm a∈ b∈ k ha hb =
  let (r₀ , m₀ , ka , ea) = admit-row i (EvalSt.registry st) a∈
      (r₁ , m₁ , kb , eb) = admit-row i (EvalSt.registry st) b∈
  in trans (sym ea) (trans (tm k m₀ m₁ (subst T (sym (ka k)) ha) (subst T (sym (kb k)) hb)) eb)

-- a node found in a two-node frame is one of the two
node-cases : ∀ {x y k : ℕ} {A : Set} → T (any (_≡ᵇ k) (x ∷ y ∷ [])) → (x ≡ k → A) → (y ≡ k → A) → A
node-cases {x} {y} {k} p l r with x ≡ᵇ k in eq
... | true  = l (≡ᵇ→≡ x k eq)
... | false with y ≡ᵇ k in eq′
...   | true  = r (≡ᵇ→≡ y k eq′)
...   | false = ⊥-elim p

-- AN INNER'S EXIT FRAME, PUSHED AT THE COUNTER, STANDS ON THE RULE: its
-- flattener's node ends where the path below does, and its instance is
-- the counter itself, which no row runs through yet.
fresh-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (op : AllOp) (nid : NodeId)
                (κ : Path Γ lo u t) (sched : Sched Γ) {st : EvalSt e}
            → Sound κ sched st → NodeOn nid κ sched st
            → Sound (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) (bumpNode sched) st
fresh-inner op nid κ sched {st} (sound ru ea fp ds) (node-on at lt op′) =
  sound (sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sched)) ru)
    (λ k h → [ (λ fn → node-cases {x = nid} {y = nodeCt sched} fn
                         (λ eq → subst (λ j → EndsAt j (endOf κ) st) eq at)
                         (λ eq r∈ th → ⊥-elim (<-irrefl refl
                                         (subst (_< nodeCt sched) (sym eq) (fresh-rows ru r∈ k th)))))
             , (λ on → ea k on) ] (∨-T h))
    (λ k h → [ (λ fn → nodes-below (nid ∷ nodeCt sched ∷ [])
                          (<-≤-trans lt (n≤1+n _) ∷ᵃ ≤-refl ∷ᵃ []ᵃ) k fn)
             , (λ on → <-≤-trans (fp k on) (n≤1+n _)) ] (∨-T h))
    ( (λ k fn onκ → node-cases {x = nid} {y = nodeCt sched} fn
                      (λ eq → op′ (subst (λ j → T (pathHasNode j κ)) (sym eq) onκ))
                      (λ eq → <-irrefl (sym eq) (fp k onκ)))
    , ds )

-- an inner's exit frame's rule is the rule on the path below it and on
-- its flattener's node
inner-back : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} (op : AllOp) (nid inst : NodeId)
               (κ : Path Γ lo u t) {sched : Sched Γ} {st : EvalSt e}
           → Sound (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ) sched st
           → Sound κ sched st × NodeOn nid κ sched st
inner-back {u = u} op nid inst κ so =
    drop-ot (from-inner {s = u} op nid inst) ≤-refl κ so
  , head-on (from-inner {s = u} op nid inst) ≤-refl κ nid (self-node nid (inst ∷ [])) so

-- so an inner subscribed raw leaves the rule standing on both
inner-after : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} (op : AllOp) (nid : NodeId)
                (κ : Path Γ lo u t) {now} {o : Val Γ (obs u)} (sched : Sched Γ) {st : EvalSt e} {r}
            → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st r
            → Sound κ sched st → NodeOn nid κ sched st
            → Sound κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) × NodeOn nid κ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
inner-after {u = u} op nid κ sched {st} d so nd =
  let so₀ = fresh-inner op nid κ sched {st} so nd
  in inner-back op nid (nodeCt sched) κ (subscribe-kept d so₀ _ so₀ (λ _ _ _ → refl))

-- WHAT A FRAME'S NODE HOLDS IN THE STORE, read as its column: the
-- ground a path the store holds stands on, when nothing closed over
-- candidates for it.
colOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u) → EvalSt e → HeldF f
colOf (map-f _)            st = tt
colOf (scan-f _ nid)       st = lookupNode nid (EvalSt.nodes st)
colOf (take-f nid)         st = lookupNode nid (EvalSt.nodes st)
colOf (batchSync-f nid)    st = lookupNode nid (EvalSt.nodes st)
colOf (from-inner _ nid _) st = lookupNode nid (EvalSt.nodes st)
colOf (thru-outer _ nid)   st = lookupNode nid (EvalSt.nodes st)

colsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (κ : Path Γ lo u t) → EvalSt e → PreFs κ
colsOf root             st = tt
colsOf (share-sink _ _) st = tt
colsOf (f ↠[ _ ] κ)     st = colOf f st , colsOf κ st

consistentOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (f : Frame Γ s u) (st : EvalSt e)
             → ConsistentF f (colOf f st) st
consistentOf (map-f _)            st = tt
consistentOf (scan-f _ _)         st = refl
consistentOf (take-f _)           st = refl
consistentOf (batchSync-f _)      st = refl
consistentOf (from-inner _ _ _)   st = refl
consistentOf (thru-outer _ _)     st = refl

-- every node found among some is below a bound, so all of them are
all-below : ∀ (ns : List ℕ) {ct} → (∀ k → T (any (_≡ᵇ k) ns) → k < ct) → All (_< ct) ns
all-below []       b = []ᵃ
all-below (j ∷ ns) b = b j (self-node j ns) ∷ᵃ all-below ns (λ k on → b k (∨-Tʳ on))

-- SO A PATH THE RULE HOLDS OF STANDS ON THE STORE'S OWN COLUMNS: each
-- frame agrees with what it reads, its nodes are below the counter by
-- `fresh-path`, and it is apart from the path below by `distinct`.
holdsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (κ : Path Γ lo u t) {sched : Sched Γ} {st : EvalSt e}
        → FreshPath κ sched → Distinct κ → HoldsFs κ (colsOf κ st) sched st
holdsOf root             fp ds = tt
holdsOf (share-sink _ _) fp ds = tt
holdsOf (f ↠[ _ ] κ) {st = st} fp (ap , ds) =
    (consistentOf f st , all-below (frameNodes f) (λ k on → fp k (∨-Tˡ on)))
  , ap
  , holdsOf κ (λ k on → fp k (∨-Tʳ on)) ds

-- how many inners a merge's node holds back, and none at any other node
waiting : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → ℕ
waiting (just (mergeAll-st _ _ q _)) = length q
waiting _                            = 0

-- the drain reads back no more than the node holds
drain-waiting : ∀ {n} {Γ : Ctx n} (s : Ty) (h : Maybe (NodeState Γ))
              → length (proj₁ (proj₂ (proj₂ (drainSt s h)))) ≤ waiting h
drain-waiting s (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | no  _    = z≤n
... | yes refl = ≤-refl
drain-waiting s nothing                     = z≤n
drain-waiting s (just (cell-st _))          = z≤n
drain-waiting s (just (take-st _))          = z≤n
drain-waiting s (just (switch-st _ _))      = z≤n
drain-waiting s (just (exhaust-st _ _))     = z≤n
drain-waiting s (just (batchSync-st _ _ _)) = z≤n

-- A RUN SPENT ROOM: something it subscribed connected.
Spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Spends sched st sched′ st′ =
  unconn (Sched.slots sched′) (EvalSt.connectedShares st′) < unconn (Sched.slots sched) (EvalSt.connectedShares st)

-- A RAW FOLD THAT CONNECTS NOTHING KEEPS THE TERMINUS.  Past the path's
-- sink the fold fans out, and the fan-out writes the nodes of the rows
-- it folds; a row on slot `j` sits at floor `suc j` and ends above it or
-- at the root, and so does every row that fan-out reaches in turn, so a
-- node whose rows all end at `j`'s sink is on none of them.  Every other
-- write is to a frame's own node on the path or to one the counter hands
-- out.  Read off the relation's arms and the row types, not
-- machine-checked.

-- Measured on the side branch's evaluator over 142k programs of the 1.5M
-- corpus: at 157k frame steps whose continuation fanned out and 5.9k
-- that connected, the fold below left the frame's own nodes unchanged in
-- shape and value.  That reads the nodes of frames stacked on a path,
-- not every node the terminus guards, and reachable states only.
--
-- PROBED: `Probed.Base-Leaves` -- down a share's sink fanning out to a
--   reader, and through a one-lane merge handed a fresh inner, both in
--   the share's def and at the root, from stores the builder reached.
--   Not a switch cutting a sibling, nor the unsupported formers.
postulate
  raw-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t}
               {now vals fin sched st out sched′ st′}
           → foldPath⇓ {e = e} now κ vals fin sched st (out , sched′ , st′) → Sound κ sched st
           → (Spends sched st sched′ st′ → ⊥)
           → ∀ {pfs} → Kept κ (standing pfs) sched st sched′ st′

-- A MERGE'S QUEUE REFILLS WHILE ONE OF ITS INNERS RUNS ONLY BY SPENDING
-- ROOM.  A fold reaches the flattener's outer frame along a path through
-- its node, and there are three such paths.  The inner's own is excluded
-- by `off-path`.  A row folded by the fan-out of the sink the inner's
-- path ends at, `just j`, is excluded as well: `at-end` puts every row
-- through the node at `just j`, while a row on slot `j` sits at floor
-- `suc j` and ends above it or at the root, and so does every row that
-- fan-out reaches in turn.  That leaves a row folded inside a connect's
-- definition.  A share that already finished completes its new
-- subscriber and runs nothing (`slot-spent`).  Read off the relation's
-- arms and the path and row types, not machine-checked.

-- Measured on the sweep-era evaluator over 1.5M programs: 44,160 raw
-- finishes met a nonempty queue, and every one of the 324,536 budgeted
-- finishes met a queue exactly at its budget; none overran it, and no
-- walk-order finish met a queue.
-- The budgeted-drain prototype on the oracle's side branch agrees over
-- 48k programs: 42k raw finishes met a nonempty queue, 129k budgeted
-- finishes met one exactly at budget, and the overrun, unfunded and
-- walk-order tags never fired.  Reachable states only; the statement
-- quantifies over every state its hypotheses admit.
--
-- PROBED: `Probed.Base-Leaves` -- a fresh inner of a one-lane merge in a
--   share's def, whose values fan out past the sink, and one at the root.
--   Neither re-enters the merge's outer, so the refill itself is not
--   covered.
postulate
  refill-spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u ℓ} (op : AllOp) (nid : NodeId)
                    (κ : Path Γ ℓ u t) {o : Val Γ (obs u)} {now} {sched : Sched Γ} {st : EvalSt e} {r}
                → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now (bumpNode sched) st r
                → Sound κ sched st → NodeOn nid κ sched st
                → ∀ {h} → lookupNode nid (EvalSt.nodes st) ≡ h
                → (Spends sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) → ⊥)
                → waiting (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))) ≤ waiting h

-- THE INNER'S BASE: ITS EXIT FRAME OVER THE REST OF THE PATH, FOLDED
-- RAW.  It is the one continuation an inner subscribed from the raw
-- fold is handed, so the frames the inner stacks step live above it and
-- no arm's extension re-enters the raw fold.  It holds no candidates,
-- so its column is what the store holds, and its successor stands there
-- again -- or on `fallen`, where the fold connected.

-- IT IS BUDGETED BY THE QUEUE ITS OWN COLUMN PINS.  It is the only place
-- a merge's queue is nonempty at an inner's finish: on standing ground
-- the column guards keep it empty, but a share's fan-out reaches the
-- outer while the lane is busy, and a raw finish meets what it queued.
-- Standing ground makes the store read back the column at every fold, so
-- the finish drains exactly the queue the base was built over; each
-- drained inner's base is built over the queue with that inner popped,
-- and a drain reading its queue back longer than it left it has spent
-- room and peels it.  The accessibility is the column's, so no fold
-- transports it.

-- DEAD ROUTE: the base folded raw at the same room, unbudgeted.  The
--   base reaches the drain's inner as an argument to its candidate, and
--   a call there is not guarded by the `fold` copattern: nothing on the
--   cycle through `rawInner` is smaller.
baseRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
         (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
       → (op : AllOp) (nid inst : NodeId) (κ : Path Γ ℓ u t)
         (pfs : PreFs (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ)) → Acc _<_ (waiting (proj₁ pfs))
       → RP {e = e} m (Red m u) ⊤ (from-inner op nid inst ↠[ ≤-refl ] κ) (standing pfs)

-- what one fold of the base answers: fallen where it connected, and the
-- base again, over the store's columns, where it did not
baseAns : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
          (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
        → (op : AllOp) (nid inst : NodeId) (κ : Path Γ ℓ u t) {now : Tick} {vals : List (Val Γ u)} {fin : Bool}
          (sched : Sched Γ) (st : EvalSt e) → Room m sched st
        → Sound (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ) sched st
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
-- else the base folds the path below it, which is shorter.  Under the
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
         → (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h → Acc _<_ (waiting h)
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
         → Sound κ sched st → NodeOn nid κ sched st → Acc _<_ (length q)
         → Σ (Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e)
             (λ r → mergeAllDrain⇓ {e = e} nid κ now fuel lim act od q sched st r
                  × Sound κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  × NodeOn nid κ (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))))
rawDrain ac le aM nid κ now [] lim act od q sched st rm so nd aq = _ , drain-spent , so , nd
rawDrain ac le aM nid κ now (_ ∷ fs) lim act od [] sched st rm so nd aq = _ , drain-nil , so , nd
rawDrain {s = s} ac le (acc rsM) nid κ now (_ ∷ fs) lim act od (o ∷ q) sched st rm so nd (acc rs)
  with hasRoom lim act in eqr
... | false = _ , drain-no-room eqr , so , nd
... | true
  with rawInner ac le (acc rsM) mergeAllᵒ nid κ now o sched
         (record st { nodes = setNode nid (mergeAll-st {t = s} lim (suc act) q od) (EvalSt.nodes st) })
         rm (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
         (just (mergeAll-st {t = s} lim (suc act) q od)) (lookup-set nid _ (EvalSt.nodes st)) (rs ≤-refl)
...   | (r₁ , d₁)
  with unconn (Sched.slots (proj₁ (proj₂ r₁))) (EvalSt.connectedShares (proj₂ (proj₂ r₁)))
         <? unconn (Sched.slots sched) (EvalSt.connectedShares st)
...     | yes sp =
  let (so₁ , nd₁) = inner-after mergeAllᵒ nid κ sched d₁ (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
      ds = drainSt s (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁))))
      (r₂ , d₂ , so₂ , nd₂) = rawDrain ac le (rsM (<-≤-trans sp rm)) nid κ now fs (proj₁ ds) (proj₁ (proj₂ ds))
                                (proj₂ (proj₂ (proj₂ ds))) (proj₁ (proj₂ (proj₂ ds)))
                                (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) ≤-refl so₁ nd₁ (<-wellFounded _)
  in _ , drain-room eqr (inner refl d₁) refl d₂ , so₂ , nd₂
...     | no nsp
  with waiting (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁)))) ≤? length q
...       | no nw = ⊥-elim (nw (refill-spends mergeAllᵒ nid κ d₁ (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                                (lookup-set nid _ (EvalSt.nodes st)) nsp))
...       | yes w =
  let (so₁ , nd₁) = inner-after mergeAllᵒ nid κ sched d₁ (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
      ds = drainSt s (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁))))
      bd = ≤-trans (drain-waiting s (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₁))))) w
      (r₂ , d₂ , so₂ , nd₂) = rawDrain ac le (acc rsM) nid κ now fs (proj₁ ds) (proj₁ (proj₂ ds))
                                (proj₂ (proj₂ (proj₂ ds))) (proj₁ (proj₂ (proj₂ ds)))
                                (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁)) (room-keeps (subscribeE-keeps d₁) rm) so₁ nd₁
                                (rs (s≤s bd))
  in _ , drain-room eqr (inner refl d₁) refl d₂ , so₂ , nd₂

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
                          _ (lookup-set nid _ (EvalSt.nodes (proj₂ sk))) (<-wellFounded _)
          in _ , consume-switch-sub c refl refl (inner refl d) , inner-after switchᵒ nid κ (proj₁ sk) d so′ nd′
...     | u-exhaust od =
          let (r , d) = rawInner ac le aM exhaustᵒ nid κ now o sched
                          (record st { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) }) rm
                          (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                          _ (lookup-set nid _ (EvalSt.nodes st)) (<-wellFounded _)
          in _ , consume-exhaust-sub c (inner refl d)
               , inner-after exhaustᵒ nid κ sched d (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
...     | u-merge lim act q od with hasRoom lim act in eqr
...       | false = _ , consume-all-enqueue c eqr , sub-ot (λ r∈ → r∈) ≤-refl so , sub-on (λ r∈ → r∈) ≤-refl nd
...       | true  =
          let (r , d) = rawInner ac le aM mergeAllᵒ nid κ now o sched
                          (record st { nodes = setNode nid (mergeAll-st lim (suc act) q od) (EvalSt.nodes st) }) rm
                          (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)
                          _ (lookup-set nid _ (EvalSt.nodes st)) (<-wellFounded _)
          in _ , consume-all-sub c eqr (inner refl d)
               , inner-after mergeAllᵒ nid κ sched d (sub-ot (λ r∈ → r∈) ≤-refl so) (sub-on (λ r∈ → r∈) ≤-refl nd)

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
         → (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h → Acc _<_ (waiting h)
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
          → (h : Maybe (NodeState Γ)) → Acc _<_ (waiting h)
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
                         _ refl (<-wellFounded _)
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

rawReact ac le aM op nid inst le′ κ now vals false sched st rm so h eq aq =
  _ , step-from-inner react-false , drop-ot (from-inner op nid inst) le′ κ so
rawReact ac le aM op nid inst le′ κ now vals true sched st rm so h eq aq
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = _ , step-from-inner (react-alive eqa) , drop-ot (from-inner op nid inst) le′ κ so
... | false =
  let (r , fd , so′) = rawFinish ac le aM op nid inst le′ κ now vals sched st rm so h aq
  in r , step-from-inner (react-dead eqa (subst (λ x → innerFinish⇓ op nid inst κ now vals sched st x r) (sym eq) fd)) , so′

rawFinish {s = s} ac le aM op nid inst le′ κ now vals sched st rm so h aq
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
                                      (drop-ot fi le′ κ so₁) (head-on fi le′ κ nid (self-node nid (inst ∷ [])) so₁) aq
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
rawGo i ac aM now vals fin ((rid , p) ∷ ps) sched st rm ru ok ag
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  =
  let (r , g , ru′) = rawGo i ac aM now vals fin ps sched st rm ru (λ a∈ → ok (there a∈))
                        (λ a∈ b∈ → ag (there a∈) (there b∈))
  in r , go-cut eqc g , ru′
... | false =
  let so = sub-ot (λ r∈ → r∈) ≤-refl (ok (here refl))
      (r₁ , d) = rawFold ac ≤-refl aM p now vals fin sched
                   (record st { delivered = rid ∷ EvalSt.delivered st }) rm so
      (r₂ , g , ru₂) = rawGo i ac aM now vals fin ps (proj₁ (proj₂ r₁)) (proj₂ (proj₂ r₁))
                         (room-keeps (foldPath-keeps d) rm)
                         (ruled (fold-kept d so p so (λ _ _ _ → refl)))
                         (λ {a} a∈ → fold-kept d so (proj₂ a) (sub-ot (λ r∈ → r∈) ≤-refl (ok (there a∈)))
                                       (ag (here refl) (there a∈)))
                         (λ a∈ b∈ → ag (there a∈) (there b∈))
  in _ , go-live eqc d g , ru₂

------------------------------------------------------------------
-- THE ARMS, STATED.
------------------------------------------------------------------

-- THE STATEMENT EVERY ARM MAKES: the candidate for one closure over a
-- reducible environment, funded by three accessibilities.  The room's
-- is outermost and only a share's connect peels it; under it the input
-- bound and the term size fall at every former.  Every member of the
-- candidate's cycle carries all three, so the checker reads the whole
-- order off the call sites.
Arm : ∀ {n} {Γ : Ctx n} {Θ t} → Exp Γ [] [] Θ t → Set₁
Arm {Γ = Γ} {Θ = Θ} {t = t} b =
  ∀ (ρ : Env Γ Θ) {m} → RedEnv m ρ
  → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
  → Acc _<_ (gsizeᵉ b) → Acc _<_ m → Red {Γ = Γ} m (obs t) (Θ , b , ρ)

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

-- A VALUE OF A DATA TYPE IS A CANDIDATE AT EVERY CEILING, AND ASKS
-- NOTHING OF IT: no observable sits anywhere inside it, so nothing is
-- subscribed and no accessibility is spent.
red-data : ∀ {n} {Γ : Ctx n} {m} (t : Ty) → T (isData t) → (v : Val Γ t) → Red m t v
red-data unitᵗ     _  _        = tt
red-data boolᵗ     _  _        = tt
red-data natᵗ      _  _        = tt
red-data uniqᵗ     _  _        = tt
red-data (s ×ᵗ u)  ok (a , b)  with isData s in es
... | true  = red-data s (subst T (sym es) tt₀) a , red-data u ok b
... | false = ⊥-elim ok
red-data (s +ᵗ u)  ok (inj₁ a) with isData s in es
... | true  = red-data s (subst T (sym es) tt₀) a
... | false = ⊥-elim ok
red-data (s +ᵗ u)  ok (inj₂ b) with isData s in es
... | true  = red-data u ok b
... | false = ⊥-elim ok
red-data (listᵗ u) ok []       = []ᵃ
red-data (listᵗ u) ok (x ∷ xs) = red-data u ok x ∷ᵃ red-data (listᵗ u) ok xs
red-data (obs _)   ()

-- what a run kept after a step that wrote nothing below the counter,
-- it kept from before the step
kept-before : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
              (κ : Path Γ lo u t) {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
            → PreservedBelow (nodeCt sched) st st₁ → nodeCt sched ≤ nodeCt sched₁ → EndsKept κ sched st st₁
            → (p : Pre κ) → Kept κ p sched₁ st₁ sched₂ st₂ → Kept κ p sched st sched₂ st₂
kept-before κ {sched} {sched₁} {sched₂} {st} {st₁} {st₂} pr ct ek (standing q) kp =
  kept-trans κ q (standing q) {sched} {sched₁} {sched₂} {st} {st₁} {st₂}
    (kept-step κ (standing q) {sched} {sched₁} {st} {st₁} pr ct ek) kp
kept-before κ pr ct ek fallen       kp = tt

-- THE SCRIPTED SLOT.  Folds what the slot script says through the
-- continuation with a data candidate beside every value; the live hot
-- slot registers and folds nothing; the cold slot with a tail registers
-- FIRST and then folds its prefix, since a synchronous value can cut
-- this very chain and a cut severs registrations.
red-scripted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ S}
    (i : Fin n) (ρ : Env Γ Θ) (k : ℕ) → T (toℕ i <ᵇ k) → Acc _<_ k
  → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo) (pre : Pre κ)
  → ∀ {m} (rp : RP {e = e} m (Red m (lookup Γ i)) S κ pre) (s : S)
  → (now : Tick) (sched : Sched Γ)
  → (sc : ObservableInput (Val Γ (lookup Γ i))) {oks : T (isData (lookup Γ i))}
  → Sched.slots sched i ≡ scripted {ok = oks} sc
  → ∀ (st : EvalSt e) → Acc _<_ m → Room m sched st → PreHolds m κ pre sched st
  → Σ (Stream Γ t × Sched Γ × EvalSt e)
      (λ r → subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r
           × Σ (Trace {e = e} m (Red m (lookup Γ i)) S κ pre rp s)
               (λ tr → PreHolds m κ (endPre tr) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                     × Kept κ (endPre tr) sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))
red-scripted i ρ k ok aK κ below pre rp s now sched (hot async) slEq st aM rm h
  with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
... | true =
      let c  = call now [] (ofColumn κ pre []ᵃ) true sched st rm h
          an = apply rp s c
      in _ , subs-hot-done below slEq doneEq (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
... | false =
      _ , subs-hot-live below slEq doneEq refl , []ᵗ
    , holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x)
        (register-sound {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
           ≤-refl (lower-end below κ) (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on))
           (λ so′ → lower-distinct below κ (distinct so′)))
        h
    , kept-step κ pre (pres (λ _ _ → refl)) ≤-refl
        (ends-register {κ = κ} {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
           (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on)))
red-scripted i ρ k ok aK κ below pre rp s now sched (cold sync []) {oks} slEq st aM rm h =
  let c  = call now sync (ofColumn κ pre (red-data (listᵗ _) oks sync)) true sched st rm h
      an = apply rp s c
  in _ , subs-cold-sync below slEq (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
red-scripted {Γ = Γ} {lo = lo} i ρ k ok aK κ below pre rp s now sched (cold sync (d ∷ ds)) {oks} slEq st aM rm h =
  let src    = freshId sourceᵏ (Sched.mint sched)
      ord    = freshId ordinalᵏ (Sched.mint sched)
      rid    = freshId regᵏ (Sched.mint sched)
      sched₁ = record sched
                 { mint = setAt regᵏ (suc rid) (setAt sourceᵏ (suc src) (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                 ; live = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                                 ; pending = resolve now (d ∷ ds) }
                          ∷ Sched.live sched }
      st₁    = register rid (atDyn src lo) κ st
      h₁     = holds-step κ pre {sched′ = sched₁} {st′ = st₁} (λ _ _ _ → refl) ≤-refl (λ x → x)
                 (register-sound {sched = sched} {sched′ = sched₁} {st = st} rid (atDyn src lo) κ ≤-refl refl (λ k′ on → inj₁ on) (λ so′ → distinct so′))
                 h
      c      = call now sync (ofColumn κ pre (red-data (listᵗ _) oks sync)) false sched₁ st₁ rm h₁
      an     = apply rp s c
  in _ , subs-cold-async below slEq refl refl refl (der an) , c ∷ᵗ []ᵗ , Ans.holds′ an
   , kept-before κ (pres (λ _ _ → refl)) ≤-refl
       (ends-register {κ = κ} {sched = sched} {st = st} rid (atDyn src lo) κ (λ k′ on → inj₁ on)) (Ans.pre′ an) (kept an)

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
redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h
  with redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
         (rs (subst (_< suc (gsizeᵉ body))
                    (sym (gsize-unfoldμ body)) ≤-refl)) aM
         κ pre rp s₀ now sched st rm h
... | (r , d , rest) = r , subs-μ d , rest
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

red-map {s = s} f b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK
         (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
         (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) (standing (tt , pfs))
         (liveRP ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp)
         s₀ now sched st rm (grounded ((tt , []ᵃ) , (λ _ ()) , ground h) (push-sound (map-f (_ , f , ρ)) ≤-refl κ (sounds h) (λ k ())))
... | (r , d , tr , hl , kp)
  with translate-end ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
...   | (h″ , _ , eq) =
      let tr′ = translate ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
      in r , subs-map d , tr′
       , unheadHolds (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′) (subst (λ p → PreHolds _ _ p _ _) eq hl)
       , unheadKept (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′) {sched} {sched} {st = st} {st₁ = st}
           (λ _ _ ()) ≤-refl (λ _ _ → refl) (λ _ _ _ ea → ea) (subst (λ p → Kept _ p _ _ _ _) eq kp)
red-map {n = n} {s = s} f b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK
         (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
         (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (map-f (_ , f , ρ) ↠[ ≤-refl ] κ))) s₀ now sched st rm
         (grounded (ground fell) (push-sound (map-f (_ , f , ρ)) ≤-refl κ (sounds fell) (λ k ())))
... | (r , d , tr , hl , kp) =
      r , subs-map d , []ᵗ
    , unheadHolds (map-f (_ , f , ρ)) ≤-refl κ tt fallen
        (subst (λ p → PreHolds _ (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) p _ _) (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

-- A TRUNCATION CANNOT INVENT A VALUE, WHICH IS WHY THE TAKE FRAME NEEDS
-- NOTHING FROM THE STORE.  The node a take installs holds a COUNT, and
-- the dispatch's value column is a prefix of the burst it was handed --
-- on the cut path and the non-cut path alike, and at a stuck lookup the
-- column is empty.  So the arriving candidates are the departing ones
-- and the store decides only HOW MANY survive.
redTakeVals : ∀ {n} {Γ : Ctx n} {s} {P : Val Γ s → Set₁} (k : ℕ)
              {vals : List (Val Γ s)} → All P vals
            → All P (proj₁ (takeVals k vals))
redTakeVals zero          rv          = []ᵃ
redTakeVals (suc k)       []ᵃ         = []ᵃ
redTakeVals (suc zero)    (p ∷ᵃ ps)   = p ∷ᵃ []ᵃ
redTakeVals (suc (suc k)) (p ∷ᵃ ps)   = p ∷ᵃ redTakeVals (suc k) ps

redTakeDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {P : Val Γ s → Set₁}
                  (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (ns : Maybe (NodeState Γ))
                → All P vals
                → All P (proj₁ (takeDispatch {e = e} nid vals fin sched st ns))
redTakeDispatch nid {vals} fin sched st (just (take-st k)) rv
  with proj₂ (proj₂ (takeVals k vals))
... | true  = redTakeVals k rv
... | false = redTakeVals k rv
redTakeDispatch nid fin sched st (just (cell-st _))           rv = []ᵃ
redTakeDispatch nid fin sched st (just (batchSync-st _ _ _))  rv = []ᵃ
redTakeDispatch nid fin sched st (just (mergeAll-st _ _ _ _)) rv = []ᵃ
redTakeDispatch nid fin sched st (just (switch-st _ _))       rv = []ᵃ
redTakeDispatch nid fin sched st (just (exhaust-st _ _))      rv = []ᵃ
redTakeDispatch nid fin sched st nothing                      rv = []ᵃ

-- the dispatch writes its own node and no other, and the cut sweeps
-- rows and the live set but mints nothing
takeOff : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            (nid : NodeId) (ns : Maybe (NodeState Γ)) (vals : List (Val Γ s)) (fin : Bool)
            (sched : Sched Γ) (st : EvalSt e) (k : NodeId) → (nid ≡ᵇ k) ≡ false
        → lookupNode k (EvalSt.nodes (proj₂ (proj₂ (proj₂ (takeDispatch {e = e} nid vals fin sched st ns)))))
        ≡ lookupNode k (EvalSt.nodes st)
takeOff nid (just (take-st j)) vals fin sched st k ne with proj₂ (proj₂ (takeVals j vals))
... | true  = set-above nid k (take-st zero) (EvalSt.nodes st) ne
... | false = set-above nid k (take-st (proj₁ (proj₂ (takeVals j vals)))) (EvalSt.nodes st) ne
takeOff nid (just (cell-st _))           vals fin sched st k ne = refl
takeOff nid (just (batchSync-st _ _ _))  vals fin sched st k ne = refl
takeOff nid (just (mergeAll-st _ _ _ _)) vals fin sched st k ne = refl
takeOff nid (just (switch-st _ _))       vals fin sched st k ne = refl
takeOff nid (just (exhaust-st _ _))      vals fin sched st k ne = refl
takeOff nid nothing                      vals fin sched st k ne = refl

takeCt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           (nid : NodeId) (ns : Maybe (NodeState Γ)) (vals : List (Val Γ s)) (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
       → nodeCt (proj₁ (proj₂ (proj₂ (takeDispatch {e = e} nid vals fin sched st ns)))) ≡ nodeCt sched
takeCt nid (just (take-st j)) vals fin sched st with proj₂ (proj₂ (takeVals j vals))
... | true  = refl
... | false = refl
takeCt nid (just (cell-st _))           vals fin sched st = refl
takeCt nid (just (batchSync-st _ _ _))  vals fin sched st = refl
takeCt nid (just (mergeAll-st _ _ _ _)) vals fin sched st = refl
takeCt nid (just (switch-st _ _))       vals fin sched st = refl
takeCt nid (just (exhaust-st _ _))      vals fin sched st = refl
takeCt nid nothing                      vals fin sched st = refl

-- and it only cuts rows
takeReg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            (nid : NodeId) (ns : Maybe (NodeState Γ)) (vals : List (Val Γ s)) (fin : Bool)
            (sched : Sched Γ) (st : EvalSt e) {r}
        → r ∈ EvalSt.registry (proj₂ (proj₂ (proj₂ (takeDispatch {e = e} nid vals fin sched st ns))))
        → r ∈ EvalSt.registry st
takeReg nid (just (take-st j)) vals fin sched st {r} r∈ with proj₂ (proj₂ (takeVals j vals))
... | true  = cut-sub nid (EvalSt.registry st) r r∈
... | false = r∈
takeReg nid (just (cell-st _))           vals fin sched st r∈ = r∈
takeReg nid (just (batchSync-st _ _ _))  vals fin sched st r∈ = r∈
takeReg nid (just (mergeAll-st _ _ _ _)) vals fin sched st r∈ = r∈
takeReg nid (just (switch-st _ _))       vals fin sched st r∈ = r∈
takeReg nid (just (exhaust-st _ _))      vals fin sched st r∈ = r∈
takeReg nid nothing                      vals fin sched st r∈ = r∈

-- THE TAKE FRAME'S STEP: the dispatch at what the frame holds, holding
-- what the dispatch wrote.  Agreement is what lets the derivation read
-- the store and the step read the held state, and they are one read.
takeStepped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} (nid : NodeId)
            → Maybe (NodeState Γ) → List (Val Γ s) → Bool → Sched Γ → EvalSt e
            → Stepped {e = e} (take-f {s = s} nid)
takeStepped nid h vals fin sched st =
  let r = takeDispatch nid vals fin sched st h
  in stepped (proj₁ r) (proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))
             (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ (proj₂ r)))))

takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} (nid : NodeId) {P : Val Γ s → Set₁}
         → FrameStep {e = e} (take-f nid) P P (λ _ → ⊤)
takeStep nid = record
  { step      = takeStepped nid
  ; step-⇓    = λ {_} {κ} {now} h vals fin sched st c →
                  subst (λ x → stepFrame⇓ now (take-f nid) κ vals fin sched st
                                 (injectRoot (takeDispatch nid vals fin sched st x)))
                        c step-take
  ; step-red  = λ {h} {vals} {fin} {sched} {st} ps _ → redTakeDispatch nid fin sched st h ps , tt
  ; step-cons = λ _ _ _ _ _ _ → refl
  ; step-off  = λ h vals fin sched st k ne → takeOff nid h vals fin sched st k (head-off nid [] k ne)
  ; step-ct   = takeCt nid
  ; step-reg  = λ h vals fin sched st → takeReg nid h vals fin sched st }

-- THE NODE THE COUNTER HANDS OUT IS ON EVERY PATH THE RULE HOLDS FOR,
-- once installed: no row runs through it, so every row through it ends
-- wherever the path does.
fresh-on : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u} (κ : Path Γ lo u t)
             (ns : NodeState Γ) {sched : Sched Γ} {st : EvalSt e}
         → Sound κ sched st
         → NodeOn (nodeCt sched) κ (bumpNode sched) (installNode (nodeCt sched) ns st)
fresh-on κ ns so = node-on (λ r∈ th → ⊥-elim (<-irrefl refl (fresh-rows (ruled so) r∈ _ th))) ≤-refl
                             (λ on → <-irrefl refl (fresh-path so _ on))

-- A FRAME WHOSE NODES ARE THE ONE THE COUNTER HANDS OUT, installed
-- there, stands on the rule
fresh-sound : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo s u} (f : Frame Γ s u) (κ : Path Γ lo u t)
                (ns : NodeState Γ) {sched : Sched Γ} {st : EvalSt e}
            → (∀ k → T (any (_≡ᵇ k) (frameNodes f)) → nodeCt sched ≡ k)
            → Sound κ sched st
            → Sound (f ↠[ ≤-refl ] κ) (bumpNode sched) (installNode (nodeCt sched) ns st)
fresh-sound f κ ns {sched} {st} one so =
  push-sound f ≤-refl κ (sub-ot (λ r∈ → r∈) (n≤1+n _) so)
    (λ k a → subst (λ j → NodeOn j κ (bumpNode sched) (installNode (nodeCt sched) ns st)) (one k a) (fresh-on κ ns so))

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
red-take c b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h | suc j
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok) aK
         (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c)))) aM
         (take-f (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just (take-st (suc j)) , pfs))
         (liveRP ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp)
         s₀ now (bumpNode sched) (installNode (nodeCt sched) (take-st (suc j)) st) rm
         (fresh-holds (take-f (nodeCt sched)) κ pfs (just (take-st (suc j))) (take-st (suc j)) (λ _ → node-eq)
            (lookup-set (nodeCt sched) (take-st (suc j)) (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) h)
... | (r , d , tr , hl , kp)
  with translate-end ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp tr
...   | (h″ , _ , eq′) =
      let tr′ = translate ≤-refl aM (takeStep (nodeCt sched)) (just (take-st (suc j))) tt κ pfs rp tr
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
red-take {n = n} c b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell | suc j
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok) aK
         (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c)))) aM
         (take-f (nodeCt sched) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (take-f (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) (take-st (suc j)) st) rm
         (grounded (ground fell) (fresh-sound (take-f (nodeCt sched)) κ (take-st (suc j)) (λ _ → node-eq) (sounds fell)))
... | (r , d , tr , hl , kp) =
      r , subs-take-suc eq refl d , []ᵗ
    , unheadHolds (take-f (nodeCt sched)) ≤-refl κ nothing fallen
        (subst (λ p → PreHolds _ (take-f (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
           (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

-- A FOLD IS ITS ACCUMULATOR THREADED ALONG THE BATCH, and so is the
-- claim about it: each output IS the next accumulator, so one walk
-- delivers both the candidate at every emitted value and the candidate
-- at what gets written back.
redScanVals : ∀ {n} {Γ : Ctx n} {m s u} (fn : FnClo Γ (u ×ᵗ s) u)
            → (∀ {v} → Red m (u ×ᵗ s) v → Red m u (applyClo fn v))
            → {a : Val Γ u} → Red m u a
            → {vals : List (Val Γ s)} → All (Red m s) vals
            → All (Red m u) (proj₁ (scanVals fn a vals)) × Red m u (proj₂ (scanVals fn a vals))
redScanVals fn rf ra []ᵃ       = []ᵃ , ra
redScanVals fn rf ra (p ∷ᵃ ps) =
  let q = rf (ra , p)
  in q ∷ᵃ proj₁ (redScanVals fn rf q ps) , proj₂ (redScanVals fn rf q ps)

-- WHAT THE SCAN FRAME HOLDS A CANDIDATE FOR: the accumulator its cell
-- holds, whenever it holds one of the frame's own type
ScanHeld : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → Maybe (NodeState Γ) → Set₁
ScanHeld {Γ = Γ} m u h = ∀ {a : Val Γ u} → h ≡ just (cell-st a) → Red m u a

cell-inj : ∀ {n} {Γ : Ctx n} {u} {a b : Val Γ u} → just (cell-st {Γ = Γ} a) ≡ just (cell-st b) → a ≡ b
cell-inj refl = refl

-- what the frame holds after the dispatch: the cell it wrote, or what it
-- held where the dispatch wrote nothing
scanHeld : ∀ {n} {Γ : Ctx n} {s u} → FnClo Γ (u ×ᵗ s) u → List (Val Γ s)
         → Maybe (NodeState Γ) → Maybe (NodeState Γ)
scanHeld {u = u} fn vals (just (cell-st {w} a)) with w ≟ᵗ u
... | no  _    = just (cell-st a)
... | yes refl = just (cell-st (proj₂ (scanVals fn a vals)))
scanHeld fn vals h = h

scanRed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s u} (fn : FnClo Γ (u ×ᵗ s) u)
            (rf : ∀ {v} → Red m (u ×ᵗ s) v → Red m u (applyClo fn v))
            (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
            (h : Maybe (NodeState Γ))
        → All (Red m s) vals → ScanHeld m u h
        → All (Red m u) (proj₁ (scanDispatch {e = e} fn nid vals fin sched st h)) × ScanHeld m u (scanHeld fn vals h)
scanRed {u = u} fn rf nid fin sched st (just (cell-st {w} a)) ps rh with w ≟ᵗ u
... | no  _    = []ᵃ , rh
... | yes refl =
      proj₁ (redScanVals fn rf (rh refl) ps)
    , λ eq → subst (Red _ u) (cell-inj eq) (proj₂ (redScanVals fn rf (rh refl) ps))
scanRed fn rf nid fin sched st (just (take-st _))           ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (batchSync-st _ _ _))  ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (mergeAll-st _ _ _ _)) ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (switch-st _ _))       ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st (just (exhaust-st _ _))      ps rh = []ᵃ , rh
scanRed fn rf nid fin sched st nothing                      ps rh = []ᵃ , rh

scanCons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ (u ×ᵗ s) u)
             (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
             (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h
         → lookupNode nid (EvalSt.nodes (proj₂ (proj₂ (proj₂ (scanDispatch {e = e} fn nid vals fin sched st h)))))
         ≡ scanHeld fn vals h
scanCons {u = u} fn nid vals fin sched st (just (cell-st {w} a)) c with w ≟ᵗ u
... | no  _    = c
... | yes refl = lookup-set nid (cell-st (proj₂ (scanVals fn a vals))) (EvalSt.nodes st)
scanCons fn nid vals fin sched st (just (take-st _))           c = c
scanCons fn nid vals fin sched st (just (batchSync-st _ _ _))  c = c
scanCons fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) c = c
scanCons fn nid vals fin sched st (just (switch-st _ _))       c = c
scanCons fn nid vals fin sched st (just (exhaust-st _ _))      c = c
scanCons fn nid vals fin sched st nothing                      c = c

scanOff : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ (u ×ᵗ s) u)
            (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
            (h : Maybe (NodeState Γ)) (k : NodeId) → (nid ≡ᵇ k) ≡ false
        → lookupNode k (EvalSt.nodes (proj₂ (proj₂ (proj₂ (scanDispatch {e = e} fn nid vals fin sched st h)))))
        ≡ lookupNode k (EvalSt.nodes st)
scanOff {u = u} fn nid vals fin sched st (just (cell-st {w} a)) k ne with w ≟ᵗ u
... | no  _    = refl
... | yes refl = set-above nid k (cell-st (proj₂ (scanVals fn a vals))) (EvalSt.nodes st) ne
scanOff fn nid vals fin sched st (just (take-st _))           k ne = refl
scanOff fn nid vals fin sched st (just (batchSync-st _ _ _))  k ne = refl
scanOff fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) k ne = refl
scanOff fn nid vals fin sched st (just (switch-st _ _))       k ne = refl
scanOff fn nid vals fin sched st (just (exhaust-st _ _))      k ne = refl
scanOff fn nid vals fin sched st nothing                      k ne = refl

scanCt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ (u ×ᵗ s) u)
           (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
           (h : Maybe (NodeState Γ))
       → nodeCt (proj₁ (proj₂ (proj₂ (scanDispatch {e = e} fn nid vals fin sched st h)))) ≡ nodeCt sched
scanCt {u = u} fn nid vals fin sched st (just (cell-st {w} a)) with w ≟ᵗ u
... | no  _    = refl
... | yes refl = refl
scanCt fn nid vals fin sched st (just (take-st _))           = refl
scanCt fn nid vals fin sched st (just (batchSync-st _ _ _))  = refl
scanCt fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
scanCt fn nid vals fin sched st (just (switch-st _ _))       = refl
scanCt fn nid vals fin sched st (just (exhaust-st _ _))      = refl
scanCt fn nid vals fin sched st nothing                      = refl

-- and it leaves the registry alone
scanReg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ (u ×ᵗ s) u)
            (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
            (h : Maybe (NodeState Γ))
        → EvalSt.registry (proj₂ (proj₂ (proj₂ (scanDispatch {e = e} fn nid vals fin sched st h)))) ≡ EvalSt.registry st
scanReg {u = u} fn nid vals fin sched st (just (cell-st {w} a)) with w ≟ᵗ u
... | no  _    = refl
... | yes refl = refl
scanReg fn nid vals fin sched st (just (take-st _))           = refl
scanReg fn nid vals fin sched st (just (batchSync-st _ _ _))  = refl
scanReg fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
scanReg fn nid vals fin sched st (just (switch-st _ _))       = refl
scanReg fn nid vals fin sched st (just (exhaust-st _ _))      = refl
scanReg fn nid vals fin sched st nothing                      = refl

-- THE SCAN FRAME'S STEP: the dispatch at what the frame holds, holding
-- the accumulator it wrote back, with the closure's candidate carried
-- along the batch from the one the frame held.
scanStepped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
            → Maybe (NodeState Γ) → List (Val Γ s) → Bool → Sched Γ → EvalSt e
            → Stepped {e = e} (scan-f fn nid)
scanStepped fn nid h vals fin sched st =
  let r = scanDispatch fn nid vals fin sched st h
  in stepped (proj₁ r) (proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))
             (scanHeld fn vals h)

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
red-scan f z b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
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
... | (r , d , tr , hl , kp)
  with translate-end ≤-refl aM
         (scanStep (_ , f , ρ) (nodeCt sched)
           (λ {v} p → redTmAcc f (v ∷ᵉ ρ) (p , rρ) k (∧ˡ (inputsBelowᵗ k f) _ ok) aK
                        (rs (s≤s (m≤m+n (gsizeᵗ f) _))) aM))
         (just (cell-st (evalWith z ρ)))
         (λ eq → subst (Red _ _) (cell-inj eq)
                   (redTmAcc z ρ rρ k (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
                      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b)) (m≤n+m _ (gsizeᵗ f))))) aM))
         κ pfs rp tr
...   | (h″ , _ , eq′) =
      let tr′ = translate ≤-refl aM
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
red-scan {n = n} f z b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) (∧ʳ (inputsBelowᵗ k f) _ ok)) aK
         (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z)) (m≤n+m _ (gsizeᵗ f))))) aM
         (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) (cell-st (evalWith z ρ)) st) rm
         (grounded (ground fell) (fresh-sound (scan-f (_ , f , ρ) (nodeCt sched)) κ (cell-st (evalWith z ρ)) (λ _ → node-eq) (sounds fell)))
... | (r , d , tr , hl , kp) =
      r , subs-scan refl d , []ᵗ
    , unheadHolds (scan-f (_ , f , ρ) (nodeCt sched)) ≤-refl κ nothing fallen
        (subst (λ p → PreHolds _ (scan-f (_ , f , ρ) (nodeCt sched) ↠[ ≤-refl ] κ) p (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
           (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl)
    , tt

-- WHAT THE BATCH FRAME HOLDS A CANDIDATE FOR: the buffer its bracket
-- holds, whenever it holds one of the frame's own element type.  The
-- buffer is only ever a concatenation of arrivals, so the candidates
-- are the arrivals' own.
BatchHeld : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → Maybe (NodeState Γ) → Set₁
BatchHeld {Γ = Γ} m u h =
  ∀ {sync} {bur : List (Val Γ u)} {done} → h ≡ just (batchSync-st {s = u} sync bur done) → All (Red m u) bur

-- the bracket the install opens holds nothing
batch₀ : ∀ {n} {Γ : Ctx n} {m u} → BatchHeld {Γ = Γ} m u (just (batchSync-st {s = u} true [] false))
batch₀ refl = []ᵃ

-- a regrouping of candidates is candidates for the groups
redBatch : ∀ {n} {Γ : Ctx n} {m s} (sync : Bool) {vals : List (Val Γ s)}
         → All (Red m s) vals → All (Red m (s ×ᵗ listᵗ s)) (batchVals sync vals)
redBatch _     []ᵃ       = []ᵃ
redBatch true  (p ∷ᵃ ps) = (p , ps) ∷ᵃ []ᵃ
redBatch false (p ∷ᵃ ps) = (p , []ᵃ) ∷ᵃ redBatch false ps

-- what the frame holds after the dispatch: the bracket it wrote, or
-- what it held where the dispatch wrote nothing
batchHeld : ∀ {n} {Γ : Ctx n} {s} → List (Val Γ s) → Bool → Maybe (NodeState Γ) → Maybe (NodeState Γ)
batchHeld {s = s} vals fin (just (batchSync-st {w} true bur done)) with w ≟ᵗ s
... | no  _    = just (batchSync-st true bur done)
... | yes refl = just (batchSync-st true (bur ++ vals) (done ∨ fin))
batchHeld {s = s} vals fin (just (batchSync-st {w} false bur done)) with w ≟ᵗ s
... | no  _    = just (batchSync-st false bur done)
... | yes refl = just (batchSync-st {s = s} false [] false)
batchHeld vals fin h = h

batchRed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s} (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e) (h : Maybe (NodeState Γ))
         → All (Red m s) vals → BatchHeld m s h
         → All (Red m (s ×ᵗ listᵗ s)) (proj₁ (batchDispatch {e = e} nid vals fin sched st h))
         × BatchHeld m s (batchHeld vals fin h)
batchRed {s = s} nid fin sched st (just (batchSync-st {w} true bur done)) ps rh with w ≟ᵗ s
... | no  _    = []ᵃ , rh
... | yes refl = []ᵃ , λ { refl → ++⁺ (rh refl) ps }
batchRed {s = s} nid fin sched st (just (batchSync-st {w} false bur done)) ps rh with w ≟ᵗ s
... | no  _    = redBatch false ps , rh
... | yes refl = ++⁺ (redBatch true (rh refl)) (redBatch false ps) , λ { refl → []ᵃ }
batchRed nid fin sched st (just (cell-st _))           ps rh = []ᵃ , rh
batchRed nid fin sched st (just (take-st _))           ps rh = []ᵃ , rh
batchRed nid fin sched st (just (mergeAll-st _ _ _ _)) ps rh = []ᵃ , rh
batchRed nid fin sched st (just (switch-st _ _))       ps rh = []ᵃ , rh
batchRed nid fin sched st (just (exhaust-st _ _))      ps rh = []ᵃ , rh
batchRed nid fin sched st nothing                      ps rh = []ᵃ , rh

batchCons : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
              (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
              (h : Maybe (NodeState Γ)) → lookupNode nid (EvalSt.nodes st) ≡ h
          → lookupNode nid (EvalSt.nodes (proj₂ (proj₂ (proj₂ (batchDispatch {e = e} nid vals fin sched st h)))))
          ≡ batchHeld vals fin h
batchCons {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done)) c with w ≟ᵗ s
... | no  _    = c
... | yes refl = lookup-set nid (batchSync-st true (bur ++ vals) (done ∨ fin)) (EvalSt.nodes st)
batchCons {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done)) c with w ≟ᵗ s
... | no  _    = c
... | yes refl = lookup-set nid (batchSync-st {s = s} false [] false) (EvalSt.nodes st)
batchCons nid vals fin sched st (just (cell-st _))           c = c
batchCons nid vals fin sched st (just (take-st _))           c = c
batchCons nid vals fin sched st (just (mergeAll-st _ _ _ _)) c = c
batchCons nid vals fin sched st (just (switch-st _ _))       c = c
batchCons nid vals fin sched st (just (exhaust-st _ _))      c = c
batchCons nid vals fin sched st nothing                      c = c

batchOff : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
             (h : Maybe (NodeState Γ)) (k : NodeId) → (nid ≡ᵇ k) ≡ false
         → lookupNode k (EvalSt.nodes (proj₂ (proj₂ (proj₂ (batchDispatch {e = e} nid vals fin sched st h)))))
         ≡ lookupNode k (EvalSt.nodes st)
batchOff {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done)) k ne with w ≟ᵗ s
... | no  _    = refl
... | yes refl = set-above nid k (batchSync-st true (bur ++ vals) (done ∨ fin)) (EvalSt.nodes st) ne
batchOff {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done)) k ne with w ≟ᵗ s
... | no  _    = refl
... | yes refl = set-above nid k (batchSync-st {s = s} false [] false) (EvalSt.nodes st) ne
batchOff nid vals fin sched st (just (cell-st _))           k ne = refl
batchOff nid vals fin sched st (just (take-st _))           k ne = refl
batchOff nid vals fin sched st (just (mergeAll-st _ _ _ _)) k ne = refl
batchOff nid vals fin sched st (just (switch-st _ _))       k ne = refl
batchOff nid vals fin sched st (just (exhaust-st _ _))      k ne = refl
batchOff nid vals fin sched st nothing                      k ne = refl

batchCt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
            (h : Maybe (NodeState Γ))
        → nodeCt (proj₁ (proj₂ (proj₂ (batchDispatch {e = e} nid vals fin sched st h)))) ≡ nodeCt sched
batchCt {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done)) with w ≟ᵗ s
... | no  _    = refl
... | yes refl = refl
batchCt {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done)) with w ≟ᵗ s
... | no  _    = refl
... | yes refl = refl
batchCt nid vals fin sched st (just (cell-st _))           = refl
batchCt nid vals fin sched st (just (take-st _))           = refl
batchCt nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
batchCt nid vals fin sched st (just (switch-st _ _))       = refl
batchCt nid vals fin sched st (just (exhaust-st _ _))      = refl
batchCt nid vals fin sched st nothing                      = refl

batchReg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
             (h : Maybe (NodeState Γ))
         → EvalSt.registry (proj₂ (proj₂ (proj₂ (batchDispatch {e = e} nid vals fin sched st h)))) ≡ EvalSt.registry st
batchReg {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done)) with w ≟ᵗ s
... | no  _    = refl
... | yes refl = refl
batchReg {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done)) with w ≟ᵗ s
... | no  _    = refl
... | yes refl = refl
batchReg nid vals fin sched st (just (cell-st _))           = refl
batchReg nid vals fin sched st (just (take-st _))           = refl
batchReg nid vals fin sched st (just (mergeAll-st _ _ _ _)) = refl
batchReg nid vals fin sched st (just (switch-st _ _))       = refl
batchReg nid vals fin sched st (just (exhaust-st _ _))      = refl
batchReg nid vals fin sched st nothing                      = refl

-- THE BATCH FRAME'S STEP: the dispatch at what the frame holds, holding
-- the bracket it wrote.  With the bit up the arrivals go into the
-- buffer beside their candidates; with it down the buffer's candidates
-- leave as the flushed group's.
batchStepped : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} (nid : NodeId)
             → Maybe (NodeState Γ) → List (Val Γ s) → Bool → Sched Γ → EvalSt e
             → Stepped {e = e} (batchSync-f {s = s} nid)
batchStepped nid h vals fin sched st =
  let r = batchDispatch nid vals fin sched st h
  in stepped (proj₁ r) (proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))
             (batchHeld vals fin h)

batchStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m s} (nid : NodeId)
          → FrameStep {e = e} (batchSync-f {s = s} nid) (Red m s) (Red m (s ×ᵗ listᵗ s)) (BatchHeld m s)
batchStep {s = s} nid = record
  { step      = batchStepped nid
  ; step-⇓    = λ {_} {κ} {now} h vals fin sched st c →
                  subst (λ x → stepFrame⇓ now (batchSync-f nid) κ vals fin sched st
                                 (injectRoot {u = s ×ᵗ listᵗ s} (batchDispatch nid vals fin sched st x)))
                        c step-batchSync
  ; step-red  = λ {h} {vals} {fin} {sched} {st} ps rh → batchRed nid fin sched st h ps rh
  ; step-cons = λ h vals fin sched st c → batchCons nid vals fin sched st h c
  ; step-off  = λ h vals fin sched st k ne → batchOff nid vals fin sched st h k (head-off nid [] k ne)
  ; step-ct   = λ h vals fin sched st → batchCt nid vals fin sched st h
  ; step-reg  = λ h vals fin sched st r∈ → subst (_ ∈_) (batchReg nid vals fin sched st h) r∈ }

-- lowering the bit keeps the buffer, so it keeps the buffer's
-- candidates; a bracket of another type is emptied
downHeld : ∀ {n} {Γ : Ctx n} {m} (u : Ty) (x : Maybe (NodeState Γ))
         → BatchHeld m u x → BatchHeld m u (just (batchDown u x))
downHeld u (just (batchSync-st {w} sync bur done)) rh with w ≟ᵗ u
... | no  _    = λ { refl → []ᵃ }
... | yes refl = λ { refl → rh refl }
downHeld u (just (cell-st _))           rh = λ { refl → []ᵃ }
downHeld u (just (take-st _))           rh = λ { refl → []ᵃ }
downHeld u (just (mergeAll-st _ _ _ _)) rh = λ { refl → []ᵃ }
downHeld u (just (switch-st _ _))       rh = λ { refl → []ᵃ }
downHeld u (just (exhaust-st _ _))      rh = λ { refl → []ᵃ }
downHeld u nothing                      rh = λ { refl → []ᵃ }

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
red-batchSync {t = u} b ρ rρ k ok aK (acc rs) aM κ (standing pfs) rp s₀ now sched st rm h
  with redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
         (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just (batchSync-st {s = u} true [] false) , pfs))
         (liveRP ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp)
         s₀ now (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) rm
         (fresh-holds (batchSync-f (nodeCt sched)) κ pfs (just (batchSync-st {s = u} true [] false))
            (batchSync-st {s = u} true [] false) (λ _ → node-eq)
            (lookup-set (nodeCt sched) (batchSync-st {s = u} true [] false) (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) h)
... | ((o₁ , sc₁ , st₁) , d , tr , hl , kp)
  with translate-end ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp tr
...   | (h″ , rh″ , eq′) =
      batchFinish b ρ aM κ (standing pfs) rp s₀ now sched st rm
        (stage o₁ sc₁ st₁ d
           (translate ≤-refl aM (batchStep (nodeCt sched)) (just (batchSync-st {s = u} true [] false)) batch₀ κ pfs rp tr)
           refl h″
           (subst (λ p → PreHolds _ (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) p sc₁ st₁) eq′ hl)
           (subst (λ p → Kept (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) p (bumpNode sched)
                                (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) sc₁ st₁) eq′ kp))
        rh″
red-batchSync {n = n} {t = u} b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k ok aK (rs ≤-refl) aM
         (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (batchSync-f (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) (batchSync-st {s = u} true [] false) st) rm
         (grounded (ground fell)
            (fresh-sound (batchSync-f (nodeCt sched)) κ (batchSync-st {s = u} true [] false) (λ _ → node-eq) (sounds fell)))
... | ((o₁ , sc₁ , st₁) , d , tr , hl , kp) =
      batchFinish b ρ aM κ fallen rp s₀ now sched st rm
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
red-input-shared {n = n} i d {okd} aI ρ κ below pre rp s now sched slEq st aM rm h
    with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
... | true =
      let c  = call now [] (ofColumn κ pre []) true sched st rm h
          an = apply rp s c
      in _ , subs-shared {κ = κ} {below = below} slEq (slot-spent {κ = κ} {below = below} doneEq (der an))
         , c ∷ᵗ []ᵗ , Ans.holds′ an , kept an
red-input-shared {n = n} {lo = lo} i d {okd} aI ρ κ below pre rp s now sched slEq st aM rm h
    | false with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
...   | true =
        _ , subs-shared {κ = κ} {below = below} slEq (slot-join {κ = κ} {below = below} doneEq connEq refl)
        , []ᵗ , holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x) (row-sound i below κ sched st) h
        , kept-step κ pre (pres (λ _ _ → refl)) ≤-refl
            (ends-register {κ = κ} {sched = sched} {st = st} (freshId regᵏ (Sched.mint sched)) (atSlot i) (lowerFloor below κ)
               (λ k′ on → inj₁ (subst T (lower-nodes below κ k′) on)))
...   | false
      with (let rid    = freshId regᵏ (Sched.mint sched)
                sched′ = record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                st′    = register rid (atSlot i) (lowerFloor below κ)
                           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
                fell′  = ≤-trans (unconn-insert (Sched.slots sched) (EvalSt.connectedShares st) i slEq connEq) rm
            in redExpAcc d []ᵉ tt (toℕ i) okd aI (<-wellFounded (gsizeᵉ d)) aM
                 (share-sink i ≤-refl) fallen
                 (dropS (fallenRP (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl)))
                 tt now sched′ st′ (<⇒≤ fell′) (grounded fell′ (sink-sound i ≤-refl (ruled (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h)))))))
...     | (r , dv , tr , hl , _) =
          r , subs-shared {κ = κ} {below = below} slEq
                (slot-connect {κ = κ} {below = below} doneEq connEq (connect {κ = κ} {below = below} refl dv))
          , fellᵗ (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM κ)) s
          , grounded
              (ground (subst (λ p → PreHolds _ (share-sink i ≤-refl) p _ _)
                        (fallen-stays (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl) tr) hl))
              (subscribe-kept dv (sink-sound i ≤-refl (ruled (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h))))) κ (row-sound i below κ sched (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) (sub-ot (λ r∈ → r∈) ≤-refl (sounds h))) (λ k ()))
          , tt

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
  with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
     | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
... | oksc | rest
  with evalWith sc ρ
     | redTmAcc sc ρ rρ k oksc aK
         (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r)))) aM
... | inj₁ x | q =
  redTmAcc l (x ∷ᵉ ρ) (q , rρ) k
    (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
    (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                      (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc))))) aM
... | inj₂ y | q =
  redTmAcc r (y ∷ᵉ ρ) (q , rρ) k
    (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
    (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                      (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc))))) aM
redTmAcc (ifᵗ c x y) ρ rρ k ok aK (acc rs) aM
  with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
... | rest with evalWith c ρ
... | true  =
  redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
    (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                      (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c))))) aM
... | false =
  redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
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

rawInner {u = u} ac le aM op nid κ now o sched st rm so nd h eq aq =
  let κ′  = from-inner {s = u} op nid (nodeCt sched) ↠[ ≤-refl ] κ
      so′ = fresh-inner op nid κ sched so nd
      (r , d , _) = red-val aM (obs u) o κ′ (standing (h , colsOf κ st))
                      (baseRP ac le aM op nid (nodeCt sched) κ (h , colsOf κ st) aq) tt now (bumpNode sched) st rm
                      (grounded (subst (λ x → HoldsFs κ′ (x , colsOf κ st) (bumpNode sched) st) eq
                                   (holdsOf κ′ (fresh-path so′) (distinct so′))) so′)
  in r , d

-- the base: its exit frame reacts at the budget its column pins, and the
-- path below folds raw
fold (baseRP ac le aM op nid inst κ (h , pfs) aq) tt now vals _ fin sched st rm (grounded hs so) =
  let (r₀ , sd , so₀) = rawReact ac le aM op nid inst ≤-refl κ now vals fin sched st rm so h (proj₁ (proj₁ hs)) aq
      (r , d) = rawAfter ac le aM (from-inner op nid inst) ≤-refl κ r₀ sd (room-keeps (stepFrame-keeps sd) rm) so₀
  in baseAns ac le aM op nid inst κ sched st rm so r d

baseAns ac le aM op nid inst κ sched st rm so (out , sched′ , st′) d
  with unconn (Sched.slots sched′) (EvalSt.connectedShares st′) <? unconn (Sched.slots sched) (EvalSt.connectedShares st)
... | yes sp =
  ans out sched′ st′ d fallen (grounded (<-≤-trans sp rm) (fold-sound d so)) tt
      (fallenRP ac le aM (from-inner op nid inst ↠[ ≤-refl ] κ)) tt
... | no nsp =
  let κ′  = from-inner op nid inst ↠[ ≤-refl ] κ
      so′ = fold-sound d so
  in ans out sched′ st′ d (standing (colsOf κ′ st′))
         (grounded (holdsOf κ′ {sched = sched′} {st = st′} (fresh-path so′) (distinct so′)) so′)
         (raw-kept d so nsp {pfs = colsOf κ′ st′})
         (baseRP ac le aM op nid inst κ (colsOf κ′ st′) (<-wellFounded _)) tt

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

-- THE INNER FRAME'S GROUND READ BACK AS THE OUTER'S, AND AS AN EARLIER
-- INSTANCE'S.  Both frames hold the flattener's node the same way;
-- the outer names only that node, and an earlier instance is below
-- the counter and apart from the path by the frame it came from.
fiHolds→thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ u}
               (op : AllOp) (nid inst : NodeId) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
               (h : Maybe (NodeState Γ)) (p : Pre κ) {sched : Sched Γ} {st : EvalSt e}
             → PreHolds m (from-inner {s = u} op nid inst ↠[ ≤-refl ] κ) (headPre h p) sched st
             → PreHolds m (thru-outer op nid ↠[ le ] κ) (headPre h p) sched st
fiHolds→thru op nid inst le κ h (standing pfs) (grounded ((c , lt ∷ᵃ _) , ap , hs) so) =
  grounded
    ((c , lt ∷ᵃ []ᵃ) , (λ k on → ap k (∨-Tˡ {nid ≡ᵇ k} {any (_≡ᵇ k) (inst ∷ [])} ([ (λ a → a) , (λ ()) ] (∨-T {nid ≡ᵇ k} {false} on)))) , hs)
    (let (so′ , nd) = inner-back op nid inst κ so in push-thru op nid le κ so′ nd)
fiHolds→thru op nid inst le κ h fallen (grounded fell so) =
  grounded fell (let (so′ , nd) = inner-back op nid inst κ so in push-thru op nid le κ so′ nd)

-- THE TWO COLUMN GUARDS, WHICH ARE WHY NOTHING IS DRAINED ON STANDING
-- GROUND.  The outer's column never holds a queue beside a free lane:
-- it is installed empty, it queues only when every lane is taken, and
-- it reads back the inner's column, which never holds a queue at all.
-- A walk-order inner is subscribed only through a free lane, so its
-- column starts with nothing queued; nothing but its own step writes
-- it while the path stands, and its finish drains what the column
-- says, which is nothing.  So the finish never subscribes, and the
-- candidate never re-enters itself at the ceiling it was built at.  A
-- queue beside a busy lane is drained by a later finish, and that is
-- the raw fold's.
RoomEmpty : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
RoomEmpty (just (mergeAll-st lim act q _)) = T (hasRoom lim act) → q ≡ []
RoomEmpty (just (cell-st _))               = ⊤
RoomEmpty (just (take-st _))               = ⊤
RoomEmpty (just (batchSync-st _ _ _))      = ⊤
RoomEmpty (just (switch-st _ _))           = ⊤
RoomEmpty (just (exhaust-st _ _))          = ⊤
RoomEmpty nothing                          = ⊤

QEmpty : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
QEmpty (just (mergeAll-st _ _ q _)) = q ≡ []
QEmpty (just (cell-st _))           = ⊤
QEmpty (just (take-st _))           = ⊤
QEmpty (just (batchSync-st _ _ _))  = ⊤
QEmpty (just (switch-st _ _))       = ⊤
QEmpty (just (exhaust-st _ _))      = ⊤
QEmpty nothing                      = ⊤

qempty-room : ∀ {n} {Γ : Ctx n} (h : Maybe (NodeState Γ)) → QEmpty h → RoomEmpty h
qempty-room (just (mergeAll-st _ _ _ _)) e = λ _ → e
qempty-room (just (cell-st _))           _ = tt
qempty-room (just (take-st _))           _ = tt
qempty-room (just (batchSync-st _ _ _))  _ = tt
qempty-room (just (switch-st _ _))       _ = tt
qempty-room (just (exhaust-st _ _))      _ = tt
qempty-room nothing                      _ = tt

-- the wrap moves only the flag
room-wrap : ∀ {n} {Γ : Ctx n} (op : AllOp) (fin : Bool) (h : Maybe (NodeState Γ))
          → RoomEmpty h → RoomEmpty (wrapNode op fin h)
room-wrap op        false h                              g = g
room-wrap mergeAllᵒ true  (just (mergeAll-st _ _ _ _))   g = g
room-wrap mergeAllᵒ true  (just (cell-st _))             g = g
room-wrap mergeAllᵒ true  (just (take-st _))             g = g
room-wrap mergeAllᵒ true  (just (batchSync-st _ _ _))    g = g
room-wrap mergeAllᵒ true  (just (switch-st _ _))         g = g
room-wrap mergeAllᵒ true  (just (exhaust-st _ _))        g = g
room-wrap mergeAllᵒ true  nothing                        g = g
room-wrap switchᵒ   true  (just (mergeAll-st _ _ _ _))   g = g
room-wrap switchᵒ   true  (just (cell-st _))             g = g
room-wrap switchᵒ   true  (just (take-st _))             g = g
room-wrap switchᵒ   true  (just (batchSync-st _ _ _))    g = g
room-wrap switchᵒ   true  (just (switch-st _ _))         g = tt
room-wrap switchᵒ   true  (just (exhaust-st _ _))        g = g
room-wrap switchᵒ   true  nothing                        g = g
room-wrap exhaustᵒ  true  (just (mergeAll-st _ _ _ _))   g = g
room-wrap exhaustᵒ  true  (just (cell-st _))             g = g
room-wrap exhaustᵒ  true  (just (take-st _))             g = g
room-wrap exhaustᵒ  true  (just (batchSync-st _ _ _))    g = g
room-wrap exhaustᵒ  true  (just (switch-st _ _))         g = g
room-wrap exhaustᵒ  true  (just (exhaust-st _ _))        g = tt
room-wrap exhaustᵒ  true  nothing                        g = g

-- THE OUTER'S STEP: walk the observables that arrived, subscribing
-- each under a fresh inner frame, then wrap the end at the node.
thruStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
           (aM : Acc _<_ m) → SubStep {e = e} (thru-outer {u = u} op nid) RoomEmpty m

-- THE INNER FRAME'S STEP.  Values pass; an end passes while a chain
-- under this instance is still registered; otherwise the finish runs
-- at the node, and the merge's drain there has nothing to subscribe.
fiStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId)
       → SubStep {e = e} (from-inner {s = u} op allNid inst) QEmpty m

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

pass : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId) {S : Set} {lo ℓ}
       (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
       (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : Maybe (NodeState Γ))
       (now : Tick) (vals : List (Val Γ u)) → All (Red m u) vals → (fin : Bool)
     → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
     → PreHolds m (from-inner {s = u} op allNid inst ↠[ le ] κ) (standing (h , pfs)) sched st
     → innerReact⇓ {e = e} op allNid inst κ now vals sched st fin ([] , vals , false , sched , st)
     → Stage m (from-inner op allNid inst) le κ
         (λ o sc s′ → foldPath⇓ {e = e} now (from-inner op allNid inst ↠[ le ] κ) vals fin sched st (o , sc , s′))
         (standing pfs) rp s₀ sched st
pass op allNid inst le κ pfs rp s₀ h now vals col fin rm hs d =
  stage-map (λ d′ → fold-step (step-from-inner d) d′)
    (callStage (from-inner op allNid inst) le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs)

-- the finish, once no chain under the instance is registered
fiDead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId) {S : Set} {lo ℓ}
         (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
         (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S) (h : Maybe (NodeState Γ)) → QEmpty h
       → (now : Tick) (vals : List (Val Γ u)) → All (Red m u) vals
       → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
       → PreHolds m (from-inner {s = u} op allNid inst ↠[ le ] κ) (standing (h , pfs)) sched st
       → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
       → Σ (Stage m (from-inner op allNid inst) le κ
             (λ o sc s′ → foldPath⇓ {e = e} now (from-inner op allNid inst ↠[ le ] κ) vals true sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
           (λ r → QEmpty (Stage.hd r))
fiDead {Γ = Γ} {e = e} {u = u} op allNid inst le κ pfs rp s₀ h g now vals col {sched} {st} rm hs@(grounded ((c , lts) , ap , hsκ) _) eqa
  with finishUsable op u inst h in equ
... | false = stage-map (λ d′ → fold-step (step-from-inner (react-dead eqa (finish-nil (trans (cong (finishUsable op u inst) c) equ)))) d′)
                (callStage (from-inner op allNid inst) le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs)
            , g
... | true with finishing op u inst h equ
...   | f-switch c′ od eqc =
        let w  = writeStage (from-inner op allNid inst) le κ (standing pfs) rp s₀ allNid (switch-st nothing od)
                   (λ k ne → head-off allNid (inst ∷ []) k ne) (just (switch-st nothing od)) (lookup-set allNid (switch-st nothing od) (EvalSt.nodes st)) h hs
            cs = callStage (from-inner op allNid inst) le κ (just (switch-st nothing od)) (standing pfs) rp s₀ now vals
                   (ofColumn κ (standing pfs) col) od rm (Stage.hl w)
        in stage-map (λ d′ → fold-step (step-from-inner (deadBy eqa c (finish-switch-clear eqc))) d′)
             (stage-seq w cs (λ d → d))
           , tt
...   | f-exhaust act od =
        let w  = writeStage (from-inner op allNid inst) le κ (standing pfs) rp s₀ allNid (exhaust-st false od)
                   (λ k ne → head-off allNid (inst ∷ []) k ne) (just (exhaust-st false od)) (lookup-set allNid (exhaust-st false od) (EvalSt.nodes st)) h hs
            cs = callStage (from-inner op allNid inst) le κ (just (exhaust-st false od)) (standing pfs) rp s₀ now vals
                   (ofColumn κ (standing pfs) col) od rm (Stage.hl w)
        in stage-map (λ d′ → fold-step (step-from-inner (deadBy eqa c finish-exhaust-clear)) d′)
             (stage-seq w cs (λ d → d))
           , tt
...   | f-merge lim act q od with g
...     | refl =
        let fi = from-inner {s = u} op allNid inst
            s₁ = callStage fi le κ h (standing pfs) rp s₀ now vals (ofColumn κ (standing pfs) col) false rm hs
            s₂ : Stage _ fi le κ
                   (λ o sc s′ → Σ ℕ (λ act′ → Σ (List (Val Γ (obs u))) (λ q′ →
                      mergeAllDrain⇓ {e = e} allNid κ now [] lim (pred act) od [] (Stage.sc s₁) (Stage.st′ s₁)
                        (o , act′ , q′ , sc , s′))))
                   (endPre (Stage.tr s₁)) (endRP (Stage.tr s₁)) (endS (Stage.tr s₁)) (Stage.sc s₁) (Stage.st′ s₁)
            s₂ = stage-nil fi le κ (endPre (Stage.tr s₁)) (endRP (Stage.tr s₁)) (endS (Stage.tr s₁)) []
                   (pred act , [] , drain-spent) (Stage.hd s₁) (Stage.hl s₁)
            s₁₂ : Stage _ fi le κ
                    (λ o sc s′ → Σ ℕ (λ act′ → Σ (List (Val Γ (obs u))) (λ q′ →
                       innerFinish⇓ {e = e} mergeAllᵒ allNid inst κ now vals sched st (just (mergeAll-st lim act q od))
                         (o , [] , null q ∧ od ∧ (act′ ≡ᵇ 0) , sc
                         , record s′ { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes s′) }))))
                    (standing pfs) rp s₀ sched st
            s₁₂ = stage-seq s₁ s₂ (λ { (act′ , q′ , d₂) → act′ , q′ , finish-all-drain {act = act} (Stage.dv s₁) d₂ })
            act′ = proj₁ (Stage.dv s₁₂)
            q′   = proj₁ (proj₂ (Stage.dv s₁₂))
            dfin = proj₂ (proj₂ (Stage.dv s₁₂))
            fin′ = null q ∧ od ∧ (act′ ≡ᵇ 0)
            w  = writeStage fi le κ (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂)) allNid
                   (mergeAll-st lim act′ q′ od) (λ k ne → head-off allNid (inst ∷ []) k ne)
                   (just (mergeAll-st lim act′ q′ od)) (lookup-set allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes (Stage.st′ s₁₂))) (Stage.hd s₁₂) (Stage.hl s₁₂)
            cs = callStage fi le κ (just (mergeAll-st lim act′ q′ od)) (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂))
                   now [] (ofColumn κ _ []ᵃ) fin′ (room-keeps (innerFinish-keeps dfin) rm) (Stage.hl w)
            cs-hd = callStage-hd fi le κ (just (mergeAll-st lim act′ q′ od)) (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂))
                      (endS (Stage.tr s₁₂)) now [] (ofColumn κ _ []ᵃ) fin′ (room-keeps (innerFinish-keeps dfin) rm) (Stage.hl w)
            s₃ : Stage _ fi le κ
                   (λ o sc s′ → foldPath⇓ {e = e} now κ [] fin′ (Stage.sc s₁₂)
                                  (record (Stage.st′ s₁₂) { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes (Stage.st′ s₁₂)) })
                                  (o , sc , s′))
                   (endPre (Stage.tr s₁₂)) (endRP (Stage.tr s₁₂)) (endS (Stage.tr s₁₂)) (Stage.sc s₁₂) (Stage.st′ s₁₂)
            s₃ = stage-seq w cs (λ d → d)
        in stage-seq s₁₂ s₃ (λ d₃ → fold-step (step-from-inner (deadBy eqa c dfin)) d₃)
           , subst QEmpty (sym cs-hd) refl

fiStep op allNid inst le κ pfs rp s₀ h g now vals col false sched st rm hs =
  pass op allNid inst le κ pfs rp s₀ h now vals col false rm hs react-false , g
fiStep op allNid inst le κ pfs rp s₀ h g now vals col true sched st rm hs
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in eqa
... | true  = pass op allNid inst le κ pfs rp s₀ h now vals col true rm hs (react-alive eqa) , g
... | false = fiDead op allNid inst le κ pfs rp s₀ h g now vals col rm hs eqa

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
red-all op ns gns b ρ rρ k ok aK aB aM κ (standing pfs) rp s₀ now sched st rm hs
  with redExpAcc b ρ rρ k ok aK aB aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) (standing (just ns , pfs))
         (subRP ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) ns st) rm
         (fresh-holds (thru-outer op (nodeCt sched)) κ pfs (just ns) ns (λ _ → node-eq)
            (lookup-set (nodeCt sched) ns (EvalSt.nodes st)) (≤-refl ∷ᵃ []ᵃ) hs)
... | (r , d , tr , hl , kp)
  with translate-sub-end ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
...   | (h″ , _ , eq) =
      let tr′ = translate-sub ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
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
red-all {n = n} op ns gns b ρ rρ k ok aK aB aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k ok aK aB aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) ns st) rm (grounded (ground fell) (fresh-sound (thru-outer op (nodeCt sched)) κ ns (λ _ → node-eq) (sounds fell)))
... | (r , d , tr , hl , kp) =
      r , sub-all refl d , []ᵗ
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
