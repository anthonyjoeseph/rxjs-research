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
open import Data.List using (List; []; _∷_; map; _++_; null)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; suc; pred; _≤_; _<_; _∸_; s≤s; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<; n≤1+n; <-≤-trans; <⇒≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Prim using (Tick; ObservableInput)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; isData; unfoldμ; varᵗ; unit̂;
  bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; FnClo; applyClo; _≟ᵗ_)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; PreservedBelow; pres; below; pres-write; lookup-set; set-above; <→≢ᵇ)
open import Decide using (∧ˡ; ∧ʳ; ≡ᵇ→≡; ≡ᵇ-refl)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f;
  batchSync-f; from-inner; thru-outer; NodeState; lookupNode; frameNodes; pathHasNode;
  register; installNode; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; mergeAllᵒ;
  AllOp; switchᵒ; exhaustᵒ; NodeId; cell-st; take-st; switch-st; exhaust-st; batchSync-st;
  setNode; hasRoom; consumeUsable; finishUsable; thruWrap; switchKill; aliveThroughᶠ)
open import Rx.Evaluator.Unconn-Arith using (unconn; unconn-insert; fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps; Keeps; switchKill-keeps; thruWrap-keeps; thruWalk-keeps;
  thruConsume-keeps; innerFinish-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; mergeAllDrain⇓; subs-of; subs-empty; subs-mint; subs-defer; subs-floor; subs-μ; subs-map;
  subs-shared; slot-spent; slot-join; slot-connect; connect; foldPath⇓; fold-root; fold-step;
  stepFrame⇓; step-map; injectRoot; inner; thruConsume⇓; consume-all-sub; consume-all-enqueue;
  consume-all-nil; consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil; thruWalk⇓; walk-nil; walk-cons; drain-spent; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil; innerReact⇓;
  react-false; react-alive; react-dead; step-from-inner; step-thru-outer; subscribeAll⇓;
  sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all)

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
-- vouch for.  AND A STANDING PATH ENDS AT THE ROOT.  A share's sink
-- is reached two ways only -- by the connect, which subscribes the
-- definition under it with the room fallen, and by the fan-out, which
-- folds the registered rows raw from the store -- so no continuation
-- built over candidates ever ends there, and saying so by type is
-- what lets a standing fold's writes be accounted for by the path
-- alone: past a sink the path would not know what it wrote.
PreFs : ∀ {n} {Γ : Ctx n} {lo u t} → Path Γ lo u t → Set
PreFs root             = ⊤
PreFs (share-sink _ _) = ⊥
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
-- fact about the path alone, since a standing path ends at the root.
Apart : ∀ {n} {Γ : Ctx n} {lo u t s} (κ : Path Γ lo u t) (f : Frame Γ s u) → Set
Apart κ f = ∀ k → T (any (_≡ᵇ k) (frameNodes f)) → T (pathHasNode k κ) → ⊥

HoldsFs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
          (κ : Path Γ lo u t) → PreFs κ → Sched Γ → EvalSt e → Set
HoldsFs root             _         sched st = ⊤
HoldsFs (share-sink _ _) ()        sched st
HoldsFs (f ↠[ _ ] κ)     (h , pfs) sched st =
  HoldsF f h sched st × Apart κ f × HoldsFs κ pfs sched st

PreHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
           (m : ℕ) (κ : Path Γ lo u t) → Pre κ → Sched Γ → EvalSt e → Set
PreHolds m κ (standing pfs) sched st = HoldsFs κ pfs sched st
PreHolds m κ fallen         sched st = Fell m sched st

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
holdsFs-step (share-sink _ _) ()        mv ct h
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
           → PreHolds m κ pre sched st → PreHolds m κ pre sched′ st′
holds-step κ (standing pfs) mv ct fl h = holdsFs-step κ pfs mv ct h
holds-step κ fallen         mv ct fl h = fl h

-- WHAT A FOLD KEEPS FOR THE FRAME BENEATH IT.  A frame that hands a
-- burst up the path and gets the path's successor back has its own
-- node between the two, and the path above has no business with it: a
-- standing answer says the counter did not fall, and that every node
-- below it that is none of the path's own reads back as it did, so
-- the frame beneath stands on its own in the state handed back.  A
-- fallen answer keeps nothing, because nothing beneath a fallen path
-- holds candidates to keep.
--
-- IT IS A FACT ABOUT THE PATH ALONE BECAUSE A CONNECT FALLS.  The one
-- fold that writes below the counter at nodes not its own is a share's
-- fan-out, and a fan-out happens only inside a connect, whose answer
-- is fallen the whole way up; a fold that answers standing has
-- connected nothing, so what it wrote is its frames' nodes and nodes
-- it minted.
Kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
       (κ : Path Γ lo u t) → Pre κ → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Kept κ (standing _) sched st sched′ st′ =
  nodeCt sched ≤ nodeCt sched′
  × (∀ k → k < nodeCt sched → (T (pathHasNode k κ) → ⊥)
       → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st))
Kept κ fallen sched st sched′ st′ = ⊤

-- a step that writes only at or above the counter and advances it
-- keeps everything
kept-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
            (κ : Path Γ lo u t) (pre : Pre κ) {sched sched′ : Sched Γ} {st st′ : EvalSt e}
          → PreservedBelow (nodeCt sched) st st′ → nodeCt sched ≤ nodeCt sched′
          → Kept κ pre sched st sched′ st′
kept-step κ (standing _) pr ct = ct , λ k k< _ → below pr k k<
kept-step κ fallen       pr ct = tt

-- and what was kept from a counter is kept from an equal one
kept-in : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo u}
          (κ : Path Γ lo u t) (pre : Pre κ) {sched sched₁ sched′ : Sched Γ} {st st′ : EvalSt e}
        → nodeCt sched₁ ≡ nodeCt sched
        → Kept κ pre sched₁ st sched′ st′ → Kept κ pre sched st sched′ st′
kept-in κ (standing _) eq (ct , kp) = subst (_≤ _) eq ct , λ k k< → kp k (subst (k <_) (sym eq) k<)
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
          → HoldsF f h sched₁ st₁ → Apart κ f
          → (p : Pre κ) → PreHolds m κ p sched₂ st₂ → Kept κ p sched₁ st₁ sched₂ st₂
          → PreHolds m (f ↠[ le ] κ) (headPre h p) sched₂ st₂
headHolds f le κ h (c , fr) ap (standing pfs) hs (ct , kp) =
    ( consistentF-move f h (λ k on → kp k (nodes-below _ fr k on) (ap k on)) c
    , mapᵃ (λ lt → <-≤-trans lt ct) fr )
  , ap
  , hs
headHolds f le κ h hf ap fallen fell kp = fell

-- what the frame keeps for the frame beneath it: what the path kept,
-- through its own step
headKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u}
           (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t)
           {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
         → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
                → lookupNode k (EvalSt.nodes st₁) ≡ lookupNode k (EvalSt.nodes st))
         → nodeCt sched₁ ≡ nodeCt sched
         → (p : Pre κ) → Kept κ p sched₁ st₁ sched₂ st₂ → (h : HeldF f)
         → Kept (f ↠[ le ] κ) (headPre h p) sched st sched₂ st₂
headKept f le κ off ct (standing pfs) (ct₂ , kp) h =
    subst (_≤ _) ct ct₂
  , λ k k< ne → trans (kp k (subst (k <_) (sym ct) k<) (λ on → ne (∨-Tʳ on)))
                      (off k (λ on → ne (∨-Tˡ on)))
headKept f le κ off ct fallen kp h = tt

-- THE ARM READS THE PATH'S GROUND BACK OUT OF THE FRAME'S, which is
-- where a frame arm's answer comes from once its source has answered
-- about the path with the frame pushed.
unheadHolds : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f)
              (p : Pre κ) {sched : Sched Γ} {st : EvalSt e}
            → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st → PreHolds m κ p sched st
unheadHolds f le κ h (standing pfs) (_ , _ , hs) = hs
unheadHolds f le κ h fallen         fell         = fell

-- and what the frame kept for the arm's caller, given that the arm's
-- own install sat at or above the counter it began at and wrote
-- nothing below it
unheadKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo ℓ s u}
             (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (h : HeldF f) (p : Pre κ)
             {sched sched₁ sched₂ : Sched Γ} {st st₁ st₂ : EvalSt e}
           → (∀ k → k < nodeCt sched → T (any (_≡ᵇ k) (frameNodes f)) → ⊥)
           → nodeCt sched ≤ nodeCt sched₁
           → (∀ k → k < nodeCt sched → lookupNode k (EvalSt.nodes st₁) ≡ lookupNode k (EvalSt.nodes st))
           → Kept (f ↠[ le ] κ) (headPre h p) sched₁ st₁ sched₂ st₂
           → Kept κ p sched st sched₂ st₂
unheadKept f le κ h (standing pfs) above ct pr (ct₂ , kp) =
    ≤-trans ct ct₂
  , λ k k< ne → trans (kp k (<-≤-trans k< ct) (λ on → [ above k k< , ne ] (∨-T on))) (pr k k<)
unheadKept f le κ h fallen above ct pr kp = tt

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
headCall fs h rh κ pfs (call now vals col fin sched st rm ((c , fr) , ap , hs)) =
  let r = step fs h vals fin sched st
  in call now (outs r) (ofColumn κ (standing pfs) (proj₁ (step-red fs col rh))) (fin″ r) (sched″ r) (st″ r)
       (room-keeps (stepFrame-keeps (step-⇓ fs {κ = κ} {now = now} h vals fin sched st c)) rm)
       (holdsFs-step κ pfs
         (λ k on k< → step-off fs h vals fin sched st k (λ onF → ap k onF on))
         (subst (nodeCt sched ≤_) (sym (step-ct fs h vals fin sched st)) ≤-refl) hs)

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
  ; step-ct   = λ _ _ _ _ _ → refl }

------------------------------------------------------------------
-- THE FRAME CONTINUATION THAT REACHES NO CYCLE.
------------------------------------------------------------------

-- THE ROOT MINTS THE BURST FROM NOTHING, and its state is the unit.
rootRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo} {P : Val Γ t → Set₁} {pre : Pre {Γ = Γ} (root {lo = lo} {t = t})}
       → RP {e = e} m {lo = lo} P ⊤ root pre
fold (rootRP {pre = pre}) tt now vals _ fin sched st rm h =
  ans _ sched st fold-root pre h (kept-step root pre (pres (λ _ _ → refl)) ≤-refl) rootRP tt

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
path-below (share-sink _ _) ()
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
kept-refl κ (standing _) = ≤-refl , λ _ _ _ → refl
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
kept-trans κ pfs (standing _) (ct₁ , k₁) (ct₂ , k₂) =
  ≤-trans ct₁ ct₂ , λ k k< ne → trans (k₂ k (<-≤-trans k< ct₁) ne) (k₁ k k< ne)
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
           → Kept (f ↠[ le₁ ] κ) (headPre h₁ p) sched₁ st₁ sched₂ st₂
           → Kept (g ↠[ le₂ ] κ) (headPre h₂ p) sched st sched₂ st₂
kept-shift f g le₁ le₂ κ h₁ h₂ (standing pfs) ct under off (ct₂ , kp) =
    ≤-trans ct ct₂
  , λ k k< ne → trans (kp k (<-≤-trans k< ct)
                          (λ on → [ under k k< (λ b → ne (∨-Tˡ b)) , (λ c → ne (∨-Tʳ c)) ] (∨-T on)))
                      (off k k< (λ b → ne (∨-Tˡ b)))
kept-shift f g le₁ le₂ κ h₁ h₂ fallen ct under off kp = tt

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
            → Keeps {e = e} sched st sc st′ → Fell m sched st → (h : HeldF f)
            → Stage m f le κ D fallen rp s₀ sched st
fallenStage f le κ rp s₀ out sc st′ d ks fell h =
  stage out sc st′ d []ᵗ refl h (fell-keeps ks fell) tt

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
             → Stage m f le κ D q rp s₀ sched st → Stage m f le κ D q rp s₀ sched₀ st₀
stage-rebase f le κ ct off (stage out sc st′ d tr e h hl kp) =
  stage out sc st′ d tr e h hl (kept-shift f f le le κ h h (endPre tr) ct (λ _ _ ne → ne) off kp)

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
callStage f le κ h (standing pfs) rp s₀ now vals col fin {sched} {st} rm (hf , ap , hs) =
  let c  = call now vals col fin sched st rm hs
      an = apply rp s₀ c
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) (c ∷ᵗ []ᵗ) refl h
       (headHolds f le κ h hf ap (Ans.pre′ an) (Ans.holds′ an) (kept an))
       (headKept f le κ (λ _ _ → refl) refl (Ans.pre′ an) (kept an) h)
callStage f le κ h fallen rp s₀ now vals col fin {sched} {st} rm fell =
  let an = fold rp s₀ now vals col fin sched st rm fell
  in stage (out an) (Ans.sched′ an) (Ans.st′ an) (der an) []ᵗ refl h
       (fell-keeps (foldPath-keeps (der an)) fell) tt

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
  writeHolds f le κ (standing pfs) nid ns ownOff h′ {sched} {st} con h ((_ , fr) , ap , hs) =
    (con , fr) , ap
    , holdsFs-step κ pfs (λ k on _ → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ap k onF on))) ≤-refl hs
  writeHolds f le κ fallen nid ns ownOff h′ con h fell = fell
  writeKept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m} {lo ℓ s u}
              (f : Frame Γ s u) (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (p : Pre κ)
              (nid : NodeId) (ns : NodeState Γ)
            → (∀ k → (T (any (_≡ᵇ k) (frameNodes f)) → ⊥) → (nid ≡ᵇ k) ≡ false)
            → (h′ : HeldF f) {sched : Sched Γ} {st : EvalSt e}
            → (h : HeldF f) → PreHolds m (f ↠[ le ] κ) (headPre h p) sched st
            → Kept (f ↠[ le ] κ) (headPre h′ p) sched st sched (record st { nodes = setNode nid ns (EvalSt.nodes st) })
  writeKept f le κ (standing pfs) nid ns ownOff h′ {sched} {st} h (_ , ap , _) =
    ≤-refl , λ k _ ne → set-above nid k ns (EvalSt.nodes st) (ownOff k (λ onF → ne (∨-Tˡ onF)))
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
  → HoldsFs (f ↠[ le ] κ) (h , pfs) sched st
  → Σ (Stage m f le κ (λ o sc s′ → foldPath⇓ {e = e} now (f ↠[ le ] κ) vals fin sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
      (λ r → G (Stage.hd r))

------------------------------------------------------------------
-- THE ARMS, STATED.
------------------------------------------------------------------

-- THE STATEMENT EVERY ARM MAKES: the candidate for one closure over a
-- reducible environment, funded by three accessibilities.  The room's
-- is outermost and only a share's connect peels it; under it the input
-- bound and the term size fall at every former.
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
postulate
  red-take : ∀ {n} {Γ : Ctx n} {Θ t} (c : Tm Γ [] [] Θ natᵗ)
               (b : Exp Γ [] [] Θ t) → Arm (takeᵉ c b)

-- THE BATCHSYNC ARM, WHICH IS THE ONE THE TRACE EXISTS FOR.  The
-- bracket is opened by the install and closed when the subscribe call
-- returns; the arm lowers the bit and folds its frame's successor once
-- more with nothing arriving, and that successor is the replay of the
-- continuation it built over the trace its source answered with.
postulate
  red-batchSync : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) → Arm (batchSyncᵉ b)

-- THE SCAN ARM.  Its frame holds the accumulator and its candidate;
-- the translation folds the step's candidate along the column.
postulate
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

-- THE SCRIPTED SLOT.  Folds what the slot script says through the
-- continuation with `red-val` beside every value; the live hot slot
-- registers and folds nothing; the cold slot with a tail registers
-- FIRST and then folds its prefix, since a synchronous value can cut
-- this very chain and a cut severs registrations.
postulate
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

-- THE RAW FOLD OF A PATH THE STORE HOLDS.  An arrival and a share's
-- fan-out fold down registry paths no subscribe built, so the frames'
-- held candidates are rebuilt by `red-val` on what the store holds,
-- funded by the room the connect peeled and by the floor: a chain
-- registered on a share sinks STRICTLY above that share, so past a
-- sink the rows fan out at a higher floor.  It is a fold and not a
-- continuation because it holds nothing between calls -- its
-- successor would be itself -- and because the arrival spine and the
-- fallen continuation are its only callers, each of which applies it
-- once.

-- It is also the only place a merge's queue is nonempty at an inner's
-- finish: on standing ground the column guards keep it empty, but a
-- share's fan-out reaches the outer while the lane is busy, and a raw
-- finish meets what it queued.  The unwritten route drains that queue
-- on a budget no caller supplies: the raw finish seeds it at the
-- queue's own length, each drained inner is subscribed under a frame
-- budgeted at the strictly smaller remaining length, built first-order
-- before it is handed over, and a budgeted finish meeting a queue past
-- its budget peels the room.  Each frame kind is its own builder, so
-- none is handed to a candidate at its own ceiling and budget.

-- The budget is overrun only if a queue grows while one of its own
-- drained inners runs, and that takes a connect inside the inner, which
-- spends the room the peel needs.  Only a share's fan-out delivers to an
-- outer mid-fold; a row that feeds a share sits on a lower one, while the
-- inner's own path sinks only above its outer's floor, so nothing the
-- inner emits reaches the share its outer is registered on, and the only
-- other way to make that share emit is a connect below it.  So the
-- over-budget finish is always funded, by room then budget.  Read off the
-- path and row types, not machine-checked.  Measured on the sweep-era
-- evaluator over 1.5M programs: 44,160 raw finishes met a nonempty queue,
-- and every one of the 324,536 budgeted finishes met a queue exactly at
-- its budget; none overran it, and no walk-order finish met a queue.

-- THE BODY NEEDS A GROUND NEITHER CONSTRUCTOR OF `Pre` GIVES.  Both
-- callers hand it the room exactly at the ceiling -- the fallen fold
-- because its peel lands there, the arrival spine because it seeds there
-- -- so an inner it subscribes can stand neither on `fallen`, which is
-- the room below the ceiling, nor on `standing`, whose path ends at the
-- root where this one may end at a sink.  What the inner's arms need is
-- a ground whose pushed frames step LIVE over a raw base: the base is the
-- inner's exit frame, folding the rest of the path raw and descending on
-- the path, while the frames stacked above it hold their candidates, so
-- no arm's extension re-enters the raw fold.

-- THAT GROUND OWES WHAT STANDING GROUND GETS FREE FROM THE ROOT: the
-- base's fold, connecting nothing, writes no node of a frame stacked
-- above it.  The invariant carrying it is ONE TERMINUS PER NODE: every
-- registry row through a frame's node ends where that frame's own path
-- ends, at the root or at one sink.  A flattener's frames sit only on
-- its outer's path and its inners', which share its continuation, and a
-- row registered under an inner is that inner's continuation with its
-- floor lowered, so no row leaves the terminus it was made under.  A
-- base ending at the root reaches no sink without a connect.  A base
-- ending at `j`'s sink reaches only rows on shares from `j` up, and a
-- row on a share sits above that share's index, so it never ends at
-- `j`'s sink, which is the one place a stacked frame's rows end.  The
-- state records no terminus, so the record field is owed with the
-- ground.

-- The invariant held on a swept corpus of 1.5M programs, run on the
-- side branch's evaluator over this relation: at every frame step whose
-- continuation fanned out or connected (4.4M fan-out, 107k connect), the
-- frame's nodes came through the rest of the fold unchanged in shape and
-- value, and every registry row through them ended at the frame's own
-- terminus.  The same check fed the pre-step state at take's frame
-- flagged 1.4k writes on 20k programs, so it can fire.  Steps with
-- neither a fan-out nor a connect were not checked, and 63 deep
-- recursive programs timed out uncovered.

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
-- RECOVERY: git show 43c34675:agda/src/Rx/Evaluator/Reducible.agda
--   restores `drain` and `drainSub`, the live drain the route rebuilds.
postulate
  rawFold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
            (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
          → (κ : Path Γ ℓ u t) (now : Tick) (vals : List (Val Γ u)) (fin : Bool)
            (sched : Sched Γ) (st : EvalSt e) → Room m sched st
          → Σ (Stream Γ t × Sched Γ × EvalSt e) (foldPath⇓ {e = e} now κ vals fin sched st)

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
fold (fallenRP ac le (acc rsM) κ) tt now vals _ fin sched st rm fell =
  let (r , d) = rawFold ac le (rsM fell) κ now vals fin sched st ≤-refl
  in ans (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) d fallen
         (fell-keeps (foldPath-keeps d) fell) tt (fallenRP ac le (acc rsM) κ) tt

-- THE LIVE FOLD OVER A PURE FRAME.  It steps at what it holds, folds
-- the path above at the step's state with the candidates through the
-- step, and hands back its successor at what it now holds -- standing
-- where the path still stands, fallen where the path fell.  It needs
-- the room's accessibility for the fall alone, since the fallen fold
-- is funded by it.
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
redExpAcc (deferᵉ body) ρ {m} rρ k ok aK a aM {lo = lo} κ pre rp s₀ now sched st rm h =
  let nid = freshId nodeᵏ (Sched.mint sched)
      st′ = register (freshId regᵏ (Sched.mint sched)) (atDyn (freshId sourceᵏ (Sched.mint sched)) lo)
                     (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ)
                     (installNode nid (mergeAll-st nothing 0 [] false) st)
  in _ , subs-defer refl refl refl refl , []ᵗ
     , holds-step {m = m} κ pre (λ k′ _ k< → below (pres-write st st′ _ refl ≤-refl) k′ k<) (n≤1+n _)
         (λ (x : Fell m sched st) → x) h
     , kept-step κ pre (pres-write st st′ _ refl ≤-refl) (n≤1+n _)
redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h
  with (let src = freshId sourceᵏ (Sched.mint sched)
        in redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) aM κ pre rp s₀ now
             (record sched
                { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
             st rm (holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x) h))
... | (r , d , tr , hl , kp) = r , subs-mint refl d , tr , hl , kept-in κ (endPre tr) refl kp

-- the live fold: step, fold above, stand on what came back
fold (liveRP le aM fs h rh κ pfs rp) s now vals col fin sched st rm hs =
  let r  = step fs h vals fin sched st
      an = apply rp s (headCall {le = le} fs h rh κ pfs (call now vals col fin sched st rm hs))
  in ans (out an) (Ans.sched′ an) (Ans.st′ an)
         (fold-step (step-⇓ fs h vals fin sched st (proj₁ (proj₁ hs))) (der an))
         (headPre (held r) (Ans.pre′ an))
         (headHolds _ le κ (held r)
           ( step-cons fs h vals fin sched st (proj₁ (proj₁ hs))
           , subst (λ ct → All (_< ct) _) (sym (step-ct fs h vals fin sched st)) (proj₂ (proj₁ hs)) )
           (proj₁ (proj₂ hs)) (Ans.pre′ an) (Ans.holds′ an) (kept an))
         (headKept _ le κ (step-off fs h vals fin sched st) (step-ct fs h vals fin sched st)
           (Ans.pre′ an) (kept an) (held r))
         (headNext le aM fs (held r) (proj₂ (step-red fs col rh)) κ (Ans.pre′ an) (next an))
         (Ans.s′ an)

headNext le aM fs h rh κ (standing pfs) rp = liveRP le aM fs h rh κ pfs rp
headNext {n = n} {lo = lo} le aM fs h rh κ fallen rp =
  dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ))

-- THE TRANSLATION OF A SOURCE'S TRACE THROUGH THE LIVE FRAME IT WAS
-- SUBSCRIBED UNDER: each call becomes the call the frame made above
-- it, and the walk stops where the path fell, since past the fall the
-- frame's fold reads the store and calls nothing it was handed.
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
-- down, with the frame holding candidates for what it holds there
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
         s₀ now sched st rm ((tt , []ᵃ) , (λ _ ()) , h)
... | (r , d , tr , hl , kp)
  with translate-end ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
...   | (h″ , _ , eq) =
      let tr′ = translate ≤-refl aM (mapStep (_ , f , ρ) (red-mapFn f b ρ rρ k ok aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))) aM)) tt tt κ pfs rp tr
      in r , subs-map d , tr′
       , unheadHolds (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′) (subst (λ p → PreHolds _ _ p _ _) eq hl)
       , unheadKept (map-f (_ , f , ρ)) ≤-refl κ h″ (endPre tr′) {sched} {sched} {st = st} {st₁ = st}
           (λ _ _ ()) ≤-refl (λ _ _ → refl) (subst (λ p → Kept _ p _ _ _ _) eq kp)
red-map {n = n} {s = s} f b ρ rρ k ok aK (acc rs) aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok) aK
         (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f)))) aM
         (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (map-f (_ , f , ρ) ↠[ ≤-refl ] κ))) s₀ now sched st rm fell
... | (r , d , tr , hl , kp) =
      r , subs-map d , []ᵗ
    , subst (λ p → PreHolds _ _ p _ _) (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl , tt

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
        , []ᵗ , holds-step κ pre (λ _ _ _ → refl) ≤-refl (λ x → x) h
        , kept-step κ pre (pres (λ _ _ → refl)) ≤-refl
...   | false
      with (let rid    = freshId regᵏ (Sched.mint sched)
                sched′ = record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                st′    = register rid (atSlot i) (lowerFloor below κ)
                           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
                fell′  = ≤-trans (unconn-insert (Sched.slots sched) (EvalSt.connectedShares st) i slEq connEq) rm
            in redExpAcc d []ᵉ tt (toℕ i) okd aI (<-wellFounded (gsizeᵉ d)) aM
                 (share-sink i ≤-refl) fallen
                 (dropS (fallenRP (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl)))
                 tt now sched′ st′ (<⇒≤ fell′) fell′)
...     | (r , dv , tr , hl , _) =
          r , subs-shared {κ = κ} {below = below} slEq
                (slot-connect {κ = κ} {below = below} doneEq connEq (connect {κ = κ} {below = below} refl dv))
          , fellᵗ (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM κ)) s
          , subst (λ p → PreHolds _ (share-sink i ≤-refl) p _ _)
              (fallen-stays (<-wellFounded (n ∸ toℕ i)) ≤-refl aM (share-sink i ≤-refl) tr) hl
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

------------------------------------------------------------------
-- THE FOLD OVER A SUBSCRIBING FRAME, AND THE FLATTENER ARMS.
------------------------------------------------------------------

-- THE FOLD IS THE STEP APPLIED ONCE, and its successor is the same
-- fold at what the step left the frame holding -- standing where the
-- step's trace left the path standing, fallen where it fell.
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
-- the walk stops where the path fell.
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
-- a column the guard still holds of
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
fiHolds→thru op nid inst le κ h (standing pfs) ((c , lt ∷ᵃ _) , ap , hs) =
  (c , lt ∷ᵃ []ᵃ) , (λ k on → ap k (∨-Tˡ {nid ≡ᵇ k} {any (_≡ᵇ k) (inst ∷ [])} ([ (λ a → a) , (λ ()) ] (∨-T {nid ≡ᵇ k} {false} on)))) , hs
fiHolds→thru op nid inst le κ h fallen fell = fell

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
            → Σ (Stage m (thru-outer op nid) le κ
                  (λ o′ sc s′ → subscribeE⇓ {e = e} o (from-inner op nid (nodeCt sched) ↠[ ≤-refl ] κ) now
                                  (bumpNode sched) (record st { nodes = setNode nid ns′ (EvalSt.nodes st) }) (o′ , sc , s′))
                  (standing pfs) rp s₀ sched st)
                (λ r → RoomEmpty (Stage.hd r))
subStanding {m = m} {u = u} op nid aM le κ pfs rp s₀ ns′ gq o ro now {sched} {st} rm hsκ lt ap =
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
                                  now (bumpNode sched) st″ rm hs′
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
          (subst (λ p → Kept κ′ p (bumpNode sched) st″ sc st′) eq kp))
     , qempty-room h″ g″

-- one inner subscribed on fallen ground: the store is read raw
consumeFallen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
                (aM : Acc _<_ m) {ℓ} (κ : Path Γ ℓ u t) (now : Tick)
                (o : Val Γ (obs u)) → Red m (obs u) o
                → {sched : Sched Γ} {st : EvalSt e} → Room m sched st → Fell m sched st
              → Σ (Stream Γ t × Sched Γ × EvalSt e) (thruConsume⇓ {e = e} op nid κ now o sched st)
consumeFallen {n = n} {u = u} op nid aM {ℓ} κ now o ro {sched} {st} rm fell
  with lookupNode nid (EvalSt.nodes st) in c
... | h with consumeUsable op u h in equ
...   | false = _ , consumeNil op (trans (cong (consumeUsable op u) c) equ)
...   | true with usable op u h equ
...     | u-switch cur od =
            let sk = switchKill cur sched st
                ks = switchKill-keeps cur sched st refl
                κ′ = from-inner {s = u} switchᵒ nid (nodeCt (proj₁ sk)) ↠[ ≤-refl ] κ
                (r , d , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                (bumpNode (proj₁ sk))
                                (record (proj₂ sk) { nodes = setNode nid (switch-st (just (nodeCt (proj₁ sk))) od) (EvalSt.nodes (proj₂ sk)) })
                                (room-keeps ks rm) (fell-keeps ks fell)
            in _ , consume-switch-sub c refl refl (inner refl d)
...     | u-exhaust od =
            let κ′ = from-inner {s = u} exhaustᵒ nid (nodeCt sched) ↠[ ≤-refl ] κ
                (r , d , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                (bumpNode sched) (record st { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) })
                                rm fell
            in _ , consume-exhaust-sub c (inner refl d)

-- one observable consumed by the walk, on standing ground
...     | u-merge lim act q od with hasRoom lim act in eqr
...       | false = _ , consume-all-enqueue c eqr
...       | true  =
            let κ′ = from-inner {s = u} mergeAllᵒ nid (nodeCt sched) ↠[ ≤-refl ] κ
                (r , d , _) = ro κ′ fallen (dropS (fallenRP (<-wellFounded (n ∸ ℓ)) ≤-refl aM κ′)) tt now
                                (bumpNode sched) (record st { nodes = setNode nid (mergeAll-st lim (suc act) q od) (EvalSt.nodes st) })
                                rm fell
            in _ , consume-all-sub c eqr (inner refl d)
consumeStanding : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (nid : NodeId)
                  (aM : Acc _<_ m) {S : Set} {lo ℓ}
                  (le : lo ≤ ℓ) (κ : Path Γ ℓ u t) (now : Tick) (pfs : PreFs κ)
                  (rp : RP {e = e} m (Red m u) S κ (standing pfs)) (s₀ : S)
                  (h : Maybe (NodeState Γ)) → RoomEmpty h → (o : Val Γ (obs u)) → Red m (obs u) o
                → {sched : Sched Γ} {st : EvalSt e} → Room m sched st
                → HoldsFs (thru-outer {u = u} op nid ↠[ le ] κ) (h , pfs) sched st
                → Σ (Stage m (thru-outer op nid) le κ
                      (λ o′ sc s′ → thruConsume⇓ {e = e} op nid κ now o sched st (o′ , sc , s′))
                      (standing pfs) rp s₀ sched st)
                    (λ r → RoomEmpty (Stage.hd r))
consumeStanding {u = u} op nid aM le κ now pfs rp s₀ h g o ro {sched} {st} rm hs@((c , lt ∷ᵃ []ᵃ) , ap , hsκ)
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
        in stage-map (λ d → consume-switch-sub c refl refl (inner refl d))
             (stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl) (λ k _ _ → cong (lookupNode k) ndE) sb)
           , gsb
...   | u-exhaust od =
        let (sb , gsb) = subStanding exhaustᵒ nid aM le κ pfs rp s₀ (exhaust-st true od) tt o ro now rm hsκ lt ap
        in stage-map (λ d → consume-exhaust-sub c (inner refl d)) sb , gsb
...   | u-merge lim act q od with hasRoom lim act in eqr
...     | false = stage-map (λ { (refl , refl , refl) → consume-all-enqueue c eqr })
                    (writeStage _ le κ (standing pfs) rp s₀ nid (mergeAll-st lim act (q ++ o ∷ []) od)
                       (λ k ne → head-off nid [] k ne) (just (mergeAll-st lim act (q ++ o ∷ []) od))
                       (lookup-set nid (mergeAll-st lim act (q ++ o ∷ []) od) (EvalSt.nodes st)) h hs)
                , (λ tr → ⊥-elim (subst T eqr tr))
...     | true  =
        let (sb , gsb) = subStanding mergeAllᵒ nid aM le κ pfs rp s₀ (mergeAll-st lim (suc act) q od)
                           (g tt₀) o ro now rm hsκ lt ap
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
consume op nid aM le κ now fallen rp s₀ h g o ro rm fell =
  let (r , d) = consumeFallen op nid aM κ now o ro rm fell
  in fallenStage _ le κ rp s₀ (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) d (thruConsume-keeps d) fell h , g

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
thruTail op nid le κ now fin (standing pfs) rp s₀ h g {sched} {st} rm ((c , lt ∷ᵃ []ᵃ) , ap , hs) =
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
             (room-keeps (thruWrap-keeps op nid fin sched st) rm) hs₂
  in stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl)
       (λ k _ ne → Wrapped.off wf k (head-off nid [] k ne)) cs
     , room-wrap op fin h g
thruTail op nid le κ now fin fallen rp s₀ h g {sched} {st} rm fell =
  let wf  = wrap-facts op nid fin sched st
      W   = thruWrap op nid fin (sched , st)
      ctE = cong nodeCt (Wrapped.sch wf)
      cs  = callStage (thru-outer op nid) le κ (wrapNode op fin h) fallen rp s₀ now [] (ofColumn κ fallen []ᵃ) (proj₁ W)
              (room-keeps (thruWrap-keeps op nid fin sched st) rm) (fell-keeps (thruWrap-keeps op nid fin sched st) fell)
  in stage-rebase (thru-outer op nid) le κ (subst (nodeCt sched ≤_) (sym ctE) ≤-refl)
       (λ k _ ne → Wrapped.off wf k (head-off nid [] k ne)) cs
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
     → HoldsFs (from-inner {s = u} op allNid inst ↠[ le ] κ) (h , pfs) sched st
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
       → HoldsFs (from-inner {s = u} op allNid inst ↠[ le ] κ) (h , pfs) sched st
       → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
       → Σ (Stage m (from-inner op allNid inst) le κ
             (λ o sc s′ → foldPath⇓ {e = e} now (from-inner op allNid inst ↠[ le ] κ) vals true sched st (o , sc , s′))
             (standing pfs) rp s₀ sched st)
           (λ r → QEmpty (Stage.hd r))
fiDead {Γ = Γ} {e = e} {u = u} op allNid inst le κ pfs rp s₀ h g now vals col {sched} {st} rm hs@((c , lts) , ap , hsκ) eqa
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
         ( (lookup-set (nodeCt sched) ns (EvalSt.nodes st) , ≤-refl ∷ᵃ []ᵃ)
         , (λ k′ on onκ → fresh-apart κ pfs hs k′ (node-one {nodeCt sched} {k′} on) onκ)
         , holdsFs-step κ pfs (λ k′ on k< → set-above (nodeCt sched) k′ ns (EvalSt.nodes st) (<→≢ᵇ k<)) (n≤1+n _) hs )
... | (r , d , tr , hl , kp)
  with translate-sub-end ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
...   | (h″ , _ , eq) =
      let tr′ = translate-sub ≤-refl aM (thruStep op (nodeCt sched) aM) (just ns) gns κ pfs rp tr
      in r , sub-all refl d , tr′
       , unheadHolds (thru-outer op (nodeCt sched)) ≤-refl κ h″ (endPre tr′) (subst (λ p → PreHolds _ _ p _ _) eq hl)
       , unheadKept (thru-outer op (nodeCt sched)) ≤-refl κ h″ (endPre tr′)
           {sched} {bumpNode sched} {st = st} {st₁ = installNode (nodeCt sched) ns st}
           (λ k′ k< on → subst T (<→≢ᵇ k<) (node-one {nodeCt sched} {k′} on)) (n≤1+n _)
           (λ k′ k< → set-above (nodeCt sched) k′ ns (EvalSt.nodes st) (<→≢ᵇ k<))
           (subst (λ p → Kept _ p _ _ _ _) eq kp)
red-all {n = n} op ns gns b ρ rρ k ok aK aB aM {lo = lo} κ fallen rp s₀ now sched st rm fell
  with redExpAcc b ρ rρ k ok aK aB aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ) fallen
         (dropS (fallenRP (<-wellFounded (n ∸ lo)) ≤-refl aM (thru-outer op (nodeCt sched) ↠[ ≤-refl ] κ))) s₀ now
         (bumpNode sched) (installNode (nodeCt sched) ns st) rm fell
... | (r , d , tr , hl , kp) =
      r , sub-all refl d , []ᵗ
    , subst (λ p → PreHolds _ _ p _ _) (fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM _ tr) hl , tt

red-mergeAll lim b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all mergeAllᵒ (mergeAll-st lim 0 [] false) (λ _ → refl) b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-merge-all d , rest
red-switchAll b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all switchᵒ (switch-st nothing false) tt b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-switch-all d , rest
red-exhaustAll b ρ rρ k ok aK (acc rs) aM κ pre rp s₀ now sched st rm h =
  let (r , d , rest) = red-all exhaustᵒ (exhaust-st false false) tt b ρ rρ k ok aK (rs ≤-refl) aM κ pre rp s₀ now sched st rm h
  in r , subs-exhaust-all d , rest
