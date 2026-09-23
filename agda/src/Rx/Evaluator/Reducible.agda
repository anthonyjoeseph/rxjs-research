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
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _∸_; s≤s; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<; n≤1+n; <-≤-trans; <⇒≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)

open import Rx.Prim using (Tick; ObservableInput)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; isData; unfoldμ; varᵗ; unit̂;
  bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ; FnClo; applyClo)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; PreservedBelow; pres; below; pres-write)
open import Decide using (∧ˡ; ∧ʳ; ≡ᵇ→≡; ≡ᵇ-refl)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f;
  batchSync-f; from-inner; thru-outer; NodeState; lookupNode; frameNodes; pathHasNode;
  register; installNode; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; mergeAllᵒ)
open import Rx.Evaluator.Unconn-Arith using (unconn; unconn-insert; fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-of; subs-empty; subs-mint; subs-defer; subs-floor; subs-μ; subs-map;
  subs-shared; slot-spent; slot-join; slot-connect; connect;
  foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; injectRoot)

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
-- there is no successor to compute past that point and `fellᵗ` records
-- only that it happened.  The arm above still owes the fall itself,
-- as the ground its answer ends on.
data Trace {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
           (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t)
         : (pre : Pre κ) → RP {e = e} m P S κ pre → S → Set₁ where
  []ᵗ   : ∀ {pre rp s} → Trace m P S κ pre rp s
  fellᵗ : ∀ {pre rp s} → Trace m P S κ pre rp s
  _∷ᵗ_  : ∀ {pre rp s} (c : Call {e = e} m P κ pre)
        → Trace m P S κ (Ans.pre′ (apply rp s c)) (next (apply rp s c)) (Ans.s′ (apply rp s c))
        → Trace m P S κ pre rp s

-- where a trace ends: the ground it left the path on
endPre : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo} {P : Val Γ u → Set₁} {S : Set}
         {κ : Path Γ lo u t} {pre : Pre κ} {rp : RP {e = e} m P S κ pre} {s : S}
       → Trace {e = e} m P S κ pre rp s → Pre κ
endPre {pre = pre} []ᵗ = pre
endPre fellᵗ           = fallen
endPre (c ∷ᵗ tr)       = endPre tr

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
-- and every inner under the exit frame; a walk-order inner is
-- subscribed by the arm itself, and the continuation it is subscribed
-- under is the replay of the arm's own over the previous inner's
-- trace, which is what the exit frame's peel used to do.  The drain
-- descends on its budget and the queue under an unchanged room, and
-- the guard on a queue outgrowing its budget is the branch the second
-- runtime guard answered.
postulate
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
translate le aM fs h rh κ pfs rp []ᵗ   = []ᵗ
translate le aM fs h rh κ pfs rp fellᵗ = fellᵗ
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
fallen-stays ac le (acc rsM) κ []ᵗ       = refl
fallen-stays ac le (acc rsM) κ fellᵗ     = refl
fallen-stays ac le (acc rsM) κ (c ∷ᵗ tr) = fallen-stays ac le (acc rsM) κ tr

-- and the translation ends where the source's trace did, one frame down
translate-end : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
                {f : Frame Γ s u} {Held : HeldF f → Set₁}
                (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
                (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (pfs : PreFs κ)
                (rp : RP {e = e} m (Red m u) S κ (standing pfs)) {s₀ : S}
              → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (standing (h , pfs)) (liveRP le aM fs h rh κ pfs rp) s₀)
              → Σ (HeldF f) (λ h″ → endPre tr ≡ headPre h″ (endPre (translate le aM fs h rh κ pfs rp tr)))
translate-end-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo ℓ s u} {S : Set}
                   {f : Frame Γ s u} {Held : HeldF f → Set₁}
                   (le : lo ≤ ℓ) (aM : Acc _<_ m) (fs : FrameStep {e = e} f (Red m s) (Red m u) Held)
                   (h : HeldF f) (rh : Held h) (κ : Path Γ ℓ u t) (p : Pre κ)
                   (rp : RP {e = e} m (Red m u) S κ p) {s₀ : S}
                 → (tr : Trace {e = e} m (Red m s) S (f ↠[ le ] κ) (headPre h p) (headNext le aM fs h rh κ p rp) s₀)
                 → Σ (HeldF f) (λ h″ → endPre tr ≡ headPre h″ (endPre (translate-go le aM fs h rh κ p rp tr)))
translate-end le aM fs h rh κ pfs rp []ᵗ   = h , refl
translate-end le aM fs h rh κ pfs rp fellᵗ = h , refl
translate-end le aM fs h rh κ pfs rp {s₀} (c ∷ᵗ tr) =
  translate-end-go le aM fs (held (step fs h (Call.vals c) (Call.fin c) (Call.sched c) (Call.st c)))
    (proj₂ (step-red fs (Call.col c) rh)) κ (Ans.pre′ an) (next an) tr
  where an = apply rp s₀ (headCall fs h rh κ pfs c)
translate-end-go le aM fs h rh κ (standing pfs) rp tr = translate-end le aM fs h rh κ pfs rp tr
translate-end-go {n = n} {lo = lo} le aM fs h rh κ fallen rp tr =
  h , fallen-stays (<-wellFounded (n ∸ lo)) ≤-refl aM (_ ↠[ le ] κ) tr

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
...   | (h″ , eq) =
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
red-input-shared {n = n} i d {okd} aI ρ κ below pre rp s now sched slEq st aM rm h
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
          , fellᵗ
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
