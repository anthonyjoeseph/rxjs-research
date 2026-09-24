------------------------------------------------------------------
-- REDUCIBILITY'S VOCABULARY: THE CEILING, THE CONTINUATION RECORDS,
-- THE PATH INVARIANTS, AND THE PER-FRAME STEP FACTS THE CANDIDATE'S
-- MUTUAL BLOCK CONSUMES.  Nothing here calls into that block, so an
-- edit to the block re-checks none of it (`Rx.Evaluator.Reducible`).
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Support where

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
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; z≤n; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (_<?_; _≤?_; ≤-refl; ≤-trans; n≤1+n; <-≤-trans; <-irrefl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Prim using (Tick; ObservableInput; hot; cold)
open import Rx.Slots using (scripted)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; isData; inputsBelowᵉ; FnClo; applyClo; _≟ᵗ_)
open import Rx.Exp.Guarded using (gsizeᵉ)
open import Rx.Mint using (sourceᵏ; nodeᵏ; regᵏ; ordinalᵏ; freshId; setAt)
open import Rx.Evaluator.Freshness using (nodeCt; PreservedBelow; pres; below; lookup-set; set-above; <→≢ᵇ)
open import Decide using (≡ᵇ→≡; ≡ᵇ-refl)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root; share-sink; _↠[_]_; Frame; map-f; scan-f; take-f;
  batchSync-f; from-inner; thru-outer; NodeState; lookupNode; frameNodes; pathHasNode;
  register; installNode; atDyn; atSlot; lowerFloor; memberSource; mergeAll-st; mergeAllᵒ;
  AllOp; switchᵒ; exhaustᵒ; NodeId; RegRow; cell-st; take-st; switch-st; exhaust-st;
  batchSync-st; setNode; hasRoom; consumeUsable; finishUsable; thruWrap; switchKill;
  aliveThroughᶠ; RegId; RegSrc; regFloor; cutThrough; takeVals; takeDispatch; scanVals;
  scanDispatch; batchVals; batchDispatch; batchDown; resolve; shareAdmit; shareDying; drainSt)
open import Rx.Evaluator.Unconn-Arith using (unconn; fell-keeps; room-keeps)
open import Rx.Evaluator.Keeps using (foldPath-keeps; stepFrame-keeps; Keeps; innerFinish-keeps)
open import Rx.Evaluator.Domain using (subscribeE⇓; mergeAllDrain⇓; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async;
  foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; injectRoot; thruConsume⇓;
  consume-all-nil; consume-switch-nil; consume-exhaust-nil; drain-spent; innerFinish⇓;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil; innerReact⇓;
  react-false; react-alive; react-dead; step-from-inner; step-take; step-batchSync)

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
-- the rule holds in.  The route is one
-- structural induction over the evaluator's relations, in the shape of
-- the one that proves the room is kept.
postulate
  -- PROBED: `Probed.Rule-Kept` -- the merge's head step over a literal of
  --   deferred inners, at a store of rows sharing the merge's node and at
  --   one also holding a row through a node ending at a share's sink,
  --   and over two reads of a share whose def is a merge, the step that
  --   connects it and then joins it.
  --   `Probed.Base-Leaves` -- the head step of a merge handed a fresh take
  --   of a hot slot, at a store holding two live takes through its node.
  step-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo ℓ} {f : Frame Γ s u}
                (le : lo ≤ ℓ) {κ : Path Γ ℓ u t} {now vals fin sched st r}
            → stepFrame⇓ {e = e} now f κ vals fin sched st r
            → Sound (f ↠[ le ] κ) sched st
            → Sound (f ↠[ le ] κ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
  -- PROBED: `Probed.Rule-Kept` -- the root subscribe of a merge of
  --   deferred inners, and of one reading a share whose def is deferred,
  --   asked at the root and, in the second, at the sink; the root
  --   subscribe of two reads of a share whose def is a merge, asked at the
  --   root and the sink; and the second read's subscribe, which joins the
  --   connected share, asked at the share's own row -- a κ₂ ending at the
  --   sink through the def merge's node.
  --   `Probed.Base-Leaves` -- a fresh take of a hot slot subscribed as a
  --   root merge's inner, asked at a live sibling take's path, a κ₂
  --   sharing the merge's node.
  subscribe-kept : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {o : Val Γ (obs u)}
                     {κ : Path Γ lo u t} {now sched st r}
                 → subscribeE⇓ {e = e} o κ now sched st r → Sound κ sched st
                 → ∀ {lo′ s′} (κ₂ : Path Γ lo′ s′ t) → Sound κ₂ sched st → Agree κ κ₂
                 → Sound κ₂ (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  -- PROBED: `Probed.Rule-Kept` -- the merge's outer fold in all three
  --   programs, asked at its own path, the root and the sink; the third
  --   reads a share whose def is a merge twice, connecting it then
  --   joining it.
  --   `Probed.Base-Leaves` -- a root merge handed a fresh take, asked at a
  --   live sibling take's path, and a root switch cutting its live take,
  --   asked at the cut take's path.  Not a scan, nor a slot's arrival.
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

-- a drain step decided outside the drain's cycle: room was spent, or the
-- queue read back within its budget.  `f` is forced only when the bound
-- is refuted, so the evaluator never runs a postulate handed in as `f`
spend-or : ∀ {x y w l : ℕ} → ((x < y → ⊥) → w ≤ l) → x < y ⊎ (x < y → ⊥) × w ≤ l
spend-or {x} {y} {w} {l} f with x <? y
... | yes sp = inj₁ sp
... | no nsp with w ≤? l
...   | yes bd = inj₂ (nsp , bd)
...   | no nbd = ⊥-elim (nbd (f nsp))

-- a bound decided at run time, `f` forced only when it is refuted: a
-- proof carried across a fold stands on the fold's own postulates, and a
-- ceiling built from one would be forced by the next accessibility step
ceil-or : ∀ {w l : ℕ} → w ≤ l → w ≤ l
ceil-or {w} {l} f with w ≤? l
... | yes bd = bd
... | no nbd = ⊥-elim (nbd f)

-- a Boolean decided outside a cycle, its equation handed to each branch.
-- A `with` inside a cycle binds a clause's matched accessibility by its
-- field, so a call re-applying `acc` reads to the termination checker as
-- unrelated to the clause's own argument, and the order is lost
by-bool : ∀ {a} {A : Set a} (b : Bool) → (b ≡ false → A) → (b ≡ true → A) → A
by-bool false f t = f refl
by-bool true  f t = t refl

-- A RUN SPENT ROOM: something it subscribed connected.
Spends : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Spends sched st sched′ st′ =
  unconn (Sched.slots sched′) (EvalSt.connectedShares st′) < unconn (Sched.slots sched) (EvalSt.connectedShares st)

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

-- THE INNER FRAME'S STEP.  Values pass; an end passes while a chain
-- under this instance is still registered; otherwise the finish runs
-- at the node, and the merge's drain there has nothing to subscribe.
fiStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u} (op : AllOp) (allNid inst : NodeId)
       → SubStep {e = e} (from-inner {s = u} op allNid inst) QEmpty m

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
