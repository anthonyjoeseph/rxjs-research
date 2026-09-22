------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS.
------------------------------------------------------------------

-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- expression to its subscription derivation may not mention that
-- derivation's own type in a negative position, so the candidate
-- cannot be an inductive family over the domain relation.  Defined by
-- recursion on `Ty` it never needs to be: `Red (obs u)` mentions
-- `Red u` at a strictly smaller type and `subscribeE⇓` only
-- positively.
--
-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the scheduler and the evaluator state as plain indices with no
-- precondition, so the candidate can demand subscribability in EVERY
-- state -- which is what lets a flattener's hop subscribe its inner in
-- whatever state the outer delivery reached, with no invariant
-- threaded.
--
-- AND THE ENVIRONMENT IS CARRIED RATHER THAN SUBSTITUTED, WHICH IS
-- WHAT MAKES THE WHOLE SUBSTITUTION LAYER UNNECESSARY.  An observable
-- value IS a body paired with the environment it closed over, so the
-- expression face concludes about that pair directly and no lemma
-- relating a peel to a substitution is owed anywhere.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; _+_; _<ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Tick; PlainEvent; valueᵖ; completeᵖ; hot; cold)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; _≟ᵗ_;
  Ctx; Closed; Val; Exp; Tm; FnClo; applyClo; Env; []ᵉ; _∷ᵉ_; evalWith; foldVals;
  lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  isData; unfoldμ;
  varᵗ; unit̂; bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ;
  caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; freshId; setAt)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Evaluator using (Stream; Burst; Sched; EvalSt; Path; Frame; _↠_;
  map-f; take-f; scan-f; batchSync-f; from-inner; thru-outer; share-sink;
  mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp; NodeId; NodeState;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  takeVals; takeDispatch; scanVals; scanDispatch; batchVals; batchDispatch;
  lookupNode; installNode; oneShotBurst; spentBurst; memberSource;
  splitEvents; splitBurst; consumeUsable; hasRoom; switchKill; thruWrap;
  register; atSlot; lowerFloor; burstCompleted)
open import Rx.Evaluator.Freshness using (lookup-set; PreservedBelow)
open import Rx.Evaluator.Freshness.Preserve using (subscribeE-preserves)
open import Rx.Evaluator.Domain using (srcFrame; subscribeE⇓; pushBurst⇓; stepFrame⇓;
  step-map; step-scan; step-take; step-batchSync; push-nil; push-cons;
  subs-of; subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan;
  subs-batchSync; subs-mint; subs-defer; subs-floor; subs-hot-done; subs-hot-live;
  subs-cold-sync; subs-cold-async; subs-μ; sub-all; subs-merge-all;
  subs-switch-all; subs-exhaust-all; thruConsume⇓; thruWalk⇓;
  step-thru-outer; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; subs-shared; slot-spent; slot-join; slot-connect;
  connect-live; connect-died)

-- A PLAIN EVENT CARRIES A PAYLOAD ONLY IN ITS VALUE ARM; the end
-- carries none and so constrains nothing.
EvSat : ∀ {A : Set} → (A → Set) → PlainEvent A → Set
EvSat P (valueᵖ v) = P v
EvSat P completeᵖ  = ⊤

-- …and a STREAM satisfies a predicate when every value any of its
-- bursts ever carries does.  Taking the predicate as a parameter is
-- what keeps `Red`'s recursion structural: the recursive occurrence is
-- `Red u` applied at a strictly smaller type, not a call at the type
-- being defined.
StreamSat : ∀ {A : Set} → (A → Set) → List (List (PlainEvent A)) → Set
StreamSat P = All (All (EvSat P))

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the pair
-- the whole argument turns on -- a subscription derivation in every
-- state, and the guarantee that everything that derivation emits is
-- itself reducible at the element type.
Red : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → Set
Red unitᵗ     _        = ⊤
Red boolᵗ     _        = ⊤
Red natᵗ      _        = ⊤
Red uniqᵗ     _        = ⊤
Red (s ×ᵗ t)  (a , b)  = Red s a × Red t b
Red (s +ᵗ t)  (inj₁ a) = Red s a
Red (s +ᵗ t)  (inj₂ b) = Red t b
Red (listᵗ t) vs       = All (Red t) vs
Red {Γ = Γ} (obs u) b =
  ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    subscribeE⇓ {e = e} b κ now sched st r × StreamSat (Red u) (proj₁ r)

-- WHY A SHARE'S FAN-OUT COSTS THE CANDIDATE NOTHING, WHICH IS THE ONE
-- THING ABOUT `connect` THAT WAS NOT OBVIOUS.  A shared slot subscribes
-- its def ONCE and attaches every later reader to that one connection,
-- so the natural fear is that reducibility must be maintained as an
-- INVARIANT ON STORED STATE.  Nothing of the kind is owed, because the
-- fan-out carries NO PAYLOAD: a late reader's arm emits nothing at all,
-- a spent slot's arm emits only the end, and the only arm carrying
-- values is the one that subscribes the def -- whose values are the
-- def's, which is the induction hypothesis.  The semantic fact
-- underneath is that this share does not replay, so there is nothing
-- stored for the invariant to be about.

-- A SPENT SOURCE'S BURST is an end and nothing else, so every
-- predicate holds of it for want of anything to hold of.
StreamSat-spent : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                → StreamSat P (spentBurst {Γ = Γ} {u = u})
StreamSat-spent = (tt ∷ []) ∷ []

-- PUSHING A BURST THROUGH A FRAME, WITH THE CANDIDATE CARRIED ACROSS.
-- The transformer arms all have the same two-step shape -- run the
-- source, then push what it emitted through this frame -- so the second
-- step is one obligation stated once rather than several.
RedPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
        → Tick → Frame Γ s u → Path Γ lo u t
        → Stream Γ s → Sched Γ → EvalSt e → Set
RedPush {Γ = Γ} {e = e} {u = u} now f κ burst sched st =
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    pushBurst⇓ {e = e} now f κ burst sched st r × StreamSat (Red u) (proj₁ r)

-- A MAPPING FRAME APPLIES ITS CLOSURE TO EVERY ARRIVING VALUE, so what
-- it produces is reducible exactly when the closure sends reducible to
-- reducible.  That is the only thing a frame wants from the term face,
-- and it has to be stated as a HYPOTHESIS rather than reached by a
-- call: the fundamental theorem at terms is a member of the recursion
-- at the foot of this module, so a walk declared above it cannot name
-- it.
RedFn : ∀ {n} {Γ : Ctx n} {s u} → FnClo Γ s u → Set
RedFn {Γ = Γ} {s = s} {u = u} fn =
  ∀ {v : Val Γ s} → Red s v → Red u (applyClo fn v)

-- WHAT A FRAME'S OWN NODE MUST HOLD, AND IT IS ONLY EVER THE FOLD
-- THAT ASKS.  The node census says every other frame reads a store
-- that carries no payload -- a count, a flag, an identifier, a queue
-- nothing in a subscribe reads back -- so its obligation is the
-- trivial one and costs a `tt` at every site.  The fold's cell holds a
-- VALUE, and the value it holds is what leaves the frame, so this is
-- where the candidate has to already be true of the store.  Stating it
-- as a predicate on the state rather than as a hypothesis on the
-- fold's own statement is what keeps it PRESERVED rather than merely
-- assumed: the step face re-establishes it at the state it hands back,
-- and the writeback is exactly the fold applied to two things the push
-- already has.
-- DEAD ROUTE: carrying this in the STATE RECORD instead, as a field
--   beside the nodes.  It closes a definitional cycle rather than an
--   import cycle: the candidate's observable arm is indexed by the
--   subscription relation, which is itself indexed by the state
--   record, so a field of that record naming the candidate is
--   circular however the modules are cut.  A PRECONDITION on the
--   candidate's own observable arm is the same cycle stated directly,
--   and it does not decrease: the arm recurses on the element type,
--   while a predicate over a store reaches the candidate at whatever
--   type a node happens to hold, which is unrelated to it.
--   Parameterising the state record over an abstract node predicate is
--   that same cycle DEFERRED -- the instantiation ties the knot, and
--   the executable face pays a threaded parameter it only ever meets
--   at the trivial predicate.  And a SYNTACTIC invariant saying a
--   stored value is the denotation of a closed term is VACUOUS:
--   reflection is total, so every value is one and the pairing carries
--   no information.
RedNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
        → Frame Γ s u → EvalSt e → Set
RedNode {Γ = Γ} (scan-f fn nid) st =
  ∀ {w} {a : Val Γ w}
  → lookupNode nid (EvalSt.nodes st) ≡ just (cell-st a) → Red w a
RedNode (map-f fn)                  st = ⊤
RedNode (take-f nid)                st = ⊤
RedNode (batchSync-f nid)           st = ⊤
RedNode (from-inner op allNid inst) st = ⊤
RedNode (thru-outer op nid)         st = ⊤

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's closure pairs a term with one
-- such environment, so the fundamental theorem at terms has to be
-- stated under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} {Θ : List Ty} → Env Γ Θ → Set
RedEnv []ᵉ                  = ⊤
RedEnv (_∷ᵉ_ {s = t} v vs)  = Red t v × RedEnv vs

-- THE SAME CLAIM ONE BATCH DOWN: a frame, the values that arrived at
-- it, and the candidate carried across to what leaves.  The push above
-- walks a stream burst by burst, so it is stated over a stream while
-- this is stated over one list, which is where every operator's own
-- machinery sits.
RedStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
        → Tick → Frame Γ s u → Path Γ lo u t
        → List (Val Γ s) → Bool → Sched Γ → EvalSt e → Set
RedStep {Γ = Γ} {e = e} {u = u} now f κ vals fin sched st =
  Σ (List (Val Γ u) × Bool × Sched Γ × EvalSt e) λ r →
    stepFrame⇓ {e = e} now f κ vals fin sched st r × All (Red u) (proj₁ r)
      × RedNode f (proj₂ (proj₂ (proj₂ r)))

-- A SPLIT TAKES THE VALUE COLUMN OUT OF A BURST, and nothing else, so
-- whatever held of every value the burst carried holds of every value
-- the split hands back.  The end carries no payload, so it simply
-- leaves the column.
satSplitEvents : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                 (es : Burst Γ u) → All (EvSat P) es
               → All P (proj₁ (splitEvents es))
satSplitEvents []               []       = []
satSplitEvents (valueᵖ _ ∷ es)  (p ∷ ps) = p ∷ satSplitEvents es ps
satSplitEvents (completeᵖ ∷ es) (_ ∷ ps) = satSplitEvents es ps

satSplitBurst : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                (str : Stream Γ u) → StreamSat P str
              → All P (proj₁ (splitBurst str))
satSplitBurst []         []       = []
satSplitBurst (b ∷ bs) (q ∷ qs) =
  ++⁺ (satSplitEvents b q) (satSplitBurst bs qs)

-- AND THE WRAP AROUND THE WALK NEVER TOUCHES THAT COLUMN.  What it
-- decides is whether the operator is finished and what its node then
-- holds, both of which the candidate is silent about; the values pass
-- through every arm unchanged.  Spelling the arms out is the price of
-- the machine reading its own store: a catch-all in the definition
-- does not reduce against a catch-all in a proof.
thruWrap-vals : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                (op : AllOp) (nid : NodeId) (fin : Bool)
                {vs : List (Val Γ u)}
                {sched′ : Sched Γ} {st′ : EvalSt e}
              → proj₁ (thruWrap {e = e} op nid fin (vs , sched′ , st′)) ≡ vs
thruWrap-vals mergeAllᵒ nid false = refl
thruWrap-vals switchᵒ   nid false = refl
thruWrap-vals exhaustᵒ  nid false = refl
thruWrap-vals mergeAllᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals switchᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals exhaustᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl

-- CONSUMING ONE ARRIVING OBSERVABLE, and walking a list of them, with
-- the candidate carried across.  These are the flattener's two halves
-- of `RedStep`, stated separately for the same reason the machine
-- states them separately: what a consume decides is whether the
-- observable is taken at all, and every operator answers that off the
-- store.
RedConsume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
           → AllOp → NodeId → Path Γ lo u t → Tick
           → Val Γ (obs u) → Sched Γ → EvalSt e → Set
RedConsume {Γ = Γ} {e = e} {u = u} op nid κ now o sched st =
  Σ (List (Val Γ u) × Sched Γ × EvalSt e) λ r →
    thruConsume⇓ {e = e} op nid κ now o sched st r × All (Red u) (proj₁ r)

RedWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
        → AllOp → NodeId → Path Γ lo u t → Tick
        → List (Val Γ (obs u)) → Sched Γ → EvalSt e → Set
RedWalk {Γ = Γ} {e = e} {u = u} op nid κ now vals sched st =
  Σ (List (Val Γ u) × Sched Γ × EvalSt e) λ r →
    thruWalk⇓ {e = e} op nid κ now vals sched st r × All (Red u) (proj₁ r)

-- THE HOP IS PAID FOR BY THE ARRIVING VALUE'S OWN CANDIDATE, which is
-- what makes this a body rather than a leaf.  A subscribe arm hands
-- the observable down at a `from-inner` frame and splits what comes
-- back; the candidate quantifies over every schedule and every state,
-- so the freshly-counted schedule this arm builds is one of them by
-- construction and no invariant is threaded.  Every OTHER arm emits
-- nothing at all -- a refused arrival is queued, an unusable store
-- collapses -- so its column is satisfied for want of anything to hold
-- of.
red-consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
              (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
              (now : Tick) {o : Val Γ (obs u)} → Red (obs u) o
            → (sched : Sched Γ) (st : EvalSt e)
            → RedConsume {e = e} op nid κ now o sched st
red-consume {u = u} mergeAllᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (switch-st _ _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (exhaust-st _ _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u in eqw
...   | no _ =
        _ , consume-all-nil
              (trans (cong (consumeUsable mergeAllᵒ u) eq) (cong ⌊_⌋ eqw)) , []
...   | yes refl with hasRoom lim act in eqr
...     | false = _ , consume-all-enqueue eq eqr , []
...     | true =
          let ((burst , _ , _) , d , ss) =
                ro (from-inner mergeAllᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠ κ) now
                   (record sched
                      { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched)))
                                 (Sched.mint sched) })
                   st
          in _ , consume-all-sub eq eqr (inner refl d refl)
               , satSplitBurst burst ss

red-consume {u = u} switchᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (exhaust-st _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (sched₁ , st₁) =
        let ((burst , _ , _) , d , ss) =
              ro (from-inner switchᵒ nid (freshId nodeᵏ (Sched.mint sched₁)) ↠ κ) now
                 (record sched₁
                    { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched₁)))
                               (Sched.mint sched₁) })
                 st₁
        in _ , consume-switch-sub eq eqk (inner refl d refl)
             , satSplitBurst burst ss

red-consume {u = u} exhaustᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (switch-st _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st true _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st false od) =
      let ((burst , _ , _) , d , ss) =
            ro (from-inner exhaustᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠ κ) now
               (record sched
                  { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched)))
                             (Sched.mint sched) })
               st
      in _ , consume-exhaust-sub eq (inner refl d refl)
           , satSplitBurst burst ss

-- THE WALK IS THE CONSUME THREADED, and the column it returns is the
-- concatenation of the columns each arrival produced.
red-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
           (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
           (now : Tick) {vals : List (Val Γ (obs u))}
         → All (Red (obs u)) vals
         → (sched : Sched Γ) (st : EvalSt e)
         → RedWalk {e = e} op nid κ now vals sched st
red-walk op nid κ now []       sched st = _ , walk-nil , []
red-walk op nid κ now (r ∷ rs) sched st =
  let ((_ , sched₁ , st₁) , c , rv) = red-consume op nid κ now r sched st
      (_ , w , rv′) = red-walk op nid κ now rs sched₁ st₁
  in _ , walk-cons c w , ++⁺ rv rv′

-- THE FLATTENING WALK, AND THE NODE IT READS OWES NOTHING.  Every
-- value it produces is an inner subscribed out of the arriving batch,
-- and the census at `NodeState` says the nodes it consults carry no
-- payload to confuse that -- so this frame's node obligation is the
-- trivial one and the whole content is the value column.
--
-- AND THE QUEUE IT PUSHES INTO IS WRITE-ONLY FROM HERE, WHICH IS WHY
-- NO STORE INVARIANT IS OWED AT ALL.  A refused arrival is enqueued
-- and never read back within a subscribe: the read is the DRAIN, which
-- hangs off an inner's completion, and `srcFrame` says in a type that
-- a push cycle is entered only from a source former.  So the entry a
-- subscribe stores is one this face can put in and never has to take
-- out.
red-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
           (now : Tick) (op : AllOp) (nid : NodeId)
           (κ : Path Γ lo u t)
           {vals : List (Val Γ (obs u))} → All (Red (obs u)) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
         → RedStep {e = e} now (thru-outer op nid) κ vals fin sched st
red-thru now op nid κ rv fin sched st =
  let (_ , w , rvs) = red-walk op nid κ now rv sched st
  in _ , step-thru-outer w
       , subst (All (Red _)) (sym (thruWrap-vals op nid fin)) rvs
       , tt

-- The end carries no payload, so a burst's values are the only thing
-- to check and a burst with none is satisfied outright.
satEvents : ∀ {A : Set} {P : A → Set} {vals : List A} {rest : List (PlainEvent A)}
          → All P vals → All (EvSat P) rest
          → All (EvSat P) (map valueᵖ vals ++ rest)
satEvents []       ar = ar
satEvents (p ∷ ps) ar = p ∷ satEvents ps ar

satOneShot : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} {vals}
           → All P vals → StreamSat P (oneShotBurst {Γ = Γ} {u = u} vals)
satOneShot ps = satEvents ps (tt ∷ []) ∷ []

-- EVERY VALUE OF A DATA TYPE IS REDUCIBLE, AND THAT IS WHY THE SLOT
-- ARM IS SHORT.  The candidate is trivial at each data former and
-- uninhabitable at `obs`, so the recursion here is the same one `Red`
-- itself runs -- it just has to be SAID, because a slot's element type
-- is `lookup Γ i` and no reduction fires on a neutral index.  What
-- carries it is the side condition every scripted slot already holds.
-- THE PRODUCT AND SUM ARMS OF `isData` GUARD ON THE LEFT FACTOR, so
-- the witness has to be taken apart before either side can be used.
-- It sits ABOVE rather than between the signature and the clauses
-- because a declaration placed there would join the block below: the
-- dev loop stubs a multi-member block, so keeping these out of one is
-- what keeps them checked for real, termination included.
T-if : ∀ (b c : Bool) → T (if b then c else false) → T b × T c
T-if true  c ok = tt , ok
T-if false c ()

red-data : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) → (v : Val Γ u)
         → Red {Γ = Γ} u v
redDatas : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) → (vs : List (Val Γ u))
         → All (Red {Γ = Γ} u) vs

red-data unitᵗ    _  _       = tt
red-data natᵗ     _  _       = tt
red-data boolᵗ    _  _       = tt
red-data uniqᵗ    _  _       = tt
red-data (listᵗ u) ok vs     = redDatas u ok vs
red-data (s ×ᵗ t) ok (a , b) =
  let (o₁ , o₂) = T-if (isData s) (isData t) ok
  in red-data s o₁ a , red-data t o₂ b
red-data (s +ᵗ t) ok (inj₁ a) = red-data s (proj₁ (T-if (isData s) (isData t) ok)) a
red-data (s +ᵗ t) ok (inj₂ b) = red-data t (proj₂ (T-if (isData s) (isData t) ok)) b
red-data (obs u)  () _

redDatas u ok []       = []
redDatas u ok (v ∷ vs) = red-data u ok v ∷ redDatas u ok vs

-- The cold-with-a-tail arm emits its synchronous values with nothing
-- after them, so it wants the values alone rather than `satEvents`'
-- append.
satValues : ∀ {A : Set} {P : A → Set} {vals : List A}
          → All P vals → All (EvSat P) (map valueᵖ vals)
satValues []       = []
satValues (p ∷ ps) = p ∷ satValues ps

-- AND A FRAME OWES IT WHEREVER IT APPLIES ONE, WHICH IS TWO OF THE
-- SIX.  The mapping frame applies its closure to what arrived; the
-- fold applies its own to the pair of the stored accumulator and what
-- arrived, so it owes the same thing -- what it additionally needs,
-- the first component of that pair being reducible, is the store
-- obligation beside this one rather than anything about the closure.
RedFrame : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
RedFrame (map-f fn)                  = RedFn fn
RedFrame (scan-f fn nid)             = RedFn fn
RedFrame (take-f nid)                = ⊤
RedFrame (batchSync-f nid)           = ⊤
RedFrame (from-inner op allNid inst) = ⊤
RedFrame (thru-outer op nid)         = ⊤

redMapVals : ∀ {n} {Γ : Ctx n} {s u} (fn : FnClo Γ s u) → RedFn fn
           → {vals : List (Val Γ s)} → All (Red s) vals
           → All (Red u) (map (applyClo fn) vals)
redMapVals fn rf []       = []
redMapVals fn rf (p ∷ ps) = rf p ∷ redMapVals fn rf ps

-- A TRUNCATION CANNOT INVENT A VALUE, WHICH IS WHY THE TAKE ARM NEEDS
-- NOTHING FROM THE STORE.  The node a take installs holds a COUNT, and
-- the dispatch's value column is a prefix of the burst it was handed --
-- on the cut path and the non-cut path alike, and at a stuck lookup the
-- column is empty.  So the arriving candidates are the departing ones
-- and the store decides only HOW MANY survive.  This is the contrast
-- that pins what a fold's accumulator is actually missing: that cell
-- holds a VALUE, and no hypothesis here says anything about it.
redTakeVals : ∀ {n} {Γ : Ctx n} {s} {P : Val Γ s → Set} (k : ℕ)
              {vals : List (Val Γ s)} → All P vals
            → All P (proj₁ (takeVals k vals))
redTakeVals zero          rv        = []
redTakeVals (suc k)       []        = []
redTakeVals (suc zero)    (p ∷ ps)  = p ∷ []
redTakeVals (suc (suc k)) (p ∷ ps)  = p ∷ redTakeVals (suc k) ps

redTakeDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                  (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                → All (Red s) vals
                → All (Red s)
                    (proj₁ (takeDispatch {e = e} nid vals fin sched st m))
redTakeDispatch nid {vals} fin sched st (just (take-st k)) rv
  with proj₂ (proj₂ (takeVals k vals))
... | true  = redTakeVals k rv
... | false = redTakeVals k rv
redTakeDispatch nid fin sched st (just (cell-st _))           rv = []
redTakeDispatch nid fin sched st (just (batchSync-st _))      rv = []
redTakeDispatch nid fin sched st (just (mergeAll-st _ _ _ _)) rv = []
redTakeDispatch nid fin sched st (just (switch-st _ _))       rv = []
redTakeDispatch nid fin sched st (just (exhaust-st _ _))      rv = []
redTakeDispatch nid fin sched st nothing                      rv = []

red-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
           (now : Tick) (nid : NodeId) (κ : Path Γ lo s t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
         → RedStep {e = e} now (take-f nid) κ vals fin sched st
red-take now nid κ rv fin sched st =
  _ , step-take
    , redTakeDispatch nid fin sched st (lookupNode nid (EvalSt.nodes st)) rv
    , tt

-- THE BRACKET REGROUPS AND INVENTS NOTHING, so its whole obligation is
-- that a group's head and its tail are the arriving values they were
-- taken from.  The grouped arm is where the product arm of the
-- candidate and its list arm meet, and both halves come from the one
-- walk that arrived.
redBatchVals : ∀ {n} {Γ : Ctx n} {s} (sync : Bool)
               {vals : List (Val Γ s)} → All (Red s) vals
             → All (Red (s ×ᵗ listᵗ s)) (batchVals sync vals)
redBatchVals sync  []       = []
redBatchVals true  (p ∷ ps) = (p , ps) ∷ []
redBatchVals false (p ∷ ps) = (p , []) ∷ redBatchVals false ps

redBatchDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                   (nid : NodeId) {vals : List (Val Γ s)} (st : EvalSt e)
                   (m : Maybe (NodeState Γ))
                 → All (Red s) vals
                 → All (Red (s ×ᵗ listᵗ s))
                     (batchDispatch {e = e} nid vals st m)
redBatchDispatch nid st (just (batchSync-st sync))     rv = redBatchVals sync rv
redBatchDispatch nid st (just (cell-st _))             rv = []
redBatchDispatch nid st (just (take-st _))             rv = []
redBatchDispatch nid st (just (mergeAll-st _ _ _ _))   rv = []
redBatchDispatch nid st (just (switch-st _ _))         rv = []
redBatchDispatch nid st (just (exhaust-st _ _))        rv = []
redBatchDispatch nid st nothing                        rv = []

red-batchSync : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
                (now : Tick) (nid : NodeId) (κ : Path Γ lo (s ×ᵗ listᵗ s) t)
                {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
                (sched : Sched Γ) (st : EvalSt e)
              → RedStep {e = e} now (batchSync-f nid) κ vals fin sched st
red-batchSync now nid κ rv fin sched st =
  _ , step-batchSync
    , redBatchDispatch nid st (lookupNode nid (EvalSt.nodes st)) rv
    , tt

-- A FOLD IS ITS ACCUMULATOR THREADED ALONG THE BATCH, and so is the
-- claim about it: each output IS the next accumulator, so one walk
-- delivers both the candidate at every emitted value and the candidate
-- at what gets written back.
redScanVals : ∀ {n} {Γ : Ctx n} {s u} (fn : FnClo Γ (u ×ᵗ s) u) → RedFn fn
            → {a : Val Γ u} → Red u a
            → {vals : List (Val Γ s)} → All (Red s) vals
            → All (Red u) (proj₁ (scanVals fn a vals))
              × Red u (proj₂ (scanVals fn a vals))
redScanVals fn rf ra []       = [] , ra
redScanVals fn rf ra (p ∷ ps) =
  let (qs , last) = redScanVals fn rf (rf (ra , p)) ps
  in rf (ra , p) ∷ qs , last

-- the cell read back is the one written, so its payload is that payload
tie-scan : ∀ {n} {Γ : Ctx n} {w w′} {x : Val Γ w} {y : Val Γ w′}
         → _≡_ {A = Maybe (NodeState Γ)} (just (cell-st x)) (just (cell-st y))
         → Red w x → Red w′ y
tie-scan refl r = r

-- AND THE ONE THING THE FOLD'S NODE OBLIGATION CANNOT ESTABLISH FOR
-- ITSELF: that the accumulator installed just before a subscription is
-- the one still standing when the push happens.  A node is keyed by an
-- identifier drawn from the run's own counter, the fold installs at the
-- counter's current value and subscribes with it advanced, and a
-- subscription writes no node below the counter it started at -- so the
-- accumulator is untouched for structural reasons rather than by any
-- property of the candidate.  The floor spent here is the advanced
-- counter itself, which is the tightest one the fold can offer and the
-- only one under which its own node is strictly below.
red-scan-installed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo Θ}
           (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
           {a : Val Γ u} → Red u a
         → ∀ {b : Exp Γ [] [] Θ s} {ρ : Env Γ Θ} {κ : Path Γ lo u t} {now}
         → (sched : Sched Γ) (st : EvalSt e)
         → {sched₂ : Sched Γ} {st₁ : EvalSt e} {burst : Stream Γ s}
         → subscribeE⇓ {e = e} (Θ , b , ρ) (scan-f fn nid ↠ κ) now
             (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
             (installNode nid (cell-st a) st)
             (burst , sched₂ , st₁)
         → RedNode {e = e} (scan-f fn nid) st₁
red-scan-installed fn nid {a} ra sched st d eq =
  tie-scan (trans (sym (trans (PreservedBelow.below
                                 (subscribeE-preserves (suc nid) ≤-refl d)
                                 nid ≤-refl)
                              (lookup-set nid (cell-st a) (EvalSt.nodes st))))
                  eq)
           ra

-- ONE READING OF THE CELL, WHICH IS WHERE BOTH HALVES ARE PAID.  The
-- dispatch it mirrors branches on a lookup the goal does not mention,
-- so the reading is taken as a parameter and pinned by an equation --
-- and that equation is what lets the obligation coming IN be spent on
-- the accumulator that was found, before the obligation going OUT is
-- re-established against the accumulator that replaces it.
redScanDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                  {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                → lookupNode nid (EvalSt.nodes st) ≡ m
                → RedNode {e = e} (scan-f fn nid) st → RedFn fn → All (Red s) vals
                → All (Red u) (proj₁ (scanDispatch {e = e} fn nid vals fin sched st m))
                  × RedNode {e = e} (scan-f fn nid)
                      (proj₂ (proj₂ (proj₂
                        (scanDispatch {e = e} fn nid vals fin sched st m))))
redScanDispatch {u = u} fn nid {vals} fin sched st (just (cell-st {w} a)) eq rn rf rv
  with w ≟ᵗ u
... | no  _    = [] , rn
... | yes refl =
      let (outs , last) = redScanVals fn rf (rn eq) rv
      in outs , λ eq′ → tie-scan (trans (sym (lookup-set nid
                                    (cell-st (proj₂ (scanVals fn a vals)))
                                    (EvalSt.nodes st)))
                                  eq′)
                          last
redScanDispatch fn nid fin sched st nothing                      eq rn rf rv = [] , rn
redScanDispatch fn nid fin sched st (just (take-st _))           eq rn rf rv = [] , rn
redScanDispatch fn nid fin sched st (just (batchSync-st _))      eq rn rf rv = [] , rn
redScanDispatch fn nid fin sched st (just (mergeAll-st _ _ _ _)) eq rn rf rv = [] , rn
redScanDispatch fn nid fin sched st (just (switch-st _ _))       eq rn rf rv = [] , rn
redScanDispatch fn nid fin sched st (just (exhaust-st _ _))      eq rn rf rv = [] , rn

-- A SCAN READS ITS ACCUMULATOR BACK OUT OF A CELL, AND EMITS IT --
-- which is what the node obligation beside the frame's closure is for.
-- Most of the dispatch's readings write nothing and emit nothing, so
-- the obligation they hand back is the one they were given; the cell
-- folds, and there the two halves of the walk above are exactly the two
-- things owed -- the batch that leaves and the accumulator that stays.
red-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
           (κ : Path Γ lo u t) → RedFn fn
         → {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
         → (sched : Sched Γ) (st : EvalSt e)
         → RedNode {e = e} (scan-f fn nid) st
         → RedStep {e = e} now (scan-f fn nid) κ vals fin sched st
red-scan now fn nid κ rf rv fin sched st rn =
  let (rvs , rn′) = redScanDispatch fn nid fin sched st
                       (lookupNode nid (EvalSt.nodes st)) refl rn rf rv
  in _ , step-scan , rvs , rn′

-- STEPPING ONE FRAME, DISPATCHED ON THE FRAME, AND ONLY EVER A SOURCE
-- FRAME.  The mapping arm is a body because nothing about it is
-- stateful; the others each read a node this face installed earlier,
-- which is the one thing the candidate's quantification over every
-- state does not hand back.  The inner's own frame is not answered for
-- at all: `srcFrame` says in a type that a push cycle is only entered
-- from a source former, so it arrives here never, and a leaf stated for
-- it would have been a claim about a run this face cannot reach.
red-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedStep {e = e} now f κ vals fin sched st
red-step now (map-f fn) sv rf κ rv fin sched st rn =
  _ , step-map , redMapVals fn rf rv , tt
red-step now (scan-f fn nid) sv rf κ rv fin sched st rn =
  red-scan now fn nid κ rf rv fin sched st rn
red-step now (take-f nid) sv rf κ rv fin sched st rn =
  red-take now nid κ rv fin sched st
red-step now (batchSync-f nid) sv rf κ rv fin sched st rn =
  red-batchSync now nid κ rv fin sched st
red-step now (from-inner op allNid inst) () rf κ rv fin sched st rn
red-step now (thru-outer op nid) sv rf κ rv fin sched st rn =
  red-thru now op nid κ rv fin sched st

-- a frame's completion flag becomes at most one event
satFin : ∀ {A : Set} {P : A → Set} (b : Bool)
       → All (EvSat P) (if b then completeᵖ ∷ [] else [])
satFin true  = tt ∷ []
satFin false = []

-- PUSHING A STREAM THROUGH A FRAME IS A WALK, AND THE WALK IS A BODY.
-- Each burst is split, stepped and reassembled; the candidate travels
-- on the values alone, which is why the reassembly costs one append of
-- an end and one real obligation.
red-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {burst : Stream Γ s} → StreamSat (Red s) burst
         → (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedPush {e = e} now f κ burst sched st
red-push now f sv rf κ {[]}     []       sched st rn = _ , push-nil , []
red-push now f sv rf κ {b ∷ bs} (p ∷ ps) sched st rn =
  let ((vals′ , fin′ , sched₁ , st₁) , d , rv , rn₁) =
        red-step now f sv rf κ (satSplitEvents b p)
          (proj₂ (splitEvents b)) sched st rn
      ((rest , sched₂ , st₂) , dr , sr) = red-push now f sv rf κ ps sched₁ st₁ rn₁
  in _ , push-cons refl d dr
       , satEvents rv (satFin fin′) ∷ sr

-- an entry of a reducible environment is reducible
redLookup : ∀ {n} {Γ : Ctx n} {Θ t} (ρ : Env Γ Θ) → RedEnv ρ
          → (x : t ∈ Θ) → Red t (lookupEnv ρ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- THE LIST FOLD'S ACCUMULATOR LOOP, WITH THE STEP TAKEN AS A
-- HYPOTHESIS.  The step is one instance of the term face at an
-- environment two entries longer, and it does not vary along the list,
-- so the walk over the list is an ordinary recursion outside the
-- theorem's own cycle.
redFoldVals : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Tm Γ [] [] (s ∷ u ∷ Θ) u)
              (ρ : Env Γ Θ)
            → (∀ {x : Val Γ s} {ac : Val Γ u} → Red s x → Red u ac
                 → Red u (evalWith f (x ∷ᵉ ac ∷ᵉ ρ)))
            → {vs : List (Val Γ s)} → All (Red s) vs
            → {ac : Val Γ u} → Red u ac
            → Red u (foldVals f ρ vs ac)
redFoldVals f ρ step []       rac = rac
redFoldVals f ρ step (p ∷ ps) rac = redFoldVals f ρ step ps (step p rac)

-- THE BODY, AND WHAT PAYS FOR IT.  The expression face and the term
-- face are ONE recursion: a term embeds an expression and an operator
-- carries terms, so neither can be a leaf beside the other without
-- claiming the whole theorem.  Both recurse on the ACCESSIBILITY of
-- the guarded size, which counts an operator's spine and the terms it
-- carries and stops at the gate; every call below hands on a strictly
-- smaller size, the fixpoint arm included.
--
-- THE ONE ARM WITH NO SUBTERM IS THE μ, AND THE SYNTAX PAYS FOR IT.
-- An unfolding is no subterm of its fixpoint and sits at the same
-- type, so neither the syntax nor the candidate's own type recursion
-- reaches it.  What does is the size: the μ former spends a unit, the
-- gate the μ variable must sit behind is where the size stops looking,
-- and the unfolding therefore has exactly the size the body had.
--
-- THE CEILING IS A MEASURE COMPONENT, NOT A HYPOTHESIS.  The walk
-- carries a stratum `k` with the guard `T (inputsBelowᵉ k b)` and an
-- `Acc` on it, ordered ABOVE the g-size accessibility.  A term step
-- holds the ceiling and shrinks the size; the SHARED-SLOT step drops
-- the ceiling to the slot's own index -- which its `ok` field licenses
-- -- and lets the size go free.  That is what funds the descent into a
-- definition drawn from the slot table rather than from the term, and
-- an input's g-size being zero is why nothing smaller could.  Nothing
-- of it reaches `reducible`, which instantiates the ceiling at the
-- context's own size out of `ib-topᵉ`.
mutual
  redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t)
              (ρ : Env Γ Θ) → RedEnv ρ
            → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
            → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} (obs t) (Θ , b , ρ)
  redExpAcc (input i) ρ rρ k ok aK a = red-input i ρ k ok aK
  redExpAcc (ofᵉ ts) ρ rρ k ok aK (acc rs) κ now sched st =
    _ , subs-of , satOneShot (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl))
  redExpAcc emptyᵉ ρ rρ k ok aK a κ now sched st =
    _ , subs-empty , satOneShot []
  redExpAcc (mapᵉ {s = s} f b) ρ rρ k ok aK (acc rs) κ now sched st =
    let okf = ∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        okb = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        ((burst , sched₁ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f))))
            (map-f (_ , f , ρ) ↠ κ) now sched st
        (r , p , sat′) =
          red-push now (map-f (_ , f , ρ)) tt
            (redFnAcc f ρ rρ k okf aK
              (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))))
            κ sat sched₁ st₁ tt
    in r , subs-map d p , sat′
  redExpAcc (takeᵉ c b) ρ rρ k ok aK (acc rs) κ now sched st
    with evalWith c ρ in ceq
  ... | zero  = _ , subs-take-zero ceq , satOneShot []
  ... | suc j =
    let okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
        nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c))))
            (take-f nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (take-st (suc j)) st)
        (r , p , sat′) = red-push now (take-f nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-take-suc ceq refl d p , sat′
  redExpAcc (batchSyncᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (batchSync-f nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (batchSync-st true) st)
        ((out , sched₃ , st₂) , p , sat′) =
          red-push now (batchSync-f nid) tt tt κ sat sched₂ st₁ tt
    in _ , subs-batchSync refl d p , sat′
  redExpAcc (scanᵉ {s = s} {t = u} f z b) ρ rρ k ok aK (acc rs) κ now sched st =
    let zbe = inputsBelowᵗ k z ∧ inputsBelowᵉ k b
        okf = ∧ˡ (inputsBelowᵗ k f) zbe ok
        rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
        okz = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        okb = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        nid = freshId nodeᵏ (Sched.mint sched)
        rf  = redFnAcc f ρ rρ k okf aK
                (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵗ z + gsizeᵉ b))))
        rz  = redTmAcc z ρ rρ k okz aK
                (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b))
                                  (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
            (scan-f (_ , f , ρ) nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (cell-st (evalWith z ρ)) st)
        (r , p , sat′) =
          red-push now (scan-f (_ , f , ρ) nid) tt rf
            κ sat sched₂ st₁ (red-scan-installed (_ , f , ρ) nid rz sched st d)
    in r , subs-scan refl d p , sat′
  redExpAcc (mergeAllᵉ lim b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer mergeAllᵒ nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (mergeAll-st lim 0 [] false) st)
        (r , p , sat′) =
          red-push now (thru-outer mergeAllᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-merge-all (sub-all refl d p) , sat′
  redExpAcc (switchAllᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer switchᵒ nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (switch-st nothing false) st)
        (r , p , sat′) =
          red-push now (thru-outer switchᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-switch-all (sub-all refl d p) , sat′
  redExpAcc (exhaustAllᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer exhaustᵒ nid ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (exhaust-st false false) st)
        (r , p , sat′) =
          red-push now (thru-outer exhaustᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-exhaust-all (sub-all refl d p) , sat′
  redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) κ now sched st =
    let (r , d , sat) =
          redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
            (rs (subst (_< suc (gsizeᵉ body))
                       (sym (gsize-unfoldμ body)) ≤-refl))
            κ now sched st
    in r , subs-μ d , sat
  redExpAcc (varᵉ ()) ρ rρ k ok aK a
  redExpAcc (deferᵉ body) ρ rρ k ok aK a κ now sched st =
    _ , subs-defer refl refl refl refl , []
  redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) κ now sched st =
    let src = freshId sourceᵏ (Sched.mint sched)
        (r , d , sat) =
          redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) κ now
            (record sched
               { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
            st
    in r , subs-mint refl d , sat

  -- THE SLOT ARM, WHICH IS SEVERAL SUB-ARMS OF PROTOCOL AND ONE THAT
  -- SPENDS THE CEILING.  It mirrors the machine's own case split on
  -- the slot exactly, because the derivation it must produce is the
  -- one the machine produces; what is new is the satisfaction beside
  -- it, and at a scripted slot that is `red-data` at every value the
  -- script carries.  The ceiling's accessibility is taken apart here
  -- rather than passed on, since `toℕ i < k` is exactly what the
  -- expression face's guard reduces to at this former.
  red-input : ∀ {n} {Γ : Ctx n} {Θ} (i : Fin n) (ρ : Env Γ Θ) (k : ℕ)
            → T (toℕ i <ᵇ k) → Acc _<_ k
            → Red {Γ = Γ} (obs (lookup Γ i)) (Θ , input i , ρ)
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      with toℕ i <? lo
  ... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below) , StreamSat-spent
  ... | yes below  with Sched.slots sched i in slEq
  ...   | scripted {ok = okD} (hot async)
          with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ...     | true  = _ , subs-hot-done below slEq doneEq , StreamSat-spent
  ...     | false = _ , subs-hot-live below slEq doneEq refl , []
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | scripted {ok = okD} (cold sync []) =
        _ , subs-cold-sync below slEq , satOneShot (redDatas _ okD sync)
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | scripted {ok = okD} (cold sync (d ∷ ds)) =
        _ , subs-cold-async below slEq refl refl refl
          , satValues (redDatas _ okD sync) ∷ []
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | shared d {ok = okd} =
        red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok)) ρ
          κ below now sched slEq st

  -- THE SLOT SUB-ARM THE OTHERS ARE NOT.  A share's definition is an
  -- arbitrary expression standing in no relation to `input i`, so it
  -- cannot be reached by any descent on the TERM.  The telescope's own
  -- side condition is what reaches it instead: a slot's definition may
  -- reference only inputs STRICTLY BELOW that slot, so the definition
  -- is charged against the ceiling `toℕ i`, which the caller's
  -- accessibility has just been taken apart to supply.  The other
  -- sub-arms emit nothing, or values that are DATA by the slot's own
  -- side condition, so `red-data` closes their satisfaction outright;
  -- this one's values are the definition's, which is what the
  -- recursion returns and what the connect hands straight back.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ}
      (i : Fin n) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (ρ : Env Γ Θ)
      (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → (st : EvalSt e)
    → Σ (Stream Γ (lookup Γ i) × Sched Γ × EvalSt e) λ r →
        subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r
          × StreamSat (Red (lookup Γ i)) (proj₁ r)
  red-input-shared {Γ = Γ} i d {okd} aI ρ κ below now sched slEq st
      with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ... | true =
        _ , subs-shared {κ = κ} {below = below} slEq
              (slot-spent {κ = κ} {below = below} doneEq)
          , StreamSat-spent
  ... | false
        with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
  ...   | true =
          _ , subs-shared {κ = κ} {below = below} slEq
                (slot-join {κ = κ} {below = below} doneEq connEq refl)
            , []
  ...   | false
          with redExpAcc d []ᵉ tt (toℕ i) okd aI
                 (<-wellFounded (gsizeᵉ d))
                 (share-sink i ≤-refl) now
                 (record sched
                    { mint = setAt regᵏ (suc (freshId regᵏ (Sched.mint sched)))
                               (Sched.mint sched) })
                 (register (freshId regᵏ (Sched.mint sched)) (atSlot i)
                   (lowerFloor below κ)
                   (record st
                     { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  ...     | ((burst , sched₁ , st₂) , dv , dsat)
            with burstCompleted burst in compEq
  ...       | false =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect {κ = κ} {below = below} doneEq connEq
                      (connect-live {κ = κ} {below = below} refl dv compEq))
                , dsat
  ...       | true =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect {κ = κ} {below = below} doneEq connEq
                      (connect-died {κ = κ} {below = below} refl dv compEq))
                , dsat

  -- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
  -- former hands the recursion back to the expression face.
  redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
             (ρ : Env Γ Θ) → RedEnv ρ
           → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
           → Acc _<_ (gsizeᵗ tm) → Red u (evalWith tm ρ)
  redTmAcc (varᵗ x) ρ rρ k ok aK a = redLookup ρ rρ x
  redTmAcc unit̂     ρ rρ k ok aK a = tt
  redTmAcc (bool̂ b) ρ rρ k ok aK a = tt
  redTmAcc (nat̂ j)  ρ rρ k ok aK a = tt
  redTmAcc nilᵗ     ρ rρ k ok aK a = []
  redTmAcc (consᵗ x xs) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs))))
    ∷ redTmAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x))))
  redTmAcc (foldᵗ l z f) ρ rρ k ok aK (acc rs) =
    let zfe  = inputsBelowᵗ k z ∧ inputsBelowᵗ k f
        okl  = ∧ˡ (inputsBelowᵗ k l) zfe ok
        rest = ∧ʳ (inputsBelowᵗ k l) zfe ok
        okz  = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
        okf  = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
    in redFoldVals f ρ
         (λ {x} {ac} rx rac →
            redTmAcc f (x ∷ᵉ ac ∷ᵉ ρ) (rx , rac , rρ) k okf aK
              (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                                (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
         (redTmAcc l ρ rρ k okl aK
           (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))))
         (redTmAcc z ρ rρ k okz aK
           (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                             (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
  redTmAcc (pairᵗ x y) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y))))
    , redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x))))
  redTmAcc (fstᵗ q) ρ rρ k ok aK (acc rs) =
    proj₁ (redTmAcc q ρ rρ k ok aK (rs ≤-refl))
  redTmAcc (sndᵗ q) ρ rρ k ok aK (acc rs) =
    proj₂ (redTmAcc q ρ rρ k ok aK (rs ≤-refl))
  redTmAcc (inlᵗ x) ρ rρ k ok aK (acc rs) = redTmAcc x ρ rρ k ok aK (rs ≤-refl)
  redTmAcc (inrᵗ x) ρ rρ k ok aK (acc rs) = redTmAcc x ρ rρ k ok aK (rs ≤-refl)
  redTmAcc (caseᵗ sc l r) ρ rρ k ok aK (acc rs)
    with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
       | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
  ... | oksc | rest
    with evalWith sc ρ
       | redTmAcc sc ρ rρ k oksc aK
           (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r))))
  ... | inj₁ x | q =
    redTmAcc l (x ∷ᵉ ρ) (q , rρ) k
      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  ... | inj₂ y | q =
    redTmAcc r (y ∷ᵉ ρ) (q , rρ) k
      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  redTmAcc (ifᵗ c x y) ρ rρ k ok aK (acc rs)
    with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
  ... | rest with evalWith c ρ
  ... | true  =
    redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  ... | false =
    redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  redTmAcc (primᵗ add x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ sub x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ mul x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ eqᵖ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ eqᵘ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ ltᵖ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ notᵖ x) ρ rρ k ok aK a = tt
  redTmAcc (strmᵗ e) ρ rρ k ok aK (acc rs) = redExpAcc e ρ rρ k ok aK (rs ≤-refl)

  redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u} (ts : List (Tm Γ [] [] Θ u))
              (ρ : Env Γ Θ) → RedEnv ρ
            → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
            → Acc _<_ (gsizeᵗˢ ts)
            → All (Red u) (map (λ tm → evalWith tm ρ) ts)
  redTmsAcc []       ρ rρ k ok aK a = []
  redTmsAcc (x ∷ xs) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs))))
    ∷ redTmsAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x))))

  -- A FRAME'S CLOSURE APPLIED is the term face at one more entry, and
  -- with the environment carried rather than substituted that is all
  -- it is -- no transport, no lemma, the two statements are the same
  -- statement.
  redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Tm Γ [] [] (s ∷ Θ) u)
             (ρ : Env Γ Θ) → RedEnv ρ
           → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
           → Acc _<_ (gsizeᵗ f) → RedFn {Γ = Γ} {s = s} {u = u} (_ , f , ρ)
  redFnAcc f ρ rρ k ok aK a {v} p = redTmAcc f (v ∷ᵉ ρ) (p , rρ) k ok aK a

-- THE TOP LINE: every closure whose environment is reducible is
-- itself reducible, which is the face above with both accessibilities
-- seeded at their own subjects.
reducible : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) (ρ : Env Γ Θ)
          → RedEnv ρ → Red {Γ = Γ} (obs t) (Θ , b , ρ)
reducible b ρ rρ =
  redExpAcc b ρ rρ _ (ib-topᵉ b) (<-wellFounded _) (<-wellFounded (gsizeᵉ b))

-- AND EVERY RUNTIME VALUE IS REDUCIBLE, WHICH IS THE ONE THING A
-- CLOSURE CARRIER COSTS.  A value at observable type IS a body paired
-- with an environment, and an entry of that environment at observable
-- type is another such value -- so nothing could be claimed of the
-- pair that is not already claimed of its entries, and the descent is
-- on the VALUE rather than on the type.  This is why no site that
-- meets a stored observable has to thread a reducibility premise: it
-- re-establishes the claim here, once.
mutual
  red-val : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → Red t v
  red-val unitᵗ     v           = tt
  red-val boolᵗ     v           = tt
  red-val natᵗ      v           = tt
  red-val uniqᵗ     v           = tt
  red-val (s ×ᵗ u)  (a , b)     = red-val s a , red-val u b
  red-val (s +ᵗ u)  (inj₁ a)    = red-val s a
  red-val (s +ᵗ u)  (inj₂ b)    = red-val u b
  red-val (listᵗ s) []          = []
  red-val (listᵗ s) (x ∷ xs)    = red-val s x ∷ red-val (listᵗ s) xs
  red-val (obs u)   (Θ , b , ρ) = reducible b ρ (red-env ρ)

  red-env : ∀ {n} {Γ : Ctx n} {Θ : List Ty} (ρ : Env Γ Θ) → RedEnv ρ
  red-env []ᵉ                 = tt
  red-env (_∷ᵉ_ {s = s} v vs) = red-val s v , red-env vs
