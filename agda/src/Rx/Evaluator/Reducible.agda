------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS, WHERE THE RANK STOOD.
------------------------------------------------------------------

-- WHAT THIS REPLACES AND WHY THE REPLACEMENT IS FREE.  The builder
-- justifies its recursion with a RANK — a lexicographic triple carried
-- into every call, decreasing at three edges and inert at the rest.
-- Every open obligation on that face is one of the rank's own decrease
-- steps, which is why they are refuted rather than merely hard: the
-- quantity is being asked to fall across an unfolding that does not
-- move it.  A Girard-Tait candidate spends no such quantity.  It
-- recurses on the TYPE, which the flatteners move strictly downward
-- (`obs (obs u)` to `obs u`) and the term-structural formers do not
-- move at all — so the cases that cost the rank a decrease proof cost
-- this nothing, and the cases the rank passed through untouched are
-- exactly the ones the type leaves alone.
--
-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- expression to its subscription derivation may not mention that
-- derivation's own type in a negative position, so the candidate
-- cannot be an inductive family over the domain relation.  Defined by
-- recursion on `Ty` it never needs to be: `Red (obs u)` mentions
-- `Red u` at a strictly smaller type and `subscribeE⇓` only positively.
--
-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the scheduler and the evaluator state as plain indices with no
-- precondition, and the entry invariants the builder carries appear
-- nowhere in its conclusion — they are the rank's bookkeeping and are
-- discarded from the result.  So the candidate can demand
-- subscribability in EVERY state, which is what lets a flattener's hop
-- subscribe its inner in whatever state the outer delivery reached.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
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

open import Rx.Prim using (Id; Tick; Source; InstEmit; InstEvent; init; value; close; handoff;
  complete; hot; cold)
open import Rx.Mint using (nodeᵏ; regᵏ; freshId; setAt; next)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; _≟ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn; evalTm; evalWith; foldVals; applyFn; input; ofᵉ; emptyᵉ;
  takeᵉ; liftᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; isData; unfoldμ;
  varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  nilᵗ; consᵗ; foldᵗ;
  add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ; subΘExp; subΘTm; subΘTms; lookupEnv;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Subst-Elim using (sub-elimGᵉ)
open import Rx.Subst-Eval using (sub-evalTm; sub-applyFn)
open import Rx.Subst-Identity using (subΘ-id-exp)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; _↠_; take-f; lift-f; take-st; cell-st; thru-outer;
  mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; takeVals; takeDispatch;
  liftVals; liftDispatch; lookupNode; NodeState; installNode; oneShotBurst; memberSource;
  splitEvents; splitBurst; retagEvents; NodeId; AllOp; from-inner; consumeUsable; hasRoom;
  switchKill; thruWrap; share-sink; register; atSlot; lowerFloor; burstCompleted; sharedPlumb;
  spentBurst)
open import Rx.Evaluator.Freshness using (lookup-set; PreservedBelow)
open import Rx.Evaluator.Freshness.Preserve using (subscribeE-preserves)
open import Rx.Evaluator.Domain using (srcFrame; subscribeE⇓; pushBurst⇓; stepFrame⇓; step-lift; step-take; push-nil;
  push-cons; subs-of; subs-empty; subs-take-zero; subs-take-suc; subs-lift;
  subs-defer; subs-floor; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async;
  subs-μ; sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all; thruConsume⇓; thruWalk⇓;
  step-thru-outer; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil;
  walk-cons; subs-shared; slot-spent; slot-join; slot-connect; connect-live; connect-died)

-- An emitted EVENT carries a payload only in the `value` arm; every
-- other arm is protocol traffic and constrains nothing.
EvSat : ∀ {A : Set} → (A → Set) → InstEvent A → Set
EvSat P (init _)    = ⊤
EvSat P (value v)   = P v
EvSat P (close _ _) = ⊤
EvSat P (handoff _) = ⊤
EvSat P complete    = ⊤

-- …and a STREAM satisfies a predicate when every value it ever carries
-- does.  Taking the predicate as a parameter is what keeps `Red`'s
-- recursion structural: the recursive occurrence is `Red u` applied at
-- a strictly smaller type, not a call at the type being defined.
StreamSat : ∀ {A : Set} → (A → Set) → List (InstEmit A) → Set
StreamSat P = All (λ em → All (EvSat P) (InstEmit.events em))

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the pair
-- the whole argument turns on — a subscription derivation in every
-- state, and the guarantee that everything that derivation emits is
-- itself reducible at the element type.
Red : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → Set
Red unitᵗ    _        = ⊤
Red boolᵗ    _        = ⊤
Red natᵗ     _        = ⊤
Red uniqᵗ    _        = ⊤
Red (s ×ᵗ t) (a , b)  = Red s a × Red t b
Red (s +ᵗ t) (inj₁ a) = Red s a
Red (s +ᵗ t) (inj₂ b) = Red t b
Red (listᵗ t) xs      = All (Red t) xs
Red {Γ = Γ} (obs u) b =
  ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    subscribeE⇓ {e = e} b κ id now sched st r × StreamSat (Red u) (proj₁ r)

-- WHY A SHARE'S FAN-OUT COSTS THE CANDIDATE NOTHING, WHICH IS THE ONE
-- THING ABOUT `connect` THAT WAS NOT OBVIOUS.  A shared slot subscribes
-- its def ONCE and attaches every later reader to that one connection,
-- so the natural fear is that reducibility must be maintained as an
-- INVARIANT ON STORED STATE — everything a share is holding for its
-- next attacher would have to be reducible, and every step would owe
-- that invariant's preservation.  Nothing of the kind is owed, because
-- the fan-out carries NO PAYLOAD: a late reader's arm emits a bare
-- registration, a spent slot's arm emits a registration and its close,
-- and the only arm carrying values is the one that subscribes the def —
-- whose values are the def's, which is the induction hypothesis.  The
-- semantic fact underneath is that this share does not replay, so there
-- is nothing stored for the invariant to be about.

-- A SPENT SLOT'S BURST is registration traffic and a completion, so
-- every predicate holds of it for want of anything to hold of.
StreamSat-spent : ∀ {A : Set} {P : A → Set} (src : Source) (id : Id)
                → StreamSat P (spentBurst {A} src id)
StreamSat-spent src id = (tt ∷ tt ∷ tt ∷ []) ∷ []

-- AND THE FAN-OUT RETAGS ITS EMITS WITHOUT TOUCHING THEIR EVENTS, so
-- whatever held of the def's burst still holds of what the readers see.
StreamSat-plumb : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} (str : Stream Γ u)
                → StreamSat P str → StreamSat P (sharedPlumb str)
StreamSat-plumb []       []       = []
StreamSat-plumb (x ∷ xs) (q ∷ qs) = q ∷ StreamSat-plumb xs qs

-- PUSHING A BURST THROUGH A FRAME, WITH THE CANDIDATE CARRIED ACROSS.
-- The three transformer arms all have the same two-step shape — run the
-- source, then push what it emitted through this frame — so the second
-- step is one obligation stated once rather than three.
RedPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
        → Id → Tick → Frame Γ s u → Path Γ lo u t
        → Stream Γ s → Sched Γ → EvalSt e → Set
RedPush {Γ = Γ} {e = e} {u = u} id now f κ burst sched st =
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    pushBurst⇓ {e = e} id now f κ burst sched st r × StreamSat (Red u) (proj₁ r)

-- A MAPPING FRAME APPLIES ITS FUNCTION TO EVERY ARRIVING VALUE, so
-- what it produces is reducible exactly when the function sends
-- reducible to reducible.  That is the only thing a frame wants from
-- the term face, and it has to be stated as a HYPOTHESIS rather than
-- reached by a call: the fundamental theorem at terms is a member of
-- the recursion at the foot of this module, so a walk declared above
-- it cannot name it.
RedFn : ∀ {n} {Γ : Ctx n} {s u} → Fn Γ [] [] [] s u → Set
RedFn {Γ = Γ} {s = s} {u = u} fn =
  ∀ {v : Val Γ s} → Red s v → Red u (applyFn fn v)

-- A FOLD PRESERVES THE CANDIDATE WHEN ITS STEP DOES, AND THE STEP IS A
-- HYPOTHESIS FOR THE REASON `RedFn`'s IS: the fundamental theorem at
-- terms is a member of the recursion at the foot of this module, so a
-- walk declared above it cannot call it.  What is new is the recursion
-- itself — every other former's value is a function of its subterms'
-- values, so congruence discharges it, while a fold runs its step once
-- per ELEMENT and the candidate has to be re-established at each.
redFoldVals : ∀ {n} {Γ : Ctx n} {Θ s u}
              (f : Tm Γ [] [] (s ∷ u ∷ Θ) u) (σ : All (Val Γ) Θ)
            → (∀ {x : Val Γ s} {a : Val Γ u} → Red s x → Red u a
                 → Red u (evalWith f (x ∷ a ∷ σ)))
            → ∀ {xs : List (Val Γ s)} → All (Red s) xs
            → ∀ {a : Val Γ u} → Red u a
            → Red u (foldVals f σ xs a)
redFoldVals f σ step []       ra = ra
redFoldVals f σ step (p ∷ ps) ra = redFoldVals f σ step ps (step p ra)

-- WHAT A FRAME'S OWN NODE MUST HOLD, AND IT IS ONLY EVER THE FOLD
-- THAT ASKS.  The node census says four of the five frames read a
-- store that carries no payload -- a count, a flag, an identifier, a
-- queue nothing in a subscribe reads back -- so their obligation is
-- the trivial one and costs a `tt` at every site.  The fold's node
-- holds a VALUE, and the value it holds is what leaves the frame, so
-- this is where the candidate has to already be true of the store.
-- Stating it as a predicate on the state rather than as a hypothesis
-- on the fold's own statement is what keeps it PRESERVED rather than
-- merely assumed: the step face re-establishes it at the state it
-- hands back, and the writeback is exactly the fold applied to two
-- things the push already has.
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
RedNode {Γ = Γ} (lift-f fn nid) st =
  ∀ {w} {a : Val Γ w}
  → lookupNode nid (EvalSt.nodes st) ≡ just (cell-st a) → Red w a
RedNode (take-f nid)                st = ⊤
RedNode (from-inner op allNid inst) st = ⊤
RedNode (thru-outer op nid)         st = ⊤

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's function is a term with one
-- entry bound, so the fundamental theorem at terms has to be stated
-- under a substitution rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} {Θ : List Ty} → All (Val Γ) Θ → Set
RedEnv []                    = ⊤
RedEnv (_∷_ {x = t} v vs)    = Red t v × RedEnv vs

-- THE SAME CLAIM ONE BATCH DOWN: a frame, the values that arrived at
-- it, and the candidate carried across to what leaves.  The push above
-- walks a burst emit by emit, so it is stated over a stream while this
-- is stated over one list, which is where every operator's own
-- machinery sits.
RedStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
        → Id → Tick → Frame Γ s u → Path Γ lo u t
        → List (Val Γ s) → Bool → Sched Γ → EvalSt e → Set
RedStep {Γ = Γ} {t = t} {e = e} {u = u} id now f κ vals fin sched st =
  Σ (List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e) λ r →
    stepFrame⇓ {e = e} id now f κ vals fin sched st r × All (Red u) (proj₁ r)
      × RedNode f (proj₂ (proj₂ (proj₂ (proj₂ r))))

-- SUBSTITUTION COMMUTES WITH THE PEEL, which is the price of carrying
-- the environment rather than applying it: closing against the
-- environment and then peeling agrees with peeling under it.  This is
-- the only point the face still reaches one on the EXPRESSION side --
-- the readings on the TERM side are `evalTm` and `applyFn`, one
-- `evalWith` at two telescopes, so they are one statement rather than
-- two obligations, and it is proven.
--
-- THE PEEL IS THE ELIMINATOR AT THE EMPTY LOCAL TELESCOPE, and that is
-- the whole of this body: the general statement is the only one whose
-- induction can run, and at the empty telescope its transport is
-- `refl`, so the instance reduces to the equation the walk spends.
sub-unfoldμ : ∀ {n} {Γ : Ctx n} {Θ t} (body : Exp Γ (t ∷ []) [] Θ t)
              (σ : All (Val Γ) Θ)
            → subΘExp [] σ (unfoldμ body) ≡ unfoldμ (subΘExp [] σ body)
sub-unfoldμ body σ = sub-elimGᵉ [] (here refl) (μᵉ body) σ body

-- A SPLIT TAKES THE VALUE COLUMN OUT OF A BURST, and nothing else,
-- so whatever held of every value the burst carried holds of every
-- value the split hands back.  The other four event formers carry no
-- payload, so their satisfaction is decided by the former alone and
-- they simply leave the column.
satSplitEvents : ∀ {n} {Γ : Ctx n} {u} {A : Set} {P : Val Γ u → Set}
                 (es : List (InstEvent (Val Γ u))) → All (EvSat P) es
               → All P (proj₁ (splitEvents {A = A} es))
satSplitEvents []                []       = []
satSplitEvents (init _     ∷ es) (_ ∷ ps) = satSplitEvents es ps
satSplitEvents (value _    ∷ es) (p ∷ ps) = p ∷ satSplitEvents es ps
satSplitEvents (close _ _  ∷ es) (_ ∷ ps) = satSplitEvents es ps
satSplitEvents (handoff _  ∷ es) (_ ∷ ps) = satSplitEvents es ps
satSplitEvents (complete   ∷ es) (_ ∷ ps) = satSplitEvents es ps

satSplitBurst : ∀ {n} {Γ : Ctx n} {u} {A : Set} {P : Val Γ u → Set}
                (str : Stream Γ u) → StreamSat P str
              → All P (proj₁ (splitBurst {A = A} str))
satSplitBurst []         []       = []
satSplitBurst (em ∷ ems) (q ∷ qs) =
  ++⁺ (satSplitEvents (InstEmit.events em) q) (satSplitBurst ems qs)

-- AND THE WRAP AROUND THE WALK NEVER TOUCHES THAT COLUMN.  What it
-- decides is whether the operator is finished and what its node then
-- holds, both of which the candidate is silent about; the values pass
-- through every arm unchanged.  Spelling the arms out is the price of
-- the machine reading its own store: a catch-all in the definition
-- does not reduce against a catch-all in a proof.
thruWrap-vals : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                (op : AllOp) (nid : NodeId) (fin : Bool)
                {vs : List (Val Γ u)} {bs : List (InstEvent (Val Γ t))}
                {sched′ : Sched Γ} {st′ : EvalSt e}
              → proj₁ (thruWrap {e = e} op nid fin (vs , bs , sched′ , st′)) ≡ vs
thruWrap-vals op nid false = refl
thruWrap-vals mergeAllᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals switchᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals exhaustᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
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
           → AllOp → NodeId → Path Γ lo u t → Id → Tick
           → Val Γ (obs u) → Sched Γ → EvalSt e → Set
RedConsume {Γ = Γ} {t = t} {e = e} {u = u} op nid κ id now o sched st =
  Σ (List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) λ r →
    thruConsume⇓ {e = e} op nid κ id now o sched st r × All (Red u) (proj₁ r)

RedWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
        → AllOp → NodeId → Path Γ lo u t → Id → Tick
        → List (Val Γ (obs u)) → Sched Γ → EvalSt e → Set
RedWalk {Γ = Γ} {t = t} {e = e} {u = u} op nid κ id now vals sched st =
  Σ (List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) λ r →
    thruWalk⇓ {e = e} op nid κ id now vals sched st r × All (Red u) (proj₁ r)

-- THE HOP IS PAID FOR BY THE ARRIVING VALUE'S OWN CANDIDATE, which is
-- what makes this a body rather than a leaf.  A subscribe arm hands
-- the observable down at a `from-inner` frame and splits what comes
-- back; the candidate quantifies over every schedule and every state,
-- so the freshly-counted schedule this arm builds is one of them by
-- construction and no invariant is threaded.  Every OTHER arm emits
-- nothing at all -- a refused arrival is queued, an unusable store
-- collapses -- so its column is satisfied for want of anything to
-- hold of.
red-consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
              (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
              (id : Id) (now : Tick) {o : Val Γ (obs u)} → Red (obs u) o
            → (sched : Sched Γ) (st : EvalSt e)
            → RedConsume {e = e} op nid κ id now o sched st
red-consume {u = u} mergeAllᵒ nid κ id now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (take-st _) =
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
                ro (from-inner mergeAllᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠ κ) id now
                   (record sched { mint = next nodeᵏ (Sched.mint sched) }) st
          in _ , consume-all-sub eq eqr (inner refl d refl)
               , satSplitBurst burst ss

red-consume {u = u} switchᵒ nid κ id now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (exhaust-st _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (closes , sched₁ , st₁) =
        let ((burst , _ , _) , d , ss) =
              ro (from-inner switchᵒ nid (freshId nodeᵏ (Sched.mint sched₁)) ↠ κ) id now
                 (record sched₁ { mint = next nodeᵏ (Sched.mint sched₁) }) st₁
        in _ , consume-switch-sub eq eqk (inner refl d refl)
             , satSplitBurst burst ss

red-consume {u = u} exhaustᵒ nid κ id now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (switch-st _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st true _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st false od) =
      let ((burst , _ , _) , d , ss) =
            ro (from-inner exhaustᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠ κ) id now
               (record sched { mint = next nodeᵏ (Sched.mint sched) }) st
      in _ , consume-exhaust-sub eq (inner refl d refl)
           , satSplitBurst burst ss

-- THE WALK IS THE CONSUME THREADED, and the column it returns is the
-- concatenation of the columns each arrival produced.
red-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
           (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
           (id : Id) (now : Tick) {vals : List (Val Γ (obs u))}
         → All (Red (obs u)) vals
         → (sched : Sched Γ) (st : EvalSt e)
         → RedWalk {e = e} op nid κ id now vals sched st
red-walk op nid κ id now []       sched st = _ , walk-nil , []
red-walk op nid κ id now (r ∷ rs) sched st =
  let ((_ , _ , sched₁ , st₁) , c , rv) = red-consume op nid κ id now r sched st
      (_ , w , rv′) = red-walk op nid κ id now rs sched₁ st₁
  in _ , walk-cons c w , ++⁺ rv rv′

-- THE FLATTENING WALK, AND THE NODE IT READS OWES NOTHING.  Every
-- value it produces is an inner subscribed out of the arriving batch,
-- and the census at `NodeState` says the nodes it consults carry no
-- payload to confuse that -- so this frame's node obligation is the
-- trivial one and the whole content is the value column.
--
-- AND THE QUEUE IT PUSHES INTO IS WRITE-ONLY FROM HERE, WHICH IS WHY
-- NO STORE INVARIANT IS OWED AT ALL.  A refused arrival is enqueued
-- and never read back within a subscribe: the read is the DRAIN,
-- which hangs off an inner's completion, and `srcFrame` says in a
-- type that a push cycle is entered only from a source former.  So
-- the entry a subscribe stores is one this face can put in and never
-- has to take out, and the carrier the census left owed is owed to
-- the instant loop instead.
red-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
           (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
           (κ : Path Γ lo u t)
           {vals : List (Val Γ (obs u))} → All (Red (obs u)) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
         → RedStep {e = e} id now (thru-outer op nid) κ vals fin sched st
red-thru id now op nid κ rv fin sched st =
  let (_ , w , rvs) = red-walk op nid κ id now rv sched st
  in _ , step-thru-outer w
       , subst (All (Red _)) (sym (thruWrap-vals op nid fin)) rvs
       , tt


-- Every protocol event carries no payload, so a burst's values are the
-- only thing to check and a burst with none is satisfied outright.
satEvents : ∀ {A : Set} {P : A → Set} {vals : List A} {rest : List (InstEvent A)}
          → All P vals → All (EvSat P) rest
          → All (EvSat P) (map value vals ++ rest)
satEvents []       ar = ar
satEvents (p ∷ ps) ar = p ∷ satEvents ps ar

satOneShot : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} {vals}
             (id : Id) (sched : Sched Γ)
           → All P vals → StreamSat P (proj₁ (oneShotBurst vals id sched))
satOneShot id sched ps = (tt ∷ satEvents ps (tt ∷ tt ∷ [])) ∷ []

-- EVERY VALUE OF A DATA TYPE IS REDUCIBLE, AND THAT IS WHY THE SLOT
-- ARM IS SHORT.  The candidate is trivial at each data former and
-- uninhabitable at `obs`, so the recursion here is the same one `Red`
-- itself runs -- it just has to be SAID, because a slot's element type
-- is `lookup Γ i` and no reduction fires on a neutral index.  What
-- carries it is the side condition every scripted slot already holds.
-- THE PRODUCT AND SUM ARMS OF `isData` GUARD ON THE LEFT FACTOR, so
-- the witness has to be taken apart before either side can be used.
-- It sits ABOVE rather than between the signature and the clauses
-- because this module has NO multi-member block and that is worth
-- keeping: the dev loop stubs such a block, so a module without one is
-- checked for real, termination included.
T-if : ∀ (b c : Bool) → T (if b then c else false) → T b × T c
T-if true  c ok = tt , ok
T-if false c ()

red-data : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) → (v : Val Γ u)
         → Red {Γ = Γ} u v
red-data unitᵗ    _  _       = tt
red-data natᵗ     _  _       = tt
red-data uniqᵗ    _  _       = tt
red-data boolᵗ    _  _       = tt
red-data (s ×ᵗ t) ok (a , b) =
  let (o₁ , o₂) = T-if (isData s) (isData t) ok
  in red-data s o₁ a , red-data t o₂ b
red-data (s +ᵗ t) ok (inj₁ a) = red-data s (proj₁ (T-if (isData s) (isData t) ok)) a
red-data (s +ᵗ t) ok (inj₂ b) = red-data t (proj₂ (T-if (isData s) (isData t) ok)) b
red-data (listᵗ t) ok xs      = universal (red-data t ok) xs
red-data (obs u)  () _

redDatas : ∀ {n} {Γ : Ctx n} (u : Ty) → T (isData u) → (vs : List (Val Γ u))
         → All (Red {Γ = Γ} u) vs
redDatas u ok []       = []
redDatas u ok (v ∷ vs) = red-data u ok v ∷ redDatas u ok vs

-- The cold-with-a-tail arm emits its synchronous values with nothing
-- after them, so it wants the values alone rather than `satEvents`'
-- append.
satValues : ∀ {A : Set} {P : A → Set} {vals : List A}
          → All P vals → All (EvSat P) (map value vals)
satValues []       = []
satValues (p ∷ ps) = p ∷ satValues ps

-- AND A FRAME OWES IT WHEREVER IT APPLIES ONE, WHICH IS TWO OF THE
-- FIVE.  The mapping frame applies its function to what arrived; the
-- fold applies its own to the pair of the stored accumulator and what
-- arrived, so it owes the same thing -- what it additionally needs,
-- the first component of that pair being reducible, is the store
-- obligation beside this one rather than anything about the function.
RedFrame : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
RedFrame (lift-f fn nid)             = RedFn fn
RedFrame (take-f nid)                = ⊤
RedFrame (from-inner op allNid inst) = ⊤
RedFrame (thru-outer op nid)         = ⊤


-- A TRUNCATION CANNOT INVENT A VALUE, WHICH IS WHY THE TAKE ARM NEEDS
-- NOTHING FROM THE STORE.  The node a take installs holds a COUNT, and
-- the dispatch's value column is a prefix of the burst it was handed --
-- on the cut path and the non-cut path alike, and at a stuck lookup the
-- column is empty.  So the arriving candidates are the departing ones
-- and the store decides only HOW MANY survive.  This is the contrast
-- that pins what a scan's accumulator is actually missing: that node
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
redTakeDispatch nid fin sched st (just (cell-st _))        rv = []
redTakeDispatch nid fin sched st (just (mergeAll-st _ _ _ _)) rv = []
redTakeDispatch nid fin sched st (just (switch-st _ _))    rv = []
redTakeDispatch nid fin sched st (just (exhaust-st _ _))   rv = []
redTakeDispatch nid fin sched st nothing                   rv = []

red-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
           (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ lo s t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
         → RedStep {e = e} id now (take-f nid) κ vals fin sched st
red-take id now nid κ rv fin sched st =
  _ , step-take
    , redTakeDispatch nid fin sched st (lookupNode nid (EvalSt.nodes st)) rv
    , tt

-- the node read back is the one written, so its payload is that payload
tie-cell : ∀ {n} {Γ : Ctx n} {w w′} {x : Val Γ w} {y : Val Γ w′}
         → just (cell-st x) ≡ just (cell-st y) → Red w x → Red w′ y
tie-cell refl r = r

-- AND THE ONE THING THE CELL'S NODE OBLIGATION CANNOT ESTABLISH FOR
-- ITSELF: that the state installed just before a subscription is the
-- one still standing when the push happens.  A node is keyed by an
-- identifier drawn from the schedule's own counter, the former installs
-- at the counter's current value and subscribes with it advanced, and
-- a subscription writes no node below the counter it started at -- so
-- the carried state is untouched for structural reasons rather than by
-- any property of the candidate.  The floor spent here is the advanced
-- counter itself, which is the tightest one available and the only one
-- under which the former's own node is strictly below.

-- THE LIFTED STEP HANDS ITS WHOLE BATCH TO ONE APPLICATION, so the
-- two halves come back already paired: the function's own candidate,
-- read at a product whose components are the carried cell and the
-- arriving list, IS the candidate at the outgoing list paired with
-- the candidate at what gets written back.  Nothing is walked here
-- because nothing is threaded.
redLiftVals : ∀ {n} {Γ : Ctx n} {s u w}
              (fn : Fn Γ [] [] [] (w ×ᵗ listᵗ s) (w ×ᵗ listᵗ u)) → RedFn fn
            → {a : Val Γ w} → Red w a
            → {vals : List (Val Γ s)} → All (Red s) vals
            → All (Red u) (proj₁ (liftVals fn a vals))
              × Red w (proj₂ (liftVals fn a vals))
redLiftVals fn rf ra rv = proj₂ (rf (ra , rv)) , proj₁ (rf (ra , rv))

-- the installation argument, spent at the cell the former writes
red-lift-installed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w lo}
           (fn : Fn Γ [] [] [] (w ×ᵗ listᵗ s) (w ×ᵗ listᵗ u)) (nid : NodeId)
           {a : Val Γ w} → Red w a
         → {b : Closed Γ s} {κ : Path Γ lo u t} {id : Id} {now : Tick}
         → (sched : Sched Γ) (st : EvalSt e)
         → {sched₂ : Sched Γ} {st₁ : EvalSt e} {burst : Stream Γ s}
         → subscribeE⇓ {e = e} b (lift-f fn nid ↠ κ) id now
             (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
             (installNode nid (cell-st a) st)
             (burst , sched₂ , st₁)
         → RedNode {e = e} (lift-f fn nid) st₁
red-lift-installed {e = e} fn nid {a} ra sched st d eq =
  tie-cell (trans (sym (trans (PreservedBelow.below
                                 (subscribeE-preserves (suc nid) ≤-refl d)
                                 nid ≤-refl)
                              (lookup-set nid (cell-st a) (EvalSt.nodes st))))
                  eq)
           ra

redLiftDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w}
                  (fn : Fn Γ [] [] [] (w ×ᵗ listᵗ s) (w ×ᵗ listᵗ u)) (nid : NodeId)
                  {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                → lookupNode nid (EvalSt.nodes st) ≡ m
                → RedNode {e = e} (lift-f fn nid) st → RedFn fn → All (Red s) vals
                → All (Red u) (proj₁ (liftDispatch {e = e} fn nid vals fin sched st m))
                  × RedNode {e = e} (lift-f fn nid)
                      (proj₂ (proj₂ (proj₂ (proj₂
                        (liftDispatch {e = e} fn nid vals fin sched st m)))))
redLiftDispatch {w = w} fn nid {vals} fin sched st (just (cell-st {v} a)) eq rn rf rv
  with v ≟ᵗ w
... | no  _    = [] , rn
... | yes refl =
      let (outs , last) = redLiftVals fn rf (rn eq) rv
      in outs , λ eq′ → tie-cell (trans (sym (lookup-set nid
                                    (cell-st (proj₂ (liftVals fn a vals)))
                                    (EvalSt.nodes st)))
                                  eq′)
                          last
redLiftDispatch fn nid fin sched st nothing                    eq rn rf rv = [] , rn
redLiftDispatch fn nid fin sched st (just (take-st _))         eq rn rf rv = [] , rn
redLiftDispatch fn nid fin sched st (just (mergeAll-st _ _ _ _)) eq rn rf rv = [] , rn
redLiftDispatch fn nid fin sched st (just (switch-st _ _))     eq rn rf rv = [] , rn
redLiftDispatch fn nid fin sched st (just (exhaust-st _ _))    eq rn rf rv = [] , rn

red-lift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w lo}
           (id : Id) (now : Tick)
           (fn : Fn Γ [] [] [] (w ×ᵗ listᵗ s) (w ×ᵗ listᵗ u)) (nid : NodeId)
           (κ : Path Γ lo u t) → RedFn fn
         → {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
         → (sched : Sched Γ) (st : EvalSt e)
         → RedNode {e = e} (lift-f fn nid) st
         → RedStep {e = e} id now (lift-f fn nid) κ vals fin sched st
red-lift id now fn nid κ rf rv fin sched st rn =
  let (rvs , rn′) = redLiftDispatch fn nid fin sched st
                       (lookupNode nid (EvalSt.nodes st)) refl rn rf rv
  in _ , step-lift , rvs , rn′

-- STEPPING ONE FRAME, DISPATCHED ON THE FRAME, AND ONLY EVER A SOURCE
-- FRAME.  The mapping arm is a body because nothing about it is
-- stateful; the other three each read a node this face installed
-- earlier, which is the one thing the candidate's quantification over
-- every state does not hand back.  The fourth frame is not answered
-- for at all: `srcFrame` says in a type that a push cycle is only
-- entered from a source former, so the inner's own frame arrives here
-- never, and a leaf stated for it would have been a claim about a
-- run this face cannot reach.
red-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (id : Id) (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedStep {e = e} id now f κ vals fin sched st
red-step id now (lift-f fn nid) sv rf κ rv fin sched st rn =
  red-lift id now fn nid κ rf rv fin sched st rn
red-step id now (take-f nid) sv rf κ rv fin sched st rn =
  red-take id now nid κ rv fin sched st
red-step id now (from-inner op allNid inst) () rf κ rv fin sched st rn
red-step id now (thru-outer op nid) sv rf κ rv fin sched st rn =
  red-thru id now op nid κ rv fin sched st

-- WALKING A BURST IS BOOKKEEPING, AND SEPARATING IT FROM THE STEP IS
-- WHAT MAKES THAT VISIBLE.  An emit splits into the values a frame
-- must act on and the protocol traffic that flows past it untouched,
-- and what comes back out is the step's own values plus retagged
-- plumbing.  Only the first of those can fail the candidate: the
-- other three carry no payload, so their satisfaction is decided by
-- the event former alone.
satRetag : ∀ {A B : Set} {P : B → Set} (es : List (InstEvent A))
         → All (EvSat P) (retagEvents {A = A} {B = B} es)
satRetag []                = []
satRetag (init _    ∷ es) = tt ∷ satRetag es
satRetag (value _   ∷ es) = satRetag es
satRetag (close _ _ ∷ es) = tt ∷ satRetag es
satRetag (handoff _ ∷ es) = tt ∷ satRetag es
satRetag (complete  ∷ es) = tt ∷ satRetag es

splitVals : ∀ {n} {Γ : Ctx n} {u} {A : Set} {P : Val Γ u → Set}
            (es : List (InstEvent (Val Γ u)))
          → All (EvSat P) es
          → All P (proj₁ (splitEvents {A = A} es))
splitVals []                []       = []
splitVals (init _    ∷ es) (_ ∷ ps) = splitVals es ps
splitVals (value _   ∷ es) (p ∷ ps) = p ∷ splitVals es ps
splitVals (close _ _ ∷ es) (_ ∷ ps) = splitVals es ps
splitVals (handoff _ ∷ es) (_ ∷ ps) = splitVals es ps
splitVals (complete  ∷ es) (_ ∷ ps) = splitVals es ps

splitProt : ∀ {n} {Γ : Ctx n} {u} {A : Set} {P : A → Set}
            (es : List (InstEvent (Val Γ u)))
          → All (EvSat P) (proj₁ (proj₂ (splitEvents {A = A} es)))
splitProt []                = []
splitProt (init _    ∷ es) = tt ∷ splitProt es
splitProt (value _   ∷ es) = splitProt es
splitProt (close _ _ ∷ es) = tt ∷ splitProt es
splitProt (handoff _ ∷ es) = tt ∷ splitProt es
splitProt (complete  ∷ es) = splitProt es

-- a frame's completion flag becomes at most one protocol event
satFin : ∀ {A : Set} {P : A → Set} (b : Bool)
       → All (EvSat P) (if b then complete ∷ [] else [])
satFin true  = tt ∷ []
satFin false = []

-- PUSHING A BURST THROUGH A FRAME IS A WALK, AND THE WALK IS A BODY.
-- Each emit is split, stepped and reassembled; the candidate travels
-- on the values alone, which is why the reassembly costs three
-- appends of protocol traffic and one real obligation.
red-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (id : Id) (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {burst : Stream Γ s} → StreamSat (Red s) burst
         → (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedPush {e = e} id now f κ burst sched st
red-push id now f sv rf κ {[]}      []       sched st rn = _ , push-nil , []
red-push id now f sv rf κ {em ∷ ems} (p ∷ ps) sched st rn =
  let ((vals′ , evs , fin′ , sched₁ , st₁) , d , rv , rn₁) =
        red-step id now f sv rf κ (splitVals (InstEmit.events em) p)
          (proj₂ (proj₂ (splitEvents (InstEmit.events em)))) sched st rn
      ((rest , sched₂ , st₂) , dr , sr) = red-push id now f sv rf κ ps sched₁ st₁ rn₁
  in _ , push-cons refl d dr
       , ++⁺ (splitProt (InstEmit.events em))
             (++⁺ (satRetag evs) (satEvents rv (satFin fin′))) ∷ sr

-- THE BODY, AND WHAT PAYS FOR IT.  The expression face and the term
-- face are ONE recursion: a term embeds an expression and an operator
-- carries terms, so neither can be a leaf beside the other without
-- claiming the whole theorem.  Both recurse on the ACCESSIBILITY of
-- the guarded size, which counts an operator's spine and the terms it
-- carries and stops at the gate; every call below hands on a strictly
-- smaller size, the fixpoint arm included.
--
-- AND THE ENVIRONMENT IS CARRIED, NOT APPLIED, WHICH IS WHAT THE SIZE
-- COSTS.  An entry at observable type is a whole expression, so the
-- substituted form is unbounded against the syntax that binds it and
-- no measure reaches it.  So the expression face is stated at a raw
-- body under a reducible substitution and concludes about the CLOSED
-- form, and the measure is read off the raw body alone.
--
-- THE ONE ARM WITH NO SUBTERM IS THE μ, AND THE SYNTAX PAYS FOR IT.
-- An unfolding is no subterm of its fixpoint and sits at the same
-- type, so neither the syntax nor the candidate's own type recursion
-- reaches it.  What does is the size: the μ former spends a unit, the
-- gate the μ variable must sit behind is where the size stops looking,
-- and the unfolding therefore has exactly the size the body had.
redLookup : ∀ {n} {Γ : Ctx n} {Θ t} (σ : All (Val Γ) Θ) → RedEnv σ
          → (x : t ∈ Θ) → Red t (lookupEnv σ x)
redLookup (v ∷ vs) (p , ps) (here refl) = p
redLookup (v ∷ vs) (p , ps) (there x)   = redLookup vs ps x

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
              (σ : All (Val Γ) Θ) → RedEnv σ
            → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
            → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} (obs t) (subΘExp [] σ b)
  redExpAcc (input i) σ rσ k ok aK a κ id now sched st =
    red-input i k ok aK κ id now sched st
  redExpAcc (ofᵉ ts) σ rσ k ok aK (acc rs) κ id now sched st =
    _ , subs-of refl
      , satOneShot id sched (redTmsAcc ts σ rσ k ok aK (rs ≤-refl))
  redExpAcc emptyᵉ σ rσ k ok aK a κ id now sched st =
    _ , subs-empty refl , satOneShot id sched []
  redExpAcc (takeᵉ c b) σ rσ k ok aK (acc rs) κ id now sched st
    with evalTm (subΘTm [] σ c) in ceq
  ... | zero  = _ , subs-take-zero ceq refl , satOneShot id sched []
  ... | suc j =
    let nid = freshId nodeᵏ (Sched.mint sched)
        okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c))))
            (take-f nid ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (take-st (suc j)) st)
        (r , p , sat′) = red-push id now (take-f nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-take-suc ceq refl d p , sat′
  redExpAcc (liftᵉ {s = s} {u = w} f z b) σ rσ k ok aK (acc rs) κ id now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        fn  = subΘTm ((w ×ᵗ listᵗ s) ∷ []) σ f
        zbe = inputsBelowᵗ k z ∧ inputsBelowᵉ k b
        okf = ∧ˡ (inputsBelowᵗ k f) zbe ok
        rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
        okz = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        okb = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        rf  = redFnAcc f σ rσ k okf aK
                (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵗ z + gsizeᵉ b))))
        rz  = subst (Red w) (sym (sub-evalTm z σ))
                (redTmAcc z σ rσ k okz aK
                  (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b))
                                    (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f))))))
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
            (lift-f fn nid ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (cell-st (evalTm (subΘTm [] σ z))) st)
        (r , p , sat′) =
          red-push id now (lift-f fn nid) tt rf
            κ sat sched₂ st₁ (red-lift-installed fn nid rz sched st d)
    in r , subs-lift refl d p , sat′
  redExpAcc (mergeAllᵉ lim b) σ rσ k ok aK (acc rs) κ id now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b σ rσ k ok aK (rs ≤-refl)
            (thru-outer mergeAllᵒ nid ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (mergeAll-st lim 0 [] false) st)
        (r , p , sat′) =
          red-push id now (thru-outer mergeAllᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-merge-all (sub-all refl d p) , sat′
  redExpAcc (switchAllᵉ b) σ rσ k ok aK (acc rs) κ id now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b σ rσ k ok aK (rs ≤-refl)
            (thru-outer switchᵒ nid ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (switch-st nothing false) st)
        (r , p , sat′) =
          red-push id now (thru-outer switchᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-switch-all (sub-all refl d p) , sat′
  redExpAcc (exhaustAllᵉ b) σ rσ k ok aK (acc rs) κ id now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b σ rσ k ok aK (rs ≤-refl)
            (thru-outer exhaustᵒ nid ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (exhaust-st false false) st)
        (r , p , sat′) =
          red-push id now (thru-outer exhaustᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-exhaust-all (sub-all refl d p) , sat′
  redExpAcc (μᵉ body) σ rσ k ok aK (acc rs) κ id now sched st =
    let ih = subst (Red (obs _)) (sub-unfoldμ body σ)
               (redExpAcc (unfoldμ body) σ rσ k (ib-unfoldμ k body ok) aK
                 (rs (subst (_< suc (gsizeᵉ body))
                            (sym (gsize-unfoldμ body)) ≤-refl)))
        (r , d , sat) = ih κ id now sched st
    in r , subs-μ d , sat
  redExpAcc (varᵉ ()) σ rσ k ok aK a
  redExpAcc (deferᵉ body) σ rσ k ok aK a κ id now sched st =
    _ , subs-defer refl refl refl refl , (tt ∷ []) ∷ []

  -- THE SLOT ARM, WHICH IS FIVE SUB-ARMS OF PROTOCOL AND ONE THAT
  -- SPENDS THE CEILING.  It mirrors the builder's own case split on
  -- the slot exactly, because the derivation it must produce is the
  -- one the builder produces; what is new is the satisfaction beside
  -- it, and at a scripted slot that is `red-data` at every value the
  -- script carries.  The ceiling's accessibility is taken apart here
  -- rather than passed on, since `toℕ i < k` is exactly what the
  -- expression face's guard reduces to at this former.
  red-input : ∀ {n} {Γ : Ctx n} (i : Fin n) (k : ℕ) → T (toℕ i <ᵇ k)
            → Acc _<_ k → Red {Γ = Γ} (obs (lookup Γ i)) (input i)
  red-input {Γ = Γ} i k ok (acc rsK) {lo = lo} κ id now sched st
      with toℕ i <? lo
  ... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below) , (tt ∷ tt ∷ tt ∷ []) ∷ []
  ... | yes below  with Sched.slots sched i in slEq
  ...   | scripted {ok = okD} (hot async)
          with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ...     | true  = _ , subs-hot-done below slEq doneEq , (tt ∷ tt ∷ tt ∷ []) ∷ []
  ...     | false = _ , subs-hot-live below slEq doneEq refl , (tt ∷ []) ∷ []
  red-input {Γ = Γ} i k ok (acc rsK) {lo = lo} κ id now sched st
      | yes below | scripted {ok = okD} (cold sync []) =
        _ , subs-cold-sync below slEq refl
          , satOneShot id sched (redDatas _ okD sync)
  red-input {Γ = Γ} i k ok (acc rsK) {lo = lo} κ id now sched st
      | yes below | scripted {ok = okD} (cold sync (v ∷ vs)) =
        _ , subs-cold-async below slEq refl refl refl
          , (tt ∷ satValues (redDatas _ okD sync)) ∷ []
  red-input {Γ = Γ} i k ok (acc rsK) {lo = lo} κ id now sched st
      | yes below | shared d {ok = okd} =
        red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok))
          κ below id now sched slEq st

  -- THE SIXTH SLOT SUB-ARM, WHICH IS THE ONE THE OTHER FIVE ARE NOT.
  -- A share's definition is an arbitrary term standing in no relation
  -- to `input i`, so it cannot be reached by any descent on the TERM.
  -- The telescope's own side condition is what reaches it instead: a
  -- slot's definition may reference only inputs STRICTLY BELOW that
  -- slot, so the definition is charged against the ceiling `toℕ i`,
  -- which the caller's accessibility has just been taken apart to
  -- supply.  The other five sub-arms emit protocol and values that are
  -- DATA by the slot's own side condition, so `red-data` closes their
  -- satisfaction outright; this one's values are the definition's,
  -- which is what the recursion returns, retagged by the fan-out.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
      (i : Fin n) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (id : Id) (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → (st : EvalSt e)
    → Σ (Stream Γ (lookup Γ i) × Sched Γ × EvalSt e) λ r →
        subscribeE⇓ {e = e} (input i) κ id now sched st r
          × StreamSat (Red (lookup Γ i)) (proj₁ r)
  red-input-shared {Γ = Γ} i d {okd} aI κ below id now sched slEq st
      with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ... | true =
        _ , subs-shared {κ = κ} {below = below} slEq
              (slot-spent {κ = κ} {below = below} doneEq)
          , StreamSat-spent (toℕ i) id
  ... | false
        with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
  ...   | true =
          _ , subs-shared {κ = κ} {below = below} slEq
                (slot-join {κ = κ} {below = below} doneEq connEq refl)
            , (tt ∷ []) ∷ []
  ...   | false
          with subst (Red (obs (lookup Γ i))) (subΘ-id-exp d)
                 (redExpAcc d [] tt (toℕ i) okd aI
                   (<-wellFounded (gsizeᵉ d)))
                 (share-sink i ≤-refl) id now
                 (record sched { mint = next regᵏ (Sched.mint sched) })
                 (register (freshId regᵏ (Sched.mint sched))
                   (atSlot i) (lowerFloor below κ)
                   (record st
                     { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  ...     | ((burst , sched₁ , st₂) , dv , dsat)
            with burstCompleted burst in compEq
  ...       | false =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect doneEq connEq
                      (connect-live {κ = κ} {below = below} refl dv compEq))
                , (tt ∷ []) ∷ StreamSat-plumb burst dsat
  ...       | true =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect doneEq connEq
                      (connect-died {κ = κ} {below = below} refl dv compEq))
                , (tt ∷ tt ∷ []) ∷ StreamSat-plumb burst dsat

  -- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
  -- former hands the recursion back to the expression face.
  redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
             (σ : All (Val Γ) Θ) → RedEnv σ
           → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
           → Acc _<_ (gsizeᵗ tm) → Red u (evalWith tm σ)
  redTmAcc (varᵗ x) σ rσ k ok aK a = redLookup σ rσ x
  redTmAcc unit̂     σ rσ k ok aK a = tt
  redTmAcc (bool̂ b) σ rσ k ok aK a = tt
  redTmAcc (nat̂ j)  σ rσ k ok aK a = tt
  redTmAcc (uniq̂ j)  σ rσ k ok aK a = tt
  redTmAcc (pairᵗ x y) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y))))
    , redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x))))
  redTmAcc nilᵗ σ rσ k ok aK a = []
  redTmAcc (consᵗ x xs) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs))))
    ∷ redTmAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x))))
  redTmAcc (foldᵗ l z f) σ rσ k ok aK (acc rs) =
    redFoldVals f σ
      (λ rx ra →
        redTmAcc f (_ ∷ _ ∷ σ) (rx , ra , rσ) k
          (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
            (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
          (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                            (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
      (redTmAcc l σ rσ k
        (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))))
      (redTmAcc z σ rσ k
        (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
          (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
        (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                          (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
  redTmAcc (fstᵗ q) σ rσ k ok aK (acc rs) =
    proj₁ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (sndᵗ q) σ rσ k ok aK (acc rs) =
    proj₂ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (inlᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (inrᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (caseᵗ sc l r) σ rσ k ok aK (acc rs)
    with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
       | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
  ... | oksc | rest
    with evalWith sc σ
       | redTmAcc sc σ rσ k oksc aK
           (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r))))
  ... | inj₁ x | q =
    redTmAcc l (x ∷ σ) (q , rσ) k
      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  ... | inj₂ y | q =
    redTmAcc r (y ∷ σ) (q , rσ) k
      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  redTmAcc (ifᵗ c x y) σ rσ k ok aK (acc rs)
    with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
  ... | rest with evalWith c σ
  ... | true  =
    redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  ... | false =
    redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  redTmAcc (primᵗ add x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ sub x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ mul x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ ltᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵘ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ notᵖ x) σ rσ k ok aK a = tt
  redTmAcc (strmᵗ e) []       rσ k ok aK (acc rs) =
    subst (Red (obs _)) (subΘ-id-exp e) (redExpAcc e [] tt k ok aK (rs ≤-refl))
  redTmAcc (strmᵗ e) (v ∷ vs) rσ k ok aK (acc rs) =
    redExpAcc e (v ∷ vs) rσ k ok aK (rs ≤-refl)

  redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u} (ts : List (Tm Γ [] [] Θ u))
              (σ : All (Val Γ) Θ) → RedEnv σ
            → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
            → Acc _<_ (gsizeᵗˢ ts)
            → All (Red u) (map (λ tm → evalTm tm) (subΘTms [] σ ts))
  redTmsAcc []       σ rσ k ok aK a = []
  redTmsAcc (x ∷ xs) σ rσ k ok aK (acc rs) =
      subst (Red _) (sym (sub-evalTm x σ))
        (redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
          (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs)))))
    ∷ redTmsAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x))))

  -- A FRAME'S FUNCTION, CLOSED AGAINST THE AMBIENT ENVIRONMENT AND
  -- THEN APPLIED, is the term face at one more entry.
  redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Fn Γ [] [] Θ s u)
             (σ : All (Val Γ) Θ) → RedEnv σ
           → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
           → Acc _<_ (gsizeᵗ f) → RedFn (subΘTm (s ∷ []) σ f)
  redFnAcc {s = s} f σ rσ k ok aK a {v} p =
    subst (Red _) (sym (sub-applyFn f σ v)) (redTmAcc f (v ∷ σ) (p , rσ) k ok aK a)

-- THE TOP LINE: every closed expression is reducible, which is the
-- face above at the empty environment, where closing is the identity.
reducible : ∀ {n} {Γ : Ctx n} {t} (b : Closed Γ t) → Red {Γ = Γ} (obs t) b
reducible b =
  subst (Red (obs _)) (subΘ-id-exp b)
    (redExpAcc b [] tt _ (ib-topᵉ b) (<-wellFounded _) (<-wellFounded (gsizeᵉ b)))
