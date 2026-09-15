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

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Id; Tick; InstEmit; InstEvent; init; value; close; handoff;
  complete; hot; cold)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Ctx; Closed; Val; Tm; Fn; evalTm; evalWith; applyFn; input; ofᵉ; emptyᵉ;
  mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; isData; unfoldμ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsize-unfoldμ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; _↠_; map-f; take-f; scan-f; take-st; scan-st;
  thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st;
  installNode; oneShotBurst; memberSource; splitEvents; retagEvents; NodeId; AllOp; from-inner)
open import Rx.Evaluator.Domain using (subscribeE⇓; pushBurst⇓; stepFrame⇓; step-map; push-nil; push-cons; subs-of;
  subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan; subs-defer;
  subs-floor; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async;
  subs-μ; sub-all; subs-merge-all; subs-switch-all; subs-exhaust-all)

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
Red (s ×ᵗ t) (a , b)  = Red s a × Red t b
Red (s +ᵗ t) (inj₁ a) = Red s a
Red (s +ᵗ t) (inj₂ b) = Red t b
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
--
-- RECOVERY: git show 64c568e2:agda/src/Rx/Evaluator/Reducible.agda restores
--   `StreamSat-spent` and `StreamSat-plumb`, the two arms of that
--   argument discharged — the first at the spent slot's fixed burst,
--   the second across the plumbing retag.  They are three lines each
--   and belong in the body that replaces the leaf below, which is the
--   consumer they were written ahead of.

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

postulate
  -- THE FUNDAMENTAL THEOREM ONE LEVEL DOWN, AT TERMS.  `Tm` and `Exp`
  -- are one mutual datatype and `strmᵗ` embeds an expression into a
  -- term, so this and the body below are mutually structural; it is
  -- stated separately because the arm that spends it is the only one
  -- that needs a value rather than a subscription.
  --
  -- REFUTED: `Refuted.Red-Env-Too-Strong` -- not as false, but as too
  --   strong to be a leaf.  Reflection sends every runtime value into
  --   a CLOSED term, whose environment hypothesis is trivial, so this
  --   hands back the candidate at every value of every type and the
  --   body's whole induction is redundant given it.  The leak is one
  --   constructor: the term language embeds an arbitrary expression at
  --   observable type, so "closed term" buys no smallness.  Twelve of
  --   the thirteen term formers are structural and close under the
  --   candidate's own data arms; the embedding is the whole content.
  --   So the repair is NOT to split a smaller leaf off the embedding
  --   arm -- at the empty environment that arm IS the top-line
  --   subscription result, so any leaf carrying it is this statement
  --   again.  It has to stop being a leaf: the fundamental theorem at
  --   terms is a MUTUAL PARTNER of the expression recursion, which is
  --   what pulling it out as a postulate disguised.  And the partner
  --   cannot be funded by a SIZE: the guarded size does not look
  --   inside a term at all -- a transformer's clause is one `suc` over
  --   its SOURCE and the frame's function contributes nothing -- so an
  --   expression embedded in that function is unbounded against the
  --   expression containing it, which is the shape that refuted the
  --   rank this candidate replaced.  What funds it is the TYPE: a
  --   function feeding a flattener produces at the element type, and
  --   the candidate at the enclosing observable already mentions the
  --   candidate there.  So the partner is stated at the type the
  --   recursion is already spending, not at a measure.
  --
  -- PROBED: `Probed.Reducible-Arms` at an observable-typed term, where
  --   the claim IS an expression's own reducibility and the body
  --   delivers it; at the same claim under a ONE-ENTRY environment,
  --   where the variable is read back out and the entry's candidate
  --   has to be what the conclusion gets; and at a numeral, which is
  --   DEGENERATE and is there to say the data half asserts nothing.
  --   No term that BINDS is reached, and no environment past one entry.
  red-env : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
              {env : All (Val Γ) Θ} → RedEnv env → Red u (evalWith tm env)

  -- THE SIXTH SLOT SUB-ARM, WHICH IS THE ONE THE OTHER FIVE ARE NOT.
  -- A share's definition is an arbitrary term standing in no relation
  -- to `input i`, so the body below cannot reach its candidate by any
  -- descent this module can see -- it is the connect edge, and it is
  -- answered by the quantification over state rather than by a
  -- measure.  The other five sub-arms are now a body: what they emit
  -- is protocol, and what values they carry are DATA by the slot's own
  -- side condition, so `red-data` closes their satisfaction outright.
  --
  -- DEAD ROUTE: it cannot be a leaf taking the body's own induction
  --   hypothesis at the definition, which is the shape every other leaf
  --   here has.  The definition is drawn from the slot table rather
  --   than from the term, so passing `reducible d` would make this
  --   mutual with a call Agda reads as non-structural, and the block
  --   would need a measure back.
  --
  -- PROBED: `Probed.Reducible-Arms` at both sub-arms that carry no
  --   payload -- a share whose source has completed, and one whose
  --   definition is already connected so this subscription only joins
  --   the fan-out.  Neither runs the definition, so the CONNECT is not
  --   reached and neither is anything the definition emits.  Both
  --   states are CONSTRUCTED rather than reached by a run, which is
  --   what the rows are bounded by: they say the arms compose at a
  --   state of that description.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
      (i : Fin n) (d : Closed Γ (lookup Γ i)) {ok}
      (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (id : Id) (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = ok}
    → (st : EvalSt e)
    → Σ (Stream Γ (lookup Γ i) × Sched Γ × EvalSt e) λ r →
        subscribeE⇓ {e = e} (input i) κ id now sched st r
          × StreamSat (Red (lookup Γ i)) (proj₁ r)

  -- A SCAN READS ITS ACCUMULATOR BACK OUT OF A NODE, AND EMITS IT.
  -- That makes this the first statement here whose conclusion is about
  -- a value the candidate never saw threaded: the accumulator was
  -- installed by an earlier step and is folded with the arriving
  -- batch, so what leaves the frame is a function of stored state.
  -- `Red` quantifies over every state with no precondition, which is
  -- what makes its recursive calls free and is exactly what leaves
  -- this conclusion with nothing under it.
  --
  -- DEAD ROUTE: the fact this needs is `Red` of the stored value, and
  --   it is establishable at the install (`red-env` at the empty
  --   environment on the seed) and preserved at the writeback
  --   (`red-env` at two entries, the old accumulator and the arriving
  --   value, which the push already carries).  What has no home is the
  --   CARRIER between them, and three candidates are structurally
  --   blocked -- by ONE obstruction wearing three faces, which is
  --   worth saying because the first face reads as a module-order
  --   accident and is not one.  A FIELD on the state record closes a
  --   definitional cycle rather than an import cycle: the candidate's
  --   observable arm is indexed by the subscription relation, which is
  --   itself indexed by the state record, so a field of that record
  --   naming the candidate is circular however the modules are cut.  A
  --   PRECONDITION on the candidate's own observable arm is the same
  --   cycle stated directly, and it does not decrease: the arm
  --   recurses on the element type, while a predicate over a store
  --   reaches the candidate at whatever type a node happens to hold,
  --   which is unrelated to it.  And a
  --   HYPOTHESIS on this statement is laundering, since the
  --   unconditional form is not refuted -- every closed expression is
  --   reducible once the theorem lands, so there is no adversarial
  --   store to point at.  Parameterising the state record over an
  --   abstract node predicate is that same cycle DEFERRED: the
  --   instantiation ties the knot, and the executable face pays a
  --   threaded parameter it only ever meets at the trivial predicate.
  --   And the fourth candidate, a SYNTACTIC invariant saying a stored
  --   value is the denotation of a closed term, is VACUOUS: reflection
  --   is total, so every value is one and the pairing carries no
  --   information.  That vacuity is not a detail about this statement
  --   -- it is the environment leaf being too strong, refuted below,
  --   and until that leaf is restated no carrier decision here means
  --   anything, since the leaf already hands back what a carrier would
  --   deliver.
  --
  -- REFUTED: `Refuted.Red-Env-Too-Strong`
  --
  -- PROBED: `Probed.Reducible-Arms` at an accumulator of OBSERVABLE
  --   type folded by a projection, so the value that leaves the frame
  --   IS the one the node was holding and the row fails unless the
  --   candidate holds of it.  The row can only be written by
  --   INSTALLING a reducible accumulator, and that is the finding
  --   rather than the coverage: nothing in the statement, in `Red` or
  --   in `EvalSt` says an installed one ever is.  Not reached: an
  --   accumulator a run itself produced, and the empty-batch arm.
  red-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
             (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
             (κ : Path Γ lo u t)
             {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e)
           → RedStep {e = e} id now (scan-f fn nid) κ vals fin sched st

  -- A TAKE'S COUNTDOWN AND A SCAN'S ACCUMULATOR ARE THE SAME GAP.
  -- Both dispatch on a node this face installed and has not looked at
  -- since, so both are the first place the candidate must be read back
  -- OUT of stored state rather than threaded through it.  They are
  -- separate statements because the take also truncates, and a
  -- truncation is where a burst can lose the very value a satisfaction
  -- claim was taken at.
  --
  -- PROBED: `Probed.Reducible-Arms` at an observable payload with the
  --   budget unexhausted, where the values pass through untouched and
  --   the store decides only HOW MANY -- so this arm is store-reading
  --   without being store-DEPENDENT, which is the contrast that pins
  --   what the scan above is actually missing.  The CUT is not
  --   reached, and neither is a stuck node lookup.
  red-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
             (id : Id) (now : Tick) (nid : NodeId) (κ : Path Γ lo s t)
             {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e)
           → RedStep {e = e} id now (take-f nid) κ vals fin sched st

  -- WHAT AN INNER EMITS ON ITS WAY BACK UP, which is the other half of
  -- a flattener and the half no row has reached.  The walk below
  -- SUBSCRIBES an inner; this is what happens when that inner later
  -- fires, and it is where a mergeAll drains its queue and a switch
  -- decides whether the emission still belongs to anybody.
  --
  -- PROBED: `Probed.Reducible-Arms` at the arm that CARRIES rather
  --   than spends -- an unfinished inner emit, whose values pass
  --   through untouched, so an observable payload's candidate has to
  --   arrive at the conclusion.  That arm reads no store at all.  The
  --   drain and the kill, which are where this statement reads the
  --   `*All` node, are not reached.
  red-from-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
             (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
             (κ : Path Γ lo s t)
             {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e)
           → RedStep {e = e} id now (from-inner op allNid inst) κ vals fin sched st

  -- THE FLATTENING WALK, and the one leaf here with rows against it.
  --
  -- PROBED: `Probed.Reducible-Arms` at each of the three operators,
  --   with the arriving batch carrying a real observable: mergeAll
  --   subscribing it, mergeAll REFUSING it at a zero concurrency limit
  --   and queueing instead, switch killing and subscribing, exhaust
  --   subscribing with nothing active.  The inner's own subscription
  --   derivation is what comes back, so the candidate is SPENT at
  --   these rows rather than carried.  Not reached: a node already
  --   holding something -- a queue with an entry, a switch whose
  --   current inner is running, an exhaust already active -- and no
  --   batch of more than one value.
  red-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
             (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
             (κ : Path Γ lo u t)
             {vals : List (Val Γ (obs u))} → All (Red (obs u)) vals → (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e)
           → RedStep {e = e} id now (thru-outer op nid) κ vals fin sched st


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
red-data boolᵗ    _  _       = tt
red-data (s ×ᵗ t) ok (a , b) =
  let (o₁ , o₂) = T-if (isData s) (isData t) ok
  in red-data s o₁ a , red-data t o₂ b
red-data (s +ᵗ t) ok (inj₁ a) = red-data s (proj₁ (T-if (isData s) (isData t) ok)) a
red-data (s +ᵗ t) ok (inj₂ b) = red-data t (proj₂ (T-if (isData s) (isData t) ok)) b
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

-- THE SLOT ARM, WHICH IS FIVE SUB-ARMS OF PROTOCOL AND ONE LEAF.  It
-- mirrors the builder's own case split on the slot exactly, because
-- the derivation it must produce is the one the builder produces; what
-- is new is the satisfaction beside it, and at a scripted slot that is
-- `red-data` at every value the script carries.
red-input : ∀ {n} {Γ : Ctx n} (i : Fin n)
          → Red {Γ = Γ} (obs (lookup Γ i)) (input i)
red-input {Γ = Γ} i {lo = lo} κ id now sched st with toℕ i <? lo
... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below) , (tt ∷ tt ∷ tt ∷ []) ∷ []
... | yes below  with Sched.slots sched i in slEq
...   | scripted {ok = ok} (hot async)
        with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
...     | true  = _ , subs-hot-done below slEq doneEq , (tt ∷ tt ∷ tt ∷ []) ∷ []
...     | false = _ , subs-hot-live below slEq doneEq , (tt ∷ []) ∷ []
red-input {Γ = Γ} i {lo = lo} κ id now sched st
    | yes below | scripted {ok = ok} (cold sync []) =
      _ , subs-cold-sync below slEq refl
        , satOneShot id sched (redDatas _ ok sync)
red-input {Γ = Γ} i {lo = lo} κ id now sched st
    | yes below | scripted {ok = ok} (cold sync (d ∷ ds)) =
      _ , subs-cold-async below slEq refl refl
        , (tt ∷ satValues (redDatas _ ok sync)) ∷ []
red-input {Γ = Γ} i {lo = lo} κ id now sched st
    | yes below | shared d {ok = ok} =
      red-input-shared i d κ below id now sched slEq st

-- THE FUNDAMENTAL THEOREM AT CLOSED TERMS is the leaf above at the
-- empty environment, which is the whole of the difference.
red-tm : ∀ {n} {Γ : Ctx n} {u} (tm : Tm Γ [] [] [] u) → Red u (evalTm tm)
red-tm tm = red-env tm tt

redTms : ∀ {n} {Γ : Ctx n} {u} (ts : List (Tm Γ [] [] [] u))
       → All (Red u) (map (λ tm → evalTm tm) ts)
redTms []       = []
redTms (x ∷ xs) = red-tm x ∷ redTms xs

-- A MAPPING FRAME APPLIES ITS FUNCTION TO EVERY ARRIVING VALUE, so
-- what it produces is reducible exactly when the function is a term
-- under a one-entry reducible environment.
-- a frame's function binds exactly one entry, so this is the only
-- environment shape the body below ever builds.
redEnv1 : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → Red t v → RedEnv (v ∷ [])
redEnv1 t v r = r , tt

redMapVals : ∀ {n} {Γ : Ctx n} {s u} (fn : Fn Γ [] [] [] s u)
             {vals : List (Val Γ s)} → All (Red s) vals
           → All (Red u) (map (applyFn fn) vals)
redMapVals fn []       = []
redMapVals {Γ = Γ} {s = s} fn {v ∷ vs} (p ∷ ps) =
  red-env fn (redEnv1 {Γ = Γ} s v p) ∷ redMapVals fn ps

-- STEPPING ONE FRAME, DISPATCHED ON THE FRAME.  The mapping arm is a
-- body because nothing about it is stateful; the other four each read
-- a node this face installed earlier, which is the one thing the
-- candidate's quantification over every state does not hand back.
red-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ lo u t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e)
         → RedStep {e = e} id now f κ vals fin sched st
red-step id now (map-f fn) κ rv fin sched st =
  _ , step-map , redMapVals fn rv
red-step id now (scan-f fn nid) κ rv fin sched st =
  red-scan id now fn nid κ rv fin sched st
red-step id now (take-f nid) κ rv fin sched st =
  red-take id now nid κ rv fin sched st
red-step id now (from-inner op allNid inst) κ rv fin sched st =
  red-from-inner id now op allNid inst κ rv fin sched st
red-step id now (thru-outer op nid) κ rv fin sched st =
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
           (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ lo u t)
           {burst : Stream Γ s} → StreamSat (Red s) burst
         → (sched : Sched Γ) (st : EvalSt e)
         → RedPush {e = e} id now f κ burst sched st
red-push id now f κ {[]}      []       sched st = _ , push-nil , []
red-push id now f κ {em ∷ ems} (p ∷ ps) sched st =
  let ((vals′ , evs , fin′ , sched₁ , st₁) , d , rv) =
        red-step id now f κ (splitVals (InstEmit.events em) p)
          (proj₂ (proj₂ (splitEvents (InstEmit.events em)))) sched st
      ((rest , sched₂ , st₂) , dr , sr) = red-push id now f κ ps sched₁ st₁
  in _ , push-cons refl d dr
       , ++⁺ (splitProt (InstEmit.events em))
             (++⁺ (satRetag evs) (satEvents rv (satFin fin′))) ∷ sr

-- THE BODY, AND WHAT PAYS FOR IT.  Its recursion is structural in the
-- TERM at every arm that has one, and every recursive call is made at
-- a schedule and a state the caller has already moved — a fresh node
-- installed, a counter bumped, a path extended.  That those calls are
-- free is exactly what the candidate's quantification over every state
-- buys.
--
-- THE ONE ARM WITH NO SUBTERM IS THE μ, AND THE SYNTAX PAYS FOR IT.
-- An unfolding is no subterm of its fixpoint and sits at the same
-- type, so neither the term nor the candidate's own type recursion
-- reaches it.  What does is `gsizeᵉ`: the μ former spends a unit, the
-- gate the μ variable must sit behind is where the size stops looking,
-- and the unfolding therefore has exactly the size the body had.  So
-- the recursion is on the ACCESSIBILITY of that size rather than on
-- the term, and every other arm keeps its structural decrease because
-- the size counts the formers it descends through.
reducibleAcc : ∀ {n} {Γ : Ctx n} {t} (b : Closed Γ t)
             → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} (obs t) b
reducibleAcc (input i) a κ id now sched st = red-input i κ id now sched st
reducibleAcc (ofᵉ ts) a κ id now sched st =
  _ , subs-of refl , satOneShot id sched (redTms ts)
reducibleAcc emptyᵉ a κ id now sched st = _ , subs-empty refl , satOneShot id sched []
reducibleAcc (mapᵉ f b) (acc rs) κ id now sched st =
  let ((burst , sched₁ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (map-f f ↠ κ) id now sched st
      (r , p , sat′) = red-push id now (map-f f) κ sat sched₁ st₁
  in r , subs-map d p , sat′
reducibleAcc (takeᵉ c b) (acc rs) κ id now sched st with evalTm c in ceq
... | zero  = _ , subs-take-zero ceq refl , satOneShot id sched []
... | suc k =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (take-f nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (take-st (suc k)) st)
      (r , p , sat′) = red-push id now (take-f nid) κ sat sched₂ st₁
  in r , subs-take-suc ceq refl d p , sat′
reducibleAcc (scanᵉ f z b) (acc rs) κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (scan-f f nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (scan-st (evalTm z)) st)
      (r , p , sat′) = red-push id now (scan-f f nid) κ sat sched₂ st₁
  in r , subs-scan refl d p , sat′
reducibleAcc (mergeAllᵉ lim b) (acc rs) κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (thru-outer mergeAllᵒ nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (mergeAll-st lim 0 [] false) st)
      (r , p , sat′) = red-push id now (thru-outer mergeAllᵒ nid) κ sat sched₂ st₁
  in r , subs-merge-all (sub-all refl d p) , sat′
reducibleAcc (switchAllᵉ b) (acc rs) κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (thru-outer switchᵒ nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (switch-st nothing false) st)
      (r , p , sat′) = red-push id now (thru-outer switchᵒ nid) κ sat sched₂ st₁
  in r , subs-switch-all (sub-all refl d p) , sat′
reducibleAcc (exhaustAllᵉ b) (acc rs) κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducibleAcc b (rs ≤-refl) (thru-outer exhaustᵒ nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (exhaust-st false false) st)
      (r , p , sat′) = red-push id now (thru-outer exhaustᵒ nid) κ sat sched₂ st₁
  in r , subs-exhaust-all (sub-all refl d p) , sat′
reducibleAcc (μᵉ body) (acc rs) κ id now sched st =
  let (r , d , sat) =
        reducibleAcc (unfoldμ body)
          (rs (subst (_< suc (gsizeᵉ body)) (sym (gsize-unfoldμ body)) ≤-refl))
          κ id now sched st
  in r , subs-μ d , sat
reducibleAcc (varᵉ ()) a
reducibleAcc (deferᵉ body) a κ id now sched st =
  _ , subs-defer refl refl refl , (tt ∷ []) ∷ []

reducible : ∀ {n} {Γ : Ctx n} {t} (b : Closed Γ t) → Red {Γ = Γ} (obs t) b
reducible b = reducibleAcc b (<-wellFounded (gsizeᵉ b))
