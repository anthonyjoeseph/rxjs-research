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
-- candidate it just computed, so the next fold through it certifies
-- the cell against a column for what the store holds now.  The arm
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
-- RECOVERY: git show 3abdafa1:agda/src/Rx/Exp/ValEq.agda holds the
--   decidable value equality the certification compares cells with.

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
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_) renaming (map to mapᵐ)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _∸_; s≤s; _+_; _<ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Tick; ObservableInput)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; Val; Exp; Tm; Env; []ᵉ;
  _∷ᵉ_; evalWith; foldVals; lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; isData; unfoldμ; varᵗ; unit̂;
  bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (sourceᵏ; freshId; setAt)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; root)
open import Rx.Evaluator.Unconn-Arith using (unconn)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-of; subs-empty; subs-mint; subs-defer; subs-floor; subs-μ; foldPath⇓;
  fold-root)

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

-- ONE CALL MADE TO A CONTINUATION, AS THE CALLER MADE IT.  The trace
-- a subscribe answers with is a list of these, oldest first, and a
-- fold applied to the fields in order is the call itself -- which is
-- what makes the replay compute the successor rather than approximate
-- it.  The room proof travels with the call because the fold demands
-- it and the replayer holds no other.
record Call {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u}
            (P : Val Γ u → Set₁) (S : Set) : Set₁ where
  constructor call
  field
    st₀   : S
    now   : Tick
    vals  : List (Val Γ u)
    cands : All (λ v → Maybe (P v)) vals
    fin   : Bool
    sched : Sched Γ
    st    : EvalSt e
    room  : Room m sched st

Trace : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u}
        (P : Val Γ u → Set₁) (S : Set) → Set₁
Trace {e = e} m P S = List (Call {e = e} m P S)

-- a column of certainties is a column of candidates
allJust : ∀ {A : Set} {P : A → Set₁} {xs : List A} → All P xs → All (λ x → Maybe (P x)) xs
allJust []       = []
allJust (p ∷ ps) = just p ∷ allJust ps

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
-- THE CANDIDATE COLUMN IS `Maybe`, AND `nothing` IS A VALUE THE
-- CONTINUATION CANNOT VOUCH FOR.  Every value arriving through a live
-- subscribe has a candidate; a value read back from a store cell whose
-- writer's successor never reached this closure has none, and a
-- `nothing` arriving where a candidate is NEEDED -- a flattener about
-- to subscribe it -- is what the replay exists to make unreachable.
record RP {n} {Γ : Ctx n} {t} {e : Closed Γ t} (m : ℕ) {u lo}
          (P : Val Γ u → Set₁) (S : Set) (κ : Path Γ lo u t) : Set₁ where
  coinductive
  field
    fold : S → (now : Tick) (vals : List (Val Γ u)) → All (λ v → Maybe (P v)) vals
         → (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
         → Σ (Stream Γ t × Sched Γ × EvalSt e)
             (λ r → foldPath⇓ {e = e} now κ vals fin sched st r)
           × S × RP {e = e} m P S κ
open RP public

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the
-- statement the whole argument turns on -- given any continuation
-- above and any state under the ceiling, a subscription derivation
-- exists whose answer is at the root, and the continuation's state
-- comes back.
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
-- lower one is DROPPED to it (`dropRP`), its candidates forgotten.
-- Weakening only ever runs from the higher ceiling to the lower, which
-- is the direction it is sound in.
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
  ∀ {S : Set} {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t)
  → RP {e = e} m (Red m u) S κ → S
  → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → Room m sched st
  → Σ (Stream Γ t × Sched Γ × EvalSt e)
      (λ r → subscribeE⇓ {e = e} b κ now sched st r)
    × S × RP {e = e} m (Red m u) S κ × Trace {e = e} m (Red m u) S

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
-- THE FRAME CONTINUATION THAT REACHES NO CYCLE.
------------------------------------------------------------------

-- THE ROOT MINTS THE BURST FROM NOTHING, and its state is the unit.
rootRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m lo} {P : Val Γ t → Set₁}
       → RP {e = e} m {lo = lo} P ⊤ root
fold rootRP tt now vals _ fin sched st rm = (_ , fold-root) , tt , rootRP

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

-- THE MAP ARM.  Stateless; its translation maps the values and their
-- candidates through the closure, exactly as its frame's fold does.
postulate
  red-map : ∀ {n} {Γ : Ctx n} {Θ s t} (f : Tm Γ [] [] (s ∷ Θ) t)
              (b : Exp Γ [] [] Θ s) → Arm (mapᵉ f b)

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
    → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
    → ∀ {m} → RP {e = e} m (Red m (lookup Γ i)) S κ → S
    → (now : Tick) (sched : Sched Γ)
    → (sc : ObservableInput (Val Γ (lookup Γ i))) {oks : T (isData (lookup Γ i))}
    → Sched.slots sched i ≡ scripted {ok = oks} sc
    → ∀ (st : EvalSt e) → Acc _<_ m → Room m sched st
    → Σ (Stream Γ t × Sched Γ × EvalSt e)
        (λ r → subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r)
      × S × RP {e = e} m (Red m (lookup Γ i)) S κ × Trace {e = e} m (Red m (lookup Γ i)) S

-- THE SHARED SLOT, AND THE ONE EDGE OF THE CYCLE THAT SPENDS THE ROOM.
-- A share's definition is an arbitrary expression standing in no
-- relation to `input i`, so it cannot be reached by any descent on the
-- TERM; the telescope's side condition charges it against the input
-- ceiling `toℕ i` instead.  It is subscribed at the sink, with the RAW
-- continuation above it: the def's values fan out over the registry,
-- through paths no subscribe built, at the ceiling the connect just
-- lowered to.  The trigger's own continuation is not used at all; the
-- trigger receives its values through the chain it registered, so the
-- continuation's state comes back untouched and its trace is empty.
postulate
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ S}
      (i : Fin n) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (ρ : Env Γ Θ)
      (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
    → ∀ {m} → RP {e = e} m (Red m (lookup Γ i)) S κ → S
    → (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → ∀ (st : EvalSt e) → Acc _<_ m → Room m sched st
    → Σ (Stream Γ t × Sched Γ × EvalSt e)
        (λ r → subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r)
      × S × RP {e = e} m (Red m (lookup Γ i)) S κ × Trace {e = e} m (Red m (lookup Γ i)) S

-- THE RAW CONTINUATION FOR A PATH THE STORE HOLDS.  An arrival and a
-- share's fan-out fold down registry paths no subscribe built, so the
-- frames' held candidates are rebuilt by `red-val` on what the store
-- holds, funded by the room the connect peeled and by the floor: a
-- chain registered on a share sinks STRICTLY above that share.
postulate
  rawRP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m u lo ℓ}
          (ac : Acc _<_ (n ∸ lo)) (le : lo ≤ ℓ) → Acc _<_ m
        → (κ : Path Γ ℓ u t) → RP {e = e} m (Red m u) ⊤ κ

------------------------------------------------------------------
-- THE BODIES.
------------------------------------------------------------------

redExpAcc (input i) ρ rρ k ok aK a aM = red-input i ρ k ok aK aM
redExpAcc (ofᵉ ts) ρ rρ k ok aK (acc rs) aM κ rp s now sched st rm
  with fold rp s now (map (λ tm → evalWith tm ρ) ts)
         (allJust (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl) aM)) true sched st rm
... | ((r , f) , s′ , rp′) =
      (r , subs-of f) , s′ , rp′
    , call s now (map (λ tm → evalWith tm ρ) ts)
        (allJust (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl) aM)) true sched st rm ∷ []
redExpAcc emptyᵉ ρ rρ k ok aK a aM κ rp s now sched st rm
  with fold rp s now [] [] true sched st rm
... | ((r , f) , s′ , rp′) = (r , subs-empty f) , s′ , rp′ , call s now [] [] true sched st rm ∷ []
redExpAcc (mapᵉ f b)        ρ rρ k ok aK a aM = red-map f b ρ rρ k ok aK a aM
redExpAcc (takeᵉ c b)       ρ rρ k ok aK a aM = red-take c b ρ rρ k ok aK a aM
redExpAcc (batchSyncᵉ b)    ρ rρ k ok aK a aM = red-batchSync b ρ rρ k ok aK a aM
redExpAcc (scanᵉ f z b)     ρ rρ k ok aK a aM = red-scan f z b ρ rρ k ok aK a aM
redExpAcc (mergeAllᵉ lim b) ρ rρ k ok aK a aM = red-mergeAll lim b ρ rρ k ok aK a aM
redExpAcc (switchAllᵉ b)    ρ rρ k ok aK a aM = red-switchAll b ρ rρ k ok aK a aM
redExpAcc (exhaustAllᵉ b)   ρ rρ k ok aK a aM = red-exhaustAll b ρ rρ k ok aK a aM
redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm
  with redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
         (rs (subst (_< suc (gsizeᵉ body))
                    (sym (gsize-unfoldμ body)) ≤-refl)) aM
         κ rp s₀ now sched st rm
... | ((r , d) , s₁ , rp₁ , tr) = (r , subs-μ d) , s₁ , rp₁ , tr
redExpAcc (varᵉ ()) ρ rρ k ok aK a aM
redExpAcc (deferᵉ body) ρ rρ k ok aK a aM κ rp s₀ now sched st rm =
  (_ , subs-defer refl refl refl refl) , s₀ , rp , []
redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) aM κ rp s₀ now sched st rm
  with (let src = freshId sourceᵏ (Sched.mint sched)
        in redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) aM κ rp s₀ now
             (record sched
                { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
             st rm)
... | ((r , d) , s₁ , rp₁ , tr) = (r , subs-mint refl d) , s₁ , rp₁ , tr

red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    with toℕ i <? lo
... | no  ¬below with fold rp s now [] [] true sched st rm
... | ((r , f) , s′ , rp′) =
      (r , subs-floor (≮⇒≥ ¬below) f) , s′ , rp′ , call s now [] [] true sched st rm ∷ []
red-input {Γ = Γ} i ρ k ok (acc rsK) aM {lo = lo} κ rp s now sched st rm
    | yes below with Sched.slots sched i in slEq
...   | scripted {ok = oks} sc = red-scripted i ρ k ok (acc rsK) κ below rp s now sched sc {oks = oks} slEq st aM rm
...   | shared d {ok = okd} =
        red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok)) ρ
          κ below rp s now sched slEq st aM rm

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
